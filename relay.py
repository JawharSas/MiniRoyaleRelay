"""
Mini Royale relay - lets players on different networks find each other with a 5-letter room code.

Runs on a free web host (Render): standard library only, speaks WebSocket over HTTP(S).
Nothing about the game is understood here - it just pairs a joiner with the host of a room and
copies bytes between them. Game PCs only ever make OUTGOING connections to this server.

    python relay.py            (listens on $PORT, default 47780)

Protocol (first message on a new WebSocket is JSON text):
  {"t":"rhost","v":N}                  host opens a room        -> {"t":"code","c":"ABCDE"}  (socket stays open)
  {"t":"rjoin","c":"ABCDE","v":N}      a player joins a room    -> {"t":"ok"} then raw pipe, or {"t":"err","m":...}
  host gets {"t":"newc","id":K} for every joiner and answers with a NEW socket:
  {"t":"rattach","c":"ABCDE","id":K}   -> {"t":"ok"} then raw pipe to that joiner
After "ok" every binary frame is forwarded unchanged to the other side.
"""
import asyncio
import base64
import hashlib
import json
import os
import random
import struct
import time

PROTO = 1                       # relay protocol version (the game sends it as "v")
GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
ALPHA = "BCDFGHJKLMNPQRSTVWXZ"  # no vowels: no accidental words, no 0/O or 1/I mix-ups
MAX_FRAME = 8_000_000
MAX_ROOMS = 300
MAX_PLAYERS = 8                 # pipes per room (host's own game is not a pipe)
ROOM_BYTES = 600_000_000        # per room, keeps a runaway room from eating the free bandwidth
PAIR_WAIT = 12                  # seconds the host has to answer a joiner


def frame(op, data=b""):
    n = len(data)
    if n < 126:
        h = bytes([0x80 | op, n])
    elif n < 65536:
        h = bytes([0x80 | op, 126]) + struct.pack("!H", n)
    else:
        h = bytes([0x80 | op, 127]) + struct.pack("!Q", n)
    return h + data


def unmask(data, mask):
    n = len(data)
    if not n:
        return data
    pad = (mask * (n // 4 + 1))[:n]
    return (int.from_bytes(data, "big") ^ int.from_bytes(pad, "big")).to_bytes(n, "big")


class Peer:
    """One WebSocket connection."""

    def __init__(s, reader, writer):
        s.r, s.w, s.closed = reader, writer, False

    async def read_frame(s):
        msg, op0 = b"", 0
        while True:
            b1, b2 = await s.r.readexactly(2)
            op, n = b1 & 0x0F, b2 & 0x7F
            if n == 126:
                n = struct.unpack("!H", await s.r.readexactly(2))[0]
            elif n == 127:
                n = struct.unpack("!Q", await s.r.readexactly(8))[0]
            if n > MAX_FRAME:
                raise ValueError("frame too big")
            mask = await s.r.readexactly(4) if b2 & 0x80 else None
            data = await s.r.readexactly(n)
            if mask:
                data = unmask(data, mask)
            if op >= 8:
                return op, data
            if op:
                op0 = op
            msg += data
            if b1 & 0x80:
                return op0, msg

    async def recv(s):
        """Next data message (ping/pong handled here). Raises when the socket is gone."""
        while True:
            op, data = await s.read_frame()
            if op == 8:
                raise EOFError
            if op == 9:
                await s.send(10, data)
            elif op in (1, 2):
                return op, data

    async def send(s, op, data=b""):
        if s.closed or s.w.is_closing():
            raise EOFError
        s.w.write(frame(op, data))
        await s.w.drain()

    async def send_json(s, obj):
        await s.send(1, json.dumps(obj, separators=(",", ":")).encode())

    async def close(s):
        if s.closed:
            return
        s.closed = True
        try:
            s.w.write(frame(8))
            s.w.close()
        except Exception:
            pass


class Join:
    def __init__(s, peer):
        s.peer, s.mate, s.ev, s.done = peer, None, asyncio.Event(), False


class Room:
    def __init__(s, host):
        s.host, s.joins, s.nid, s.bytes, s.t0 = host, {}, 0, 0, time.time()

    def live(s):
        return sum(1 for j in s.joins.values() if not j.done)


rooms = {}


def new_code():
    for _ in range(100):
        c = "".join(random.choice(ALPHA) for _ in range(5))
        if c not in rooms:
            return c
    raise RuntimeError("no free room code")


async def pipe(src, dst, room, j):
    """Copy messages src -> dst until either side goes away."""
    try:
        while True:
            _op, data = await src.recv()
            room.bytes += len(data)
            if room.bytes > ROOM_BYTES:
                break
            await dst.send(2, data)
    except Exception:
        pass
    j.done = True
    await src.close()
    await dst.close()


async def do_host(peer):
    code = new_code()
    room = rooms[code] = Room(peer)
    try:
        await peer.send_json({"t": "code", "c": code})
        while True:
            await peer.recv()                      # keep-alive pings from the host; nothing else expected
    except Exception:
        pass
    finally:
        rooms.pop(code, None)
        for j in list(room.joins.values()):
            if j.mate is None:
                j.ev.set()
                j.done = True


async def do_join(peer, first):
    room = rooms.get(str(first.get("c", "")).upper())
    if room is None:
        await peer.send_json({"t": "err", "m": "No room with that code"})
        return
    if room.live() >= MAX_PLAYERS:
        await peer.send_json({"t": "err", "m": "That room is full"})
        return
    room.nid += 1
    jid = room.nid
    j = room.joins[jid] = Join(peer)
    try:
        await room.host.send_json({"t": "newc", "id": jid})
        try:
            await asyncio.wait_for(j.ev.wait(), PAIR_WAIT)
        except asyncio.TimeoutError:
            pass
        if j.mate is None:
            await peer.send_json({"t": "err", "m": "The host did not answer"})
            return
        await pipe(peer, j.mate, room, j)
    except Exception:
        pass
    finally:
        j.done = True
        room.joins.pop(jid, None)


async def do_attach(peer, first):
    room = rooms.get(str(first.get("c", "")).upper())
    j = room.joins.get(first.get("id")) if room else None
    if j is None or j.mate is not None or j.done:
        await peer.send_json({"t": "err", "m": "Joiner is gone"})
        return
    j.mate = peer
    await peer.send_json({"t": "ok"})
    await j.peer.send_json({"t": "ok"})
    j.ev.set()
    await pipe(peer, j.peer, room, j)


async def handle(reader, writer):
    peer = Peer(reader, writer)
    try:
        head = await asyncio.wait_for(reader.readuntil(b"\r\n\r\n"), 10)
        lines = head.decode("latin1").split("\r\n")
        hdr = {}
        for ln in lines[1:]:
            if ":" in ln:
                k, v = ln.split(":", 1)
                hdr[k.strip().lower()] = v.strip()
        if hdr.get("upgrade", "").lower() != "websocket" or "sec-websocket-key" not in hdr:
            body = ("Mini Royale relay: ok, %d rooms\n" % len(rooms)).encode()      # health check / wake-up ping
            writer.write(b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\nConnection: close\r\nContent-Length: %d\r\n\r\n" % len(body) + body)
            await writer.drain()
            return
        acc = base64.b64encode(hashlib.sha1((hdr["sec-websocket-key"] + GUID).encode()).digest()).decode()
        writer.write(("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                      "Sec-WebSocket-Accept: %s\r\n\r\n" % acc).encode())
        await writer.drain()
        _op, data = await asyncio.wait_for(peer.recv(), 15)
        first = json.loads(data)
        t = first.get("t")
        if t in ("rhost", "rjoin") and first.get("v") != PROTO:
            await peer.send_json({"t": "err", "m": "Your game is out of date - get the newest version"})
        elif t == "rhost":
            if len(rooms) >= MAX_ROOMS:
                await peer.send_json({"t": "err", "m": "The server is busy, try again in a minute"})
            else:
                await do_host(peer)
        elif t == "rjoin":
            await do_join(peer, first)
        elif t == "rattach":
            await do_attach(peer, first)
    except Exception:
        pass
    finally:
        await peer.close()
        try:
            writer.close()
        except Exception:
            pass


async def main():
    port = int(os.environ.get("PORT", "47780"))
    srv = await asyncio.start_server(handle, "0.0.0.0", port)
    print("relay listening on", port, flush=True)
    async with srv:
        await srv.serve_forever()


if __name__ == "__main__":
    asyncio.run(main())
