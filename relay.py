"""
Mini Royale relay - lets players on different networks find each other with a 5-letter room code.

Runs on a free web host (Render): standard library only, speaks WebSocket over HTTP(S).
It pairs a joiner with the host of a room and copies bytes between them, keeps the player
accounts, and serves the private admin page. Game PCs only ever make OUTGOING connections here.

    python relay.py            (listens on $PORT, default 47780)

Protocol (first message on a new WebSocket is JSON text):
  {"t":"reg","u":name,"p":password,"v":N}     create an account   -> {"t":"auth","u":name,"tok":token} or {"t":"err","m":...}
  {"t":"login","u":name,"p":password,"v":N}   log in              -> the same
  {"t":"rhost","v":N,"tok":T}                 host opens a room   -> {"t":"code","c":"ABCDE","u":name}  (socket stays open)
  {"t":"rjoin","c":"ABCDE","v":N,"tok":T}     a player joins      -> {"t":"ok"} then raw pipe, or {"t":"err","m":...}
  host gets {"t":"newc","id":K,"u":name} for every joiner and answers with a NEW socket:
  {"t":"rattach","c":"ABCDE","id":K}          -> {"t":"ok"} then raw pipe to that joiner
After "ok" every binary frame is forwarded unchanged to the other side.
An error with "auth":1 means the token is no longer good and the player has to log in again.

On its own socket the host also sends {"t":"info",...} (what the room is doing) and {"t":"res","r":[[name,win,kills],...]}
(match results for the account stats), and receives {"t":"adm","k":...} admin events started from the admin page.

Settings (environment variables on the web host, never in this file):
  ADMIN_PASSWORD            password of the admin page at /admin (10+ characters; the page is off without it)
  REDIS_URL                 Redis database that keeps the accounts (redis://user:password@host:port, e.g. Redis Cloud)
  UPSTASH_REDIS_REST_URL    } or instead: a free Upstash Redis database, reached over HTTPS
  UPSTASH_REDIS_REST_TOKEN  }
  Without a database the accounts live in memory only and are lost whenever the server restarts.
  DATA_KEY                  32+ random characters. With it, every account record is encrypted and sealed before it goes
                            to the database and the login tokens are signed with it, so somebody who gets into the
                            database can neither read nor forge anything. Never change or lose it: the accounts
                            become unreadable.
"""
import asyncio
import base64
import hashlib
import hmac
import json
import os
import random
import secrets
import socket
import ssl
import struct
import time
import urllib.parse
import urllib.request

PROTO = 2                       # relay protocol version (the game sends it as "v")
GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
ALPHA = "BCDFGHJKLMNPQRSTVWXZ"  # no vowels: no accidental words, no 0/O or 1/I mix-ups
MAX_FRAME = 8_000_000
MAX_ROOMS = 300
MAX_PLAYERS = 8                 # pipes per room (host's own game is not a pipe)
ROOM_BYTES = 600_000_000        # per room, keeps a runaway room from eating the free bandwidth
PAIR_WAIT = 12                  # seconds the host has to answer a joiner
MAX_ACCOUNTS = 3000
TOKEN_DAYS = 90                 # a saved login lasts this long
PW_ROUNDS = 300_000             # PBKDF2 rounds for the password hash (each account remembers its own number)
WEAK = {"password", "password1", "12345678", "123456789", "1234567890", "11111111", "00000000", "qwertyui", "qwerty123",
        "iloveyou", "abcdefgh", "abcd1234", "minecraft", "roblox123", "miniroyale", "letmein123", "football", "princess"}
RESERVED = {"you", "announcer", "gemma", "host", "player", "admin", "server"}    # same list as the game
EVENTS = {"say", "drops", "gift", "heal", "meteor", "smite", "xp", "storm"}      # admin events the game understands
ADMIN_PASSWORD = os.environ.get("ADMIN_PASSWORD", "")
DB_URL = os.environ.get("UPSTASH_REDIS_REST_URL", "").rstrip("/")
DB_TOKEN = os.environ.get("UPSTASH_REDIS_REST_TOKEN", "")
REDIS_URL = os.environ.get("REDIS_URL", "")
DATA_KEY = os.environ.get("DATA_KEY", "")       # 32+ characters: everything stored in the database is encrypted and sealed with it
T0 = time.time()
try:
    with open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "admin.html"), "rb") as _fh:
        ADMIN_PAGE = _fh.read()
except OSError:
    ADMIN_PAGE = b"admin.html is missing next to relay.py"


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
    def __init__(s, peer, user):
        s.peer, s.mate, s.ev, s.done, s.user = peer, None, asyncio.Event(), False, user


class Room:
    def __init__(s, host, user):
        s.host, s.joins, s.nid, s.bytes, s.t0 = host, {}, 0, 0, time.time()
        s.user, s.members, s.info, s.res_t = user, {user.lower()}, {}, 0.0

    def live(s):
        return sum(1 for j in s.joins.values() if not j.done)


rooms = {}


# ------------------------------ accounts ------------------------------
def resp_read(f):
    """One answer in the Redis wire format."""
    line = f.readline()
    if not line:
        raise OSError("database closed the connection")
    k, rest = line[:1], line[1:].strip()
    if k == b"+":
        return rest.decode()
    if k == b"-":
        raise OSError("database: " + rest.decode(errors="replace")[:60])
    if k == b":":
        return int(rest)
    if k == b"$":
        return f.read(int(rest) + 2)[:-2].decode() if int(rest) >= 0 else None
    if k == b"*":
        return [resp_read(f) for _ in range(int(rest))] if int(rest) >= 0 else None
    raise OSError("database sent something unexpected")


def redis_call(*cmd):
    """One command to a normal Redis server (REDIS_URL = redis://user:password@host:port, or rediss:// with TLS)."""
    u = urllib.parse.urlsplit(REDIS_URL)
    sk = socket.create_connection((u.hostname, u.port or 6379), timeout=8)
    try:
        if u.scheme == "rediss":
            sk = ssl.create_default_context().wrap_socket(sk, server_hostname=u.hostname)
        f = sk.makefile("rb")

        def send(*a):
            parts = [str(x).encode() for x in a]
            sk.sendall(b"*%d\r\n" % len(parts) + b"".join(b"$%d\r\n%s\r\n" % (len(p), p) for p in parts))
            return resp_read(f)
        if u.password:
            send("AUTH", *([urllib.parse.unquote(u.username)] if u.username else []), urllib.parse.unquote(u.password))
        return send(*cmd)
    finally:
        sk.close()


def db_call(*cmd):
    """One Redis command (blocking: always run it in a thread). REDIS_URL if set, else Upstash's HTTPS REST API."""
    if REDIS_URL:
        return redis_call(*cmd)
    req = urllib.request.Request(DB_URL, data=json.dumps(cmd).encode(),
                                 headers={"Authorization": "Bearer " + DB_TOKEN, "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=8) as r:
        return json.loads(r.read()).get("result")


def subkey(label):
    return hmac.new(DATA_KEY.encode(), label, hashlib.sha256).digest()


def seal(name, text):
    """Encrypt a record and seal it to its account name (encrypt-then-MAC: SHAKE-256 keystream, HMAC-SHA256 tag)."""
    nonce, raw = secrets.token_bytes(16), text.encode()
    ks = hashlib.shake_256(subkey(b"enc") + nonce).digest(len(raw))
    ct = (int.from_bytes(raw, "big") ^ int.from_bytes(ks, "big")).to_bytes(len(raw), "big")
    tag = hmac.new(subkey(b"mac"), name.encode() + b"|" + nonce + ct, hashlib.sha256).digest()
    return "v1:" + base64.b64encode(nonce + ct + tag).decode()


def unseal(name, blob):
    """The text of a sealed record; ValueError if it was changed, copied from another account or not made with our key."""
    if not blob.startswith("v1:"):
        raise ValueError("not sealed")
    raw = base64.b64decode(blob[3:])
    nonce, ct, tag = raw[:16], raw[16:-32], raw[-32:]
    if len(raw) < 49 or not hmac.compare_digest(tag, hmac.new(subkey(b"mac"), name.encode() + b"|" + nonce + ct, hashlib.sha256).digest()):
        raise ValueError("bad seal")
    ks = hashlib.shake_256(subkey(b"enc") + nonce).digest(len(ct))
    return (int.from_bytes(ct, "big") ^ int.from_bytes(ks, "big")).to_bytes(len(ct), "big").decode()


class Store:
    """Accounts by lower-case name. Kept in memory; every change is also written to the database when one is set up."""

    def __init__(s):
        s.acc, s.dirty, s.db = {}, set(), bool(REDIS_URL or (DB_URL.startswith("https://") and DB_TOKEN))
        s.enc, s.skipped = len(DATA_KEY) >= 32, 0
        s.loaded, s.secret = not s.db, subkey(b"tok").hex() if s.enc else secrets.token_hex(32)

    async def call(s, *cmd):
        return await asyncio.get_running_loop().run_in_executor(None, db_call, *cmd)

    async def run(s):
        while not s.loaded:                          # never write before the old data has been read
            try:
                if s.enc:
                    await s.call("DEL", "mr:secret")         # tokens are signed with DATA_KEY: nothing secret stays in the database
                else:
                    await s.call("SETNX", "mr:secret", s.secret)
                    s.secret = await s.call("GET", "mr:secret") or s.secret
                flat, acc = await s.call("HGETALL", "mr:acc") or [], {}
                for i in range(0, len(flat) - 1, 2):
                    try:
                        acc[flat[i]] = json.loads(unseal(flat[i], flat[i + 1]) if s.enc else flat[i + 1])
                    except ValueError:
                        s.skipped += 1                   # changed by somebody else, or not written with our key: not trusted
                s.acc, s.loaded = acc, True
                if s.skipped:
                    print("ignored", s.skipped, "database records that failed the seal check", flush=True)
            except Exception as e:
                print("database not reachable:", str(e)[:80], flush=True)
                await asyncio.sleep(5)
        while s.db:
            await asyncio.sleep(1)
            for k in list(s.dirty):
                s.dirty.discard(k)
                try:
                    if k in s.acc:
                        text = json.dumps(s.acc[k], separators=(",", ":"))
                        await s.call("HSET", "mr:acc", k, seal(k, text) if s.enc else text)
                    else:
                        await s.call("HDEL", "mr:acc", k)
                except Exception:
                    s.dirty.add(k)                   # try again on the next round
                    break

    def put(s, k):
        if s.db:
            s.dirty.add(k)


store = Store()
hits = {}                       # rate limits: key -> recent times
adminlog = []


def limited(key, n, per):
    """True when `key` already did this n times within `per` seconds."""
    now = time.time()
    if len(hits) > 5000:
        hits.clear()
    q = hits[key] = [t for t in hits.get(key, []) if now - t < per]
    if len(q) >= n:
        return True
    q.append(now)
    return False


def good_name(u):
    return (isinstance(u, str) and 3 <= len(u) <= 12 and u.isascii() and all(c.isalnum() or c == "_" for c in u)
            and u.lower() not in RESERVED)


def good_pw(p, u=""):
    """8-64 characters, not the username and not one of the passwords everybody tries first."""
    return (isinstance(p, str) and 8 <= len(p) <= 64 and p.isascii() and p.isprintable()
            and p.lower() != str(u).lower() and p.lower() not in WEAK)


PW_RULE = "Password: 8-64 characters, not your username, not an easy one"


def pw_hash(pw, salt, rounds):
    return hashlib.pbkdf2_hmac("sha256", pw.encode(), bytes.fromhex(salt), rounds).hex()


def sign(text):
    return hmac.new(store.secret.encode(), text.encode(), hashlib.sha256).hexdigest()[:40]


def make_token(a):
    exp = int(time.time()) + TOKEN_DAYS * 86400
    return "%s.%d.%s" % (a["n"], exp, sign("u|%s|%d|%s" % (a["n"].lower(), exp, a["tv"])))


def check_token(tok):
    """The account a token belongs to, or None (bad, expired, banned, password changed)."""
    try:
        name, exp, sig = str(tok).split(".")
        a = store.acc.get(name.lower())
        if a is None or a.get("ban") or int(exp) < time.time():
            return None
        return a if hmac.compare_digest(sig, sign("u|%s|%d|%s" % (name.lower(), int(exp), a["tv"]))) else None
    except (ValueError, KeyError):
        return None


async def do_auth(peer, first, ip):
    t, u, p = first.get("t"), first.get("u"), first.get("p")
    err = None
    if not store.loaded:
        err = "The server is still starting - try again in a few seconds"
    elif limited(("auth", ip), 10, 300) or limited("auth", 60, 60):
        err = "Too many tries - wait a few minutes"
    elif not good_name(u):
        err = "Username: 3-12 letters, numbers or _"
    elif t == "reg" and not good_pw(p, u):
        err = PW_RULE
    elif not isinstance(p, str) or not 1 <= len(p) <= 64:
        err = "Wrong username or password"
    elif t != "reg" and limited(("try", u.lower()), 8, 900):         # somebody guessing one account from many addresses
        err = "Too many tries for this account - wait 15 minutes"
    if err:
        await peer.send_json({"t": "err", "m": err})
        return
    k, loop = u.lower(), asyncio.get_running_loop()
    a = store.acc.get(k)
    if t == "reg":
        if a is not None:
            err = "That username is taken"
        elif len(store.acc) >= MAX_ACCOUNTS or limited(("reg", ip), 4, 3600):
            err = "No new accounts right now - try again later"
        else:
            salt = secrets.token_hex(16)
            h = await loop.run_in_executor(None, pw_hash, p, salt, PW_ROUNDS)
            if k in store.acc:                       # somebody else took the name while we were hashing
                err = "That username is taken"
            else:
                a = store.acc[k] = {"n": u, "s": salt, "h": h, "r": PW_ROUNDS, "tv": secrets.token_hex(4), "c": int(time.time()),
                                    "seen": int(time.time()), "g": 0, "w": 0, "k": 0, "bk": 0, "ban": 0}
    else:
        salt = a["s"] if a else "00" * 16            # hash anyway, so a missing name takes just as long
        h = await loop.run_in_executor(None, pw_hash, p, salt, a.get("r", 100_000) if a else PW_ROUNDS)
        if a is None or not hmac.compare_digest(h, a["h"]):
            err = "Wrong username or password"
        elif a.get("ban"):
            err = "This account is banned"
        else:
            hits.pop(("try", k), None)
    if err:
        await peer.send_json({"t": "err", "m": err})
        return
    a["seen"] = int(time.time())
    store.put(k)
    await peer.send_json({"t": "auth", "u": a["n"], "tok": make_token(a)})


def add_results(room, rows):
    """Match results from a room's host; only players who really are in that room count."""
    now = time.time()
    if not isinstance(rows, list) or now - room.res_t < 30:
        return
    room.res_t = now
    for row in rows[:MAX_PLAYERS + 1]:
        try:
            k, win, kills = str(row[0]).lower(), bool(row[1]), max(0, min(99, int(row[2])))
        except (TypeError, ValueError, IndexError):
            continue
        a = store.acc.get(k)
        if a is None or k not in room.members:
            continue
        a["g"], a["w"], a["k"], a["bk"] = a["g"] + 1, a["w"] + int(win), a["k"] + kills, max(a["bk"], kills)
        a["seen"] = int(now)
        store.put(k)


# ------------------------------ rooms ------------------------------
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


async def do_host(peer, a):
    code = new_code()
    room = rooms[code] = Room(peer, a["n"])
    try:
        await peer.send_json({"t": "code", "c": code, "u": a["n"]})
        while True:
            _op, data = await peer.recv()          # besides keep-alive pings: room info and match results
            try:
                m = json.loads(data) if len(data) <= 4000 else {}
                if m.get("t") == "info":
                    room.info = {"s": str(m.get("s", ""))[:8], "m": str(m.get("m", ""))[:8], "n": max(0, min(99, int(m.get("n", 0))))}
                elif m.get("t") == "res":
                    add_results(room, m.get("r"))
            except (ValueError, TypeError, AttributeError):
                pass                               # a broken message is ignored, the room stays open
    except Exception:
        pass
    finally:
        rooms.pop(code, None)
        for j in list(room.joins.values()):
            if j.mate is None:
                j.ev.set()
                j.done = True


async def do_join(peer, first, a):
    room = rooms.get(str(first.get("c", "")).upper())
    if room is None:
        await peer.send_json({"t": "err", "m": "No room with that code"})
        return
    if room.live() >= MAX_PLAYERS:
        await peer.send_json({"t": "err", "m": "That room is full"})
        return
    me = a["n"].lower()
    if me == room.user.lower() or any(j.user.lower() == me and not j.done for j in room.joins.values()):
        await peer.send_json({"t": "err", "m": "This account is already in that room"})
        return
    room.nid += 1
    jid = room.nid
    j = room.joins[jid] = Join(peer, a["n"])
    room.members.add(me)
    try:
        await room.host.send_json({"t": "newc", "id": jid, "u": a["n"]})
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


# ------------------------------ admin page ------------------------------
def admin_on():
    return len(ADMIN_PASSWORD) >= 10


def admin_token():
    exp = int(time.time()) + 12 * 3600
    return "%d.%s" % (exp, sign("admin|%d|%s" % (exp, ADMIN_PASSWORD)))


def admin_ok(tok):
    try:
        exp, sig = str(tok).split(".")
        return admin_on() and int(exp) > time.time() and hmac.compare_digest(sig, sign("admin|%d|%s" % (int(exp), ADMIN_PASSWORD)))
    except ValueError:
        return False


def note(text):
    adminlog.append([int(time.time()), text[:120]])
    del adminlog[:-60]


def admin_state():
    online = {}
    for code, r in rooms.items():
        for n in [r.user] + [j.user for j in r.joins.values() if not j.done]:
            online[n.lower()] = code
    return {"up": int(time.time() - T0), "db": store.db, "enc": store.enc, "skipped": store.skipped, "loaded": store.loaded, "pending": len(store.dirty), "log": adminlog[::-1],
            "rooms": [{"c": c, "host": r.user, "players": [j.user for j in r.joins.values() if not j.done],
                       "s": r.info.get("s", "?"), "m": r.info.get("m", ""), "n": r.info.get("n", 0),
                       "age": int(time.time() - r.t0), "mb": round(r.bytes / 1e6, 1)} for c, r in rooms.items()],
            "acc": [{"u": a["n"], "c": a["c"], "seen": a["seen"], "g": a["g"], "w": a["w"], "k": a["k"], "bk": a["bk"],
                     "ban": int(bool(a.get("ban"))), "on": online.get(k, "")} for k, a in store.acc.items()]}


async def drop_player(k):
    """Throw an account out of every room (and close the rooms it hosts)."""
    for r in list(rooms.values()):
        if r.user.lower() == k:
            await r.host.close()
        for j in list(r.joins.values()):
            if j.user.lower() == k or r.user.lower() == k:
                await j.peer.close()
                if j.mate is not None:
                    await j.mate.close()


async def admin_do(m):
    a = m.get("a")
    if a == "event":
        k, code = m.get("k"), str(m.get("room", "*")).upper()
        if k not in EVENTS:
            return "Unknown event"
        try:
            n = max(1, min(20, int(m.get("n", 1))))
        except (TypeError, ValueError):
            n = 1
        ev = {"t": "adm", "k": k, "text": "".join(c for c in str(m.get("text", "")) if c.isprintable())[:70],
              "who": str(m.get("who", ""))[:12], "w": str(m.get("w", ""))[:24], "n": n}
        sent = 0
        for c, r in list(rooms.items()):
            if code in ("*", c):
                try:
                    await r.host.send_json(ev)
                    sent += 1
                except Exception:
                    pass
        note("event %s -> %s (%d rooms)" % (k, "all rooms" if code == "*" else code, sent))
        return "Sent to %d room%s" % (sent, "" if sent == 1 else "s")
    if a == "close":
        code = str(m.get("room", "")).upper()
        r = rooms.get(code)
        if r is None:
            return "No such room"
        await drop_player(r.user.lower())
        note("closed room " + code)
        return "Room closed"
    k = str(m.get("u", "")).lower()
    acc = store.acc.get(k)
    if acc is None:
        return "No such account"
    if a == "kick":
        await drop_player(k)
    elif a in ("ban", "unban"):
        acc["ban"] = int(a == "ban")
        if a == "ban":
            await drop_player(k)
    elif a == "del":
        await drop_player(k)
        del store.acc[k]
    elif a == "pw":
        if not good_pw(m.get("p"), acc["n"]):
            return PW_RULE
        salt = secrets.token_hex(16)
        acc["h"] = await asyncio.get_running_loop().run_in_executor(None, pw_hash, m["p"], salt, PW_ROUNDS)
        acc["s"], acc["r"], acc["tv"] = salt, PW_ROUNDS, secrets.token_hex(4)        # a new "tv" makes every older login stop working
    else:
        return "Unknown action"
    store.put(k)
    note("%s %s" % (a, acc["n"]))
    return "Done: %s %s" % (a, acc["n"])


async def reply(writer, status, body, ctype="application/json"):
    if not isinstance(body, bytes):
        body = json.dumps(body, separators=(",", ":")).encode()
    writer.write(("HTTP/1.1 %s\r\nContent-Type: %s\r\nContent-Length: %d\r\nConnection: close\r\nCache-Control: no-store\r\n"
                  "X-Frame-Options: DENY\r\nX-Content-Type-Options: nosniff\r\nReferrer-Policy: no-referrer\r\n\r\n"
                  % (status, ctype, len(body))).encode() + body)
    await writer.drain()


async def do_http(reader, writer, method, path, hdr, ip):
    path = path.split("?")[0].rstrip("/") or "/"
    if not path.startswith("/admin"):
        await reply(writer, "200 OK", ("Mini Royale relay: ok, %d rooms\n" % len(rooms)).encode(), "text/plain")   # health check / wake-up ping
        return
    if not admin_on():
        await reply(writer, "404 Not Found", b"The admin page is switched off (no ADMIN_PASSWORD is set on the server).\n", "text/plain")
        return
    if method == "GET" and path == "/admin":
        await reply(writer, "200 OK", ADMIN_PAGE, "text/html; charset=utf-8")
        return
    body = {}
    if method == "POST":
        n = int(hdr.get("content-length", "0"))
        if not 0 < n <= 4000:
            await reply(writer, "400 Bad Request", {"m": "bad request"})
            return
        body = json.loads(await asyncio.wait_for(reader.readexactly(n), 10))
        if not isinstance(body, dict):
            raise ValueError
    if method == "POST" and path == "/admin/login":
        if limited(("adm", ip), 5, 600) or limited("adm", 40, 600):         # also a global cap, in case the address is faked
            await reply(writer, "429 Too Many Requests", {"m": "Too many tries - wait 10 minutes"})
        elif hmac.compare_digest(str(body.get("pw", "")).encode(), ADMIN_PASSWORD.encode()):
            hits.pop(("adm", ip), None)
            note("admin logged in")
            await reply(writer, "200 OK", {"tok": admin_token()})
        else:
            await asyncio.sleep(1)
            await reply(writer, "403 Forbidden", {"m": "Wrong password"})
        return
    if not admin_ok(hdr.get("x-admin", "")):
        await reply(writer, "401 Unauthorized", {"m": "Log in again"})
    elif method == "GET" and path == "/admin/state":
        await reply(writer, "200 OK", admin_state())
    elif method == "POST" and path == "/admin/do":
        await reply(writer, "200 OK", {"m": await admin_do(body)})
    else:
        await reply(writer, "404 Not Found", {"m": "not found"})


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
        ip = hdr.get("cf-connecting-ip") or hdr.get("x-forwarded-for", "").split(",")[0].strip() or "?"
        if hdr.get("upgrade", "").lower() != "websocket" or "sec-websocket-key" not in hdr:
            req = lines[0].split(" ")
            peer.closed = True                       # plain HTTP: no WebSocket close frame after the answer
            await do_http(reader, writer, req[0], req[1] if len(req) > 1 else "/", hdr, ip)
            return
        acc = base64.b64encode(hashlib.sha1((hdr["sec-websocket-key"] + GUID).encode()).digest()).decode()
        writer.write(("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n"
                      "Sec-WebSocket-Accept: %s\r\n\r\n" % acc).encode())
        await writer.drain()
        _op, data = await asyncio.wait_for(peer.recv(), 15)
        first = json.loads(data)
        t = first.get("t")
        acct = check_token(first.get("tok")) if t in ("rhost", "rjoin") else None
        if t in ("rhost", "rjoin", "reg", "login") and first.get("v") != PROTO:
            await peer.send_json({"t": "err", "m": "Your game is out of date - get the newest version"})
        elif t in ("reg", "login"):
            await do_auth(peer, first, ip)
        elif t in ("rhost", "rjoin") and acct is None:
            await peer.send_json({"t": "err", "m": "Log in to your account to play online", "auth": 1})
        elif t == "rhost":
            if len(rooms) >= MAX_ROOMS:
                await peer.send_json({"t": "err", "m": "The server is busy, try again in a minute"})
            else:
                await do_host(peer, acct)
        elif t == "rjoin":
            await do_join(peer, first, acct)
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
    print("relay listening on", port, "| accounts saved:", store.db, "| encrypted:", store.enc, "| admin page:", admin_on(), flush=True)
    keep = asyncio.create_task(store.run())          # keep a reference so the task is not garbage-collected
    async with srv:
        await srv.serve_forever()
    del keep


if __name__ == "__main__":
    asyncio.run(main())
