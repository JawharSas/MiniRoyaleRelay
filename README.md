# Mini Royale relay

Small WebSocket relay for Mini Royale: pairs players by room code, keeps the player accounts and serves the private admin page (`/admin`). Standard library only (`python relay.py`). Deployed on Render's free plan.

Secrets (`ADMIN_PASSWORD`, `UPSTASH_REDIS_REST_URL`, `UPSTASH_REDIS_REST_TOKEN`) are set as environment variables on the host, never in this repo.
