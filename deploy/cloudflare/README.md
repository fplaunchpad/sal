# Cloudflare deployment (sal p2p demo)

One Worker serves the static sal tree and routes WebSocket upgrades to a
Durable Object per room (`src/worker.mjs`), the serverless twin of
`p2p-demo/src/relay.mjs` with the identical protocol. Free plan suffices
(SQLite-backed Durable Objects + WebSocket hibernation; an idle room costs
nothing).

```
./build.sh                 # stage web/src/runtime + prosemirror ESM into public/
npx wrangler dev           # local test (workerd, no login needed)
npx wrangler login         # once, interactive
npx wrangler deploy        # -> https://sal-p2p.<account>.workers.dev
```

Open `/p2p-demo/web/richtext.html?room=X&name=Y` on the deployed host ("/"
redirects there). The client already speaks `wss://` under https and sends
`?room=` on the upgrade URL, which is how the Worker picks the room's Durable
Object before any message arrives.

Notes:

- FREE-TIER QUOTA: Durable Object requests are metered per day, and every
  incoming WebSocket message counts. When the cap is hit, upgrades return 500
  ("Exceeded allowed volume of requests in Durable Objects free tier") until
  the daily reset (UTC midnight); static assets keep serving. The client
  retries with backoff, so open tabs heal on reset. Presence is throttled
  (min 300ms between sends, 20s heartbeat) to keep idle burn low; Workers
  Paid removes the cap if the deployment should be reliably public.

- `build.sh` re-stages `public/` from the repo; run it before every deploy.
- The DO relay is DUMB (never inspects the CRDT payload). This same DO can
  become a merging SyncServer hub: it would hold a headless
  `DistributedReplica` and persist records to DO storage, so peers collaborate
  asynchronously without any browser online.
- `html_handling = "none"` keeps asset URLs verbatim (the import map depends
  on exact paths).
- The root README records what is verified (the deployed editor is a tested
  mirror of the Lean proofs; the relay is deliberately outside the
  TCB, but commits are unauthenticated).
