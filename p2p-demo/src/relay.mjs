// The RELAY (task #95, stage 2 transport server) + a static file server for the
// browser UI (stage 3). A WebSocket relay carries the sync gossip (have / req /
// delta / roster / join / leave) between p2p nodes grouped into ROOMS (one room
// per document id). It is a dumb switch: it broadcasts a client's message to
// the other clients in the same room, or routes it to a single named client
// when the message carries `to`. It never inspects the CRDT payload -- the nodes
// converge (src/node.js), the relay only moves bytes.
//
// The same HTTP server serves the sal tree statically so the browser editor can
// import the runtime ESM directly (runtime/src is browser-safe, dependency-
// free), making the demo one command: `npm run relay` then open the printed URL.
//
// HONEST FRAMING: this is a star RELAY, not a mesh -- every message hops through
// the server. The Transport interface (src/transport.js) is shaped so a WebRTC
// data-channel mesh could replace it without touching node logic. See README
// "Honest limits".
//
// MEMBERSHIP: on join the relay tells the newcomer the current roster and tells
// the room a peer joined; on disconnect it announces a leave. That roster is
// the closed replica set the stability certificate quantifies over.

import { WebSocketServer } from 'ws';
import { fileURLToPath } from 'node:url';
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';

const SAL_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const MIME = { '.html': 'text/html', '.js': 'text/javascript', '.mjs': 'text/javascript',
  '.css': 'text/css', '.json': 'application/json', '.svg': 'image/svg+xml', '.ico': 'image/x-icon' };

function serveStatic(req, res) {
  let urlPath = decodeURIComponent(new URL(req.url, 'http://x').pathname);
  if (urlPath === '/' || urlPath === '') urlPath = '/p2p-demo/web/index.html';
  const full = path.join(SAL_ROOT, path.normalize(urlPath));
  if (!full.startsWith(SAL_ROOT)) { res.writeHead(403); res.end('forbidden'); return; } // no traversal
  fs.readFile(full, (err, data) => {
    if (err) { res.writeHead(404); res.end('not found: ' + urlPath); return; }
    res.writeHead(200, { 'content-type': MIME[path.extname(full)] || 'application/octet-stream' });
    res.end(data);
  });
}

/** Start a relay + static server. port 0 picks an ephemeral port (tests).
 *  Returns { server, port, close, rooms }. */
export function startRelay(port = 0, { host = '127.0.0.1' } = {}) {
  const server = http.createServer(serveStatic);
  const wss = new WebSocketServer({ server });
  const rooms = new Map(); // room -> Map(name -> ws)
  const roomOf = (r) => { if (!rooms.has(r)) rooms.set(r, new Map()); return rooms.get(r); };
  const send = (ws, obj) => { if (ws.readyState === ws.OPEN) ws.send(JSON.stringify(obj)); };

  wss.on('connection', (ws) => {
    ws.name = null; ws.room = null;
    ws.on('message', (buf) => {
      let msg; try { msg = JSON.parse(buf.toString()); } catch { return; }
      if (msg.t === 'join') {
        ws.name = msg.name; ws.room = msg.room;
        const room = roomOf(msg.room);
        const names = [...room.keys()];
        room.set(msg.name, ws);
        send(ws, { t: 'roster', names });
        for (const [nm, peer] of room) if (nm !== msg.name) send(peer, { t: 'join', name: msg.name });
        return;
      }
      if (!ws.room) return;
      const room = roomOf(ws.room);
      const tagged = { ...msg, from: ws.name };
      if (msg.to) { const peer = room.get(msg.to); if (peer) send(peer, tagged); }
      else for (const [nm, peer] of room) if (nm !== ws.name) send(peer, tagged);
    });
    ws.on('close', () => {
      if (!ws.room) return;
      const room = roomOf(ws.room);
      if (room.get(ws.name) === ws) room.delete(ws.name);
      for (const [, peer] of room) send(peer, { t: 'leave', name: ws.name });
      if (room.size === 0) rooms.delete(ws.room);
    });
  });

  return new Promise((resolve) => {
    server.listen(port, host, () => resolve({
      server, port: server.address().port, rooms,
      close: () => new Promise((res) => { wss.close(); server.close(res); }),
    }));
  });
}

// Run directly: `node src/relay.mjs` (PORT env or 8787).
if (import.meta.url === `file://${process.argv[1]}`) {
  const port = Number(process.env.PORT) || 8787;
  const host = process.env.HOST || '127.0.0.1';
  startRelay(port, { host }).then(({ port }) => {
    console.log(`[relay] ws + UI on http://${host}:${port}/  (open in 2+ tabs; Ctrl-C to stop)`);
  });
}
