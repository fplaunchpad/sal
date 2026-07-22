// Cloudflare deployment of the p2p demo (tasks #95/#107): one Worker serves
// the static sal tree (assets binding) and routes WebSocket upgrades to a
// DURABLE OBJECT per room -- the serverless twin of p2p-demo/src/relay.mjs,
// speaking the identical protocol (join/roster/broadcast/to-routing/leave).
// The room name rides the upgrade URL (?room=...) because the DO must be
// chosen BEFORE any message can arrive; WsTransport already sends it.
//
// The DO uses the WebSocket HIBERNATION API: membership is recoverable from
// state.getWebSockets() + per-socket attachments, so an idle room costs
// nothing. The relay stays DUMB (never inspects the CRDT payload); promoting
// it to a merging SyncServer hub is the design note's next step.

export class Room {
  constructor(state) { this.state = state; }

  async fetch(request) {
    if (request.headers.get('Upgrade') !== 'websocket') {
      return new Response('expected websocket', { status: 426 });
    }
    const pair = new WebSocketPair();
    const [client, server] = Object.values(pair);
    this.state.acceptWebSocket(server);
    return new Response(null, { status: 101, webSocket: client });
  }

  #peers() {
    return this.state.getWebSockets()
      .map((ws) => [ws.deserializeAttachment()?.name ?? null, ws]);
  }
  #send(ws, obj) { try { ws.send(JSON.stringify(obj)); } catch {} }

  webSocketMessage(ws, data) {
    let msg;
    try { msg = JSON.parse(typeof data === 'string' ? data : new TextDecoder().decode(data)); }
    catch { return; }
    if (msg.t === 'join') {
      const names = this.#peers().filter(([n, w]) => n && w !== ws).map(([n]) => n);
      ws.serializeAttachment({ name: msg.name });
      this.#send(ws, { t: 'roster', names });
      for (const [n, peer] of this.#peers()) {
        if (peer !== ws && n) this.#send(peer, { t: 'join', name: msg.name });
      }
      return;
    }
    const me = ws.deserializeAttachment()?.name;
    if (!me) return; // messages before join are dropped, as in relay.mjs
    const tagged = { ...msg, from: me };
    if (msg.to) {
      for (const [n, peer] of this.#peers()) if (n === msg.to) this.#send(peer, tagged);
    } else {
      for (const [, peer] of this.#peers()) if (peer !== ws) this.#send(peer, tagged);
    }
  }

  webSocketClose(ws) { this.#leave(ws); }
  webSocketError(ws) { this.#leave(ws); }
  #leave(ws) {
    const me = ws.deserializeAttachment()?.name;
    try { ws.close(); } catch {}
    if (!me) return;
    for (const [n, peer] of this.#peers()) {
      if (peer !== ws && n) this.#send(peer, { t: 'leave', name: me });
    }
  }
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);
    if (request.headers.get('Upgrade') === 'websocket') {
      const room = url.searchParams.get('room') || 'default';
      return env.ROOMS.get(env.ROOMS.idFromName(room)).fetch(request);
    }
    if (url.pathname === '/') {
      return Response.redirect(new URL('/p2p-demo/web/richtext.html', url).toString(), 302);
    }
    return env.ASSETS.fetch(request);
  },
};
