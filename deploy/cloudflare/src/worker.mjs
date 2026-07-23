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

import { HubPeer, HUB_NAME } from '../../../p2p-demo/src/hub.js';

// ctx.storage as the async KV the RefStore consumes (same interface as
// MemoryKV / openIdbKV): keys are '<store>:<key>'.
class DoKV {
  constructor(storage) { this.s = storage; }
  #k(store, key) { return store + ':' + key; }
  async get(store, key) { return (await this.s.get(this.#k(store, key))) ?? null; }
  async put(store, key, val) { await this.s.put(this.#k(store, key), val); }
  async delete(store, key) { await this.s.delete(this.#k(store, key)); }
  async entries(store) {
    const m = await this.s.list({ prefix: store + ':' });
    const pre = store.length + 1;
    return [...m].map(([k, v]) => [k.slice(pre), v]);
  }
}

export class Room {
  constructor(state) { this.state = state; this.hub = null; }

  // THE SYNC HUB (p2p-demo/src/hub.js): a headless replica for this room,
  // persisted in the DO's own storage, so the doc survives everyone
  // disconnecting AND the DO hibernating (rebuilt lazily from storage).
  // Invisible to clients: never in rosters, never authors, cannot block GC.
  #ensureHub(dt) {
    if (!this.hub) {
      const roomName = 'doc'; // one DO == one room; the storage is already scoped
      this.hub = new HubPeer({
        room: roomName,
        datatypeLabel: dt,
        kv: new DoKV(this.state.storage),
        broadcast: (obj) => { for (const [, ws] of this.#peers()) this.#send(ws, obj); },
        sendTo: (name, obj) => { for (const [n, ws] of this.#peers()) if (n === name) this.#send(ws, obj); },
      }).init();
    }
    return this.hub;
  }

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

  async webSocketMessage(ws, data) {
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
      (await this.#ensureHub(msg.dt)).onPeerJoin(msg.name);
      return;
    }
    const me = ws.deserializeAttachment()?.name;
    if (!me) return; // messages before join are dropped, as in relay.mjs
    const tagged = { ...msg, from: me };
    if (msg.to === HUB_NAME) { (await this.#ensureHub()).onMessage(tagged); return; }
    if (msg.to) {
      for (const [n, peer] of this.#peers()) if (n === msg.to) this.#send(peer, tagged);
    } else {
      for (const [, peer] of this.#peers()) if (peer !== ws) this.#send(peer, tagged);
      (await this.#ensureHub()).onMessage(tagged); // the hub hears broadcasts
    }
  }

  webSocketClose(ws) { this.#leave(ws); }
  webSocketError(ws) { this.#leave(ws); }
  async #leave(ws) {
    const me = ws.deserializeAttachment()?.name;
    try { ws.close(); } catch {}
    if (!me) return;
    for (const [n, peer] of this.#peers()) {
      if (peer !== ws && n) this.#send(peer, { t: 'leave', name: me });
    }
    if (this.hub) (await this.hub).onPeerLeave(me);
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
