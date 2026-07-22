// Browser editor (task #95, stage 3). A textarea bound to an embed-RGA Node:
// keystrokes become ins/del ops, live-synced over the WebSocket relay to other
// tabs/windows. Imports the runtime ESM directly (it is browser-safe). No
// framework, no bundler -- the relay serves these files (src/relay.mjs).

import { Node } from '../src/node.js';
import { WsTransport, NetworkNode } from '../src/transport.js';
import { applyTextEdit } from '../src/editbind.js';
import { compactibleEmbedRGA as DT } from '../../runtime/src/compact.js';

const $ = (id) => document.getElementById(id);
const short = (g) => (g ? g.slice(0, 8) : '—');

// ---- identity + room -------------------------------------------------------
const params = new URLSearchParams(location.search);
const ROOM = params.get('room') || 'doc';
const NAME = params.get('name') || 'peer-' + Math.random().toString(16).slice(2, 6);
const SALT = Math.floor(Math.random() * 1000); // per-peer tie-break for unique ids
$('me').textContent = NAME;
$('room').textContent = 'room ' + ROOM;

const node = new Node(DT, NAME);
let lamport = 0;
function mint() {
  let mx = 0; for (const id of node.head.state.keys()) if (id > mx) mx = id;
  lamport = Math.max(lamport, Math.floor(mx / 1000)) + 1;
  return lamport * 1000 + SALT; // strictly increasing across the room, unique per peer
}

// ---- transport -------------------------------------------------------------
const peerHeads = new Map(); // name -> head gid last advertised
const tp = new WsTransport(`ws://${location.host}`, ROOM, NAME);
const net = new NetworkNode(node, tp, { passive: false, onChange: () => { renderFromState(); renderPanels(); } });
tp.on('have', (m) => { if (m.from) { peerHeads.set(m.from, m.head); renderPanels(); } });
tp.on('delta', (m) => { if (m.from && m.head) { peerHeads.set(m.from, m.head); renderPanels(); } });
tp.on('leave', (m) => { peerHeads.delete(m.name); renderPanels(); });
tp.on('down', () => { $('conn').textContent = 'reconnecting…'; $('connDot').className = 'dot'; });
tp.on('up', () => { $('conn').textContent = 'connected'; $('connDot').className = 'dot on'; renderPanels(); });
tp.ready.then(() => { $('conn').textContent = 'connected'; $('connDot').className = 'dot on'; net.announce(); renderPanels(); })
  .catch(() => { $('conn').textContent = 'no relay'; });

// ---- editor binding: diff the textarea against the last rendered text -------
const editor = $('editor');
let lastText = '';

function currentText() { return node.read().join(''); }

/** Re-render the textarea from the RGA state, preserving the caret across a
 *  remote change by keeping its distance from the end stable. */
function renderFromState() {
  const next = currentText();
  if (next === editor.value) { lastText = next; return; }
  const fromEnd = editor.value.length - editor.selectionStart;
  editor.value = next;
  const pos = Math.max(0, next.length - fromEnd);
  try { editor.setSelectionRange(pos, pos); } catch {}
  lastText = next;
}

editor.addEventListener('input', () => {
  const neu = editor.value;
  const ids = DT.readIds(node.head.state); // display order; ids[i] shows at lastText[i]
  const { dels, inss } = applyTextEdit(node, ids, lastText, neu, mint);
  lastText = neu;
  if (dels || inss) { net.announce(); renderPanels(); }
});

// ---- panels ----------------------------------------------------------------
function renderPanels() {
  // convergence: do all known peers advertise my exact head gid?
  const mine = node.headGid;
  const others = [...peerHeads.entries()].filter(([n]) => n !== NAME);
  const agree = others.filter(([, h]) => h === mine).length;
  const badge = $('convBadge'), detail = $('convDetail');
  if (others.length === 0) { badge.className = 'conv no'; badge.textContent = 'solo (no other peers yet)'; detail.textContent = ''; }
  else if (agree === others.length) { badge.className = 'conv yes'; badge.textContent = '✓ converged'; detail.textContent = `all ${others.length} peer(s) on head ${short(mine)}`; }
  else { badge.className = 'conv no'; badge.textContent = `syncing… ${agree}/${others.length}`; detail.textContent = 'peers still catching up (gossip in flight)'; }

  // peers list
  const roster = [...node.registered].sort();
  $('peers').innerHTML = roster.map((nm) => {
    const h = nm === NAME ? mine : peerHeads.get(nm);
    const me = nm === NAME ? ' (you)' : '';
    return `<div class="peer"><span class="name">${nm}${me}</span><span class="hd">${short(h)}</span></div>`;
  }).join('');

  // certified-GC panel
  const sc = node.stableCut();
  $('cutInfo').textContent = sc.complete ? `${sc.meet.size} events` : `incomplete: missing ${sc.missing.join(',') || '—'}`;
  $('symInfo').textContent = String(node.symbolCount());
  $('epochInfo').textContent = String(node.epoch);
  $('gcBtn').disabled = !sc.complete || sc.meet.size === 0;

  // DAG
  const commits = [...node.dag.values()];
  $('dagCount').textContent = String(commits.length);
  $('dag').innerHTML = commits.slice(-40).reverse().map((c) => {
    const g = short(node.gid.get(c.id));
    const kind = c.parents.length === 0 ? 'root' : c.op ? `op ${c.op.replica}#${c.op.seq}` : (c.parents.length === 1 ? 'compact' : 'merge');
    return `<div class="c"><b>${g}</b> ${kind}</div>`;
  }).join('');
}

// ---- GC button: certified compactStable() on this peer ---------------------
$('gcBtn').addEventListener('click', () => {
  const before = node.symbolCount();
  const r = node.compactStable();
  const st = $('gcStatus');
  if (!r.compacted) { st.className = 'status warnc'; st.textContent = `refused: ${r.reason}`; }
  else {
    st.className = 'status good';
    st.textContent = `compacted: ${before} → ${node.symbolCount()} symbols, reads preserved, now epoch ${node.epoch}. ` +
      `(Other tabs stay at their epoch until they also GC — epochs are linearized; ` +
      `see the coordinated barrier in \`npm run demo\`.)`;
  }
  renderFromState(); renderPanels(); net.announce();
});

renderFromState();
renderPanels();
