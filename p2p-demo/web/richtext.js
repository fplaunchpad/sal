// Browser RICH-TEXT editor (task #107): a PROSEMIRROR view over the verified
// Peritext datatype. One editing surface, edited directly; no preview pane.
//
// Division of labor:
//   - ProseMirror owns the DOM: caret behavior, IME, paste, block structure.
//   - The verified peritext datatype owns the TRUTH: every gesture is diffed
//     into ins/del/addMark/removeMark ops via src/peritextbind.js (headless-
//     tested) and lands as ONE batched commit (commitBatch). After each local
//     transaction the PM doc is RECONCILED against read(): if PM's optimistic
//     mark inheritance disagrees with the datatype's span-boundary semantics
//     (e.g. whether a char typed at a span edge is bold), read() wins.
//   - The doc model is flat (chars + '\n'); PM paragraphs are presentation.
//     flatToPm/pmToFlat convert offsets (each paragraph boundary costs 2).
//   - Presence (ephemeral, off-DAG) renders as PM DECORATIONS: inline
//     highlights for selections, widgets for carets. Never committed.
//
// MERGING IS AUTOMATIC: each local gesture commits and announces; NetworkNode
// absorbs peer deltas with ingest + mergeWithGid on arrival (three-way merge
// over the DAG, fast-forward when there is no divergence). No manual step.

import { Schema } from 'prosemirror-model';
import { EditorState, Plugin, TextSelection } from 'prosemirror-state';
import { EditorView, Decoration, DecorationSet } from 'prosemirror-view';
import { keymap } from 'prosemirror-keymap';
import { baseKeymap } from 'prosemirror-commands';

import { Node } from '../src/node.js';
import { WsTransport, NetworkNode } from '../src/transport.js';
import {
  textEditOps, formatOps, commitOps, selectionHas, coveringMarkTypes, markSpan, specRead,
} from '../src/peritextbind.js';
import { shouldCompact } from '../src/autogc.js';
import { Presence, presenceSpan } from '../src/presence.js';
import { openIdbKV, RefStore } from '../src/idbstore.js';
import { nodeRecords, wireFromRecords } from '../src/records.js';
// the COMPACTIBLE peritext: same datatype + the certified marks-layer GC
// hooks (#110), so compactStable FIRES here instead of refusing
import { compactiblePeritext } from '../../runtime/src/compact-peritext.js';

const $ = (id) => document.getElementById(id);
const short = (g) => (g ? g.slice(0, 8) : '?');
const esc = (s) => s.replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));

// ---- identity + room -------------------------------------------------------
const params = new URLSearchParams(location.search);
const ROOM = params.get('room') || 'rtdoc';
// a name / room slug: room ids and replica names ride query + ws upgrade URLs.
// `~` is reserved as the display~session separator, so it is not a slug char.
const slug = (s) => s.trim().replace(/\s+/g, '-').replace(/[^A-Za-z0-9._-]/g, '');
// TWO-LEVEL IDENTITY. The DISPLAY name is human-facing and remembered;
// resolution: an explicit ?name= wins (per-session) and is then SCRUBBED from
// the address bar so a shared URL never carries your name into a
// collaborator's tab; otherwise a name remembered in THIS browser (set via
// the UI), else a fresh random one that is then remembered.
const NAME_KEY = 'sal.p2p.name';
const readSavedName = () => { try { return localStorage.getItem(NAME_KEY); } catch { return null; } };
const rememberName = (n) => { try { localStorage.setItem(NAME_KEY, n); } catch {} };
let DISPLAY = params.get('name');
if (DISPLAY) {
  const u = new URL(location.href); u.searchParams.delete('name'); // keep the address bar shareable
  try { history.replaceState(null, '', u.toString()); } catch {}
} else {
  DISPLAY = readSavedName() || 'peer-' + Math.random().toString(16).slice(2, 6);
  rememberName(DISPLAY);
}
DISPLAY = slug(DISPLAY.replace(/~.*/, '')) || 'peer'; // strip any session tag, then slug
// The REPLICA id must be UNIQUE PER TAB: two tabs (or two devices) sharing a
// display name are DISTINCT CRDT replicas -- one shared id means colliding
// seq/event keys and a corrupt frontier. A short session token disambiguates;
// `displayOf` strips it back to the human name for the UI and roster.
//
// The token lives in sessionStorage keyed by the doc, NOT re-minted per load:
// sessionStorage survives a RELOAD (same tab -> same replica id, so refreshing
// does not spawn a new author), is isolated per TAB (two tabs stay distinct),
// and clears on tab close (a genuinely new session is then a new replica).
const SESSION = (() => {
  const key = `sal.p2p.session.${ROOM}`;
  try {
    let s = sessionStorage.getItem(key);
    if (!s) { s = Math.random().toString(16).slice(2, 6); sessionStorage.setItem(key, s); }
    return s;
  } catch { return Math.random().toString(16).slice(2, 6); }
})();
const NAME = `${DISPLAY}~${SESSION}`;
const displayOf = (n) => n.split('~')[0];
const SALT = Math.floor(Math.random() * 1000); // per-peer tie-break for unique ids
$('me').textContent = DISPLAY;
$('docName').textContent = ROOM;
document.title = `${ROOM} · sal rich text`;

// ---- THEME (system / light / dark), remembered in this browser ------------
// The saved theme is applied pre-paint by an inline <head> script (no flash);
// here we wire the header toggle and keep 'system' following the OS live.
const THEME_KEY = 'sal.p2p.theme';
const THEMES = ['system', 'light', 'dark'];
const THEME_ICON = { system: '◐', light: '☀', dark: '☾' };
const THEME_LABEL = { system: 'Auto', light: 'Light', dark: 'Dark' };
let theme = (() => { try { return localStorage.getItem(THEME_KEY) || 'system'; } catch { return 'system'; } })();
function applyTheme(t) {
  const root = document.documentElement;
  if (t === 'system') delete root.dataset.theme; else root.dataset.theme = t;
  const btn = $('themeBtn');
  if (btn) {
    // show the CURRENT mode with a label so it reads as a theme control, not a
    // bare glyph; the tooltip names what the next click switches to
    const next = THEMES[(THEMES.indexOf(t) + 1) % 3];
    btn.textContent = `${THEME_ICON[t]} ${THEME_LABEL[t]}`;
    btn.title = `Theme: ${THEME_LABEL[t]} (${t === 'system' ? 'follows your OS' : t}). Click for ${THEME_LABEL[next]}`;
  }
  const dark = t === 'dark' || (t === 'system' && matchMedia('(prefers-color-scheme: dark)').matches);
  const meta = document.querySelector('meta[name="theme-color"]');
  if (meta) meta.content = dark ? '#0e1014' : '#ffffff';
}
applyTheme(theme);
$('themeBtn')?.addEventListener('click', () => {
  theme = THEMES[(THEMES.indexOf(theme) + 1) % THEMES.length];
  try { localStorage.setItem(THEME_KEY, theme); } catch {}
  applyTheme(theme);
});
matchMedia('(prefers-color-scheme: dark)').addEventListener?.('change', () => { if (theme === 'system') applyTheme('system'); });

// ---- research drawer: remember open/closed (collapsed by default) ---------
const drawer = $('infoDrawer');
if (drawer) {
  try { drawer.open = localStorage.getItem('sal.p2p.drawer') !== '0'; } catch {} // default OPEN, unless explicitly collapsed
  drawer.addEventListener('toggle', () => { try { localStorage.setItem('sal.p2p.drawer', drawer.open ? '1' : '0'); } catch {} });
}

// "verified core" explainer: what's proven vs what's unverified glue
$('verifiedBadge')?.addEventListener('click', () => {
  const p = $('verifiedPanel'), show = p.hasAttribute('hidden');
  p.toggleAttribute('hidden', !show);
  $('verifiedBadge').setAttribute('aria-expanded', String(show));
});

// PERSISTENT LOCAL FORGET (per doc, this browser). Runtime `forget` is
// transient: roster/join/ingest re-register a peer, and a reload rebuilds the
// roster from stored author metadata, so a forgotten peer keeps coming back. This
// set is persisted and RE-APPLIED on every render (`enforceForgotten`), so a
// peer you forget stays forgotten on THIS device until you un-forget it. Local
// only (other peers are unaffected); the runtime `forget` is the mechanism.
const FORGOTTEN_KEY = `sal.p2p.forgotten.${ROOM}`;
const forgotten = (() => { try { return new Set(JSON.parse(localStorage.getItem(FORGOTTEN_KEY) || '[]')); } catch { return new Set(); } })();
const saveForgotten = () => { try { localStorage.setItem(FORGOTTEN_KEY, JSON.stringify([...forgotten])); } catch {} };
function enforceForgotten() { for (const n of forgotten) node.forget(n); } // idempotent re-apply

let node = new Node(compactiblePeritext, NAME);

// ---- DURABLE STORE (local-first): the doc lives in IndexedDB, keyed by the
// room id. LOAD-BEFORE-CONNECT (top-level await): close the tab, reopen the
// same room, and the doc is there before any peer answers; the relay stays
// stateless. Every head change re-persists (content-addressed puts are
// idempotent; a tampered stored record trips the ingest gate on load).
// Reopening under a NEW session name keeps the history and roster and starts
// a fresh authoring seq (src/records.js).
let store = null;
let restoredCommits = 0;
try {
  store = new RefStore(await openIdbKV());
  const restored = await store.loadNode(ROOM, compactiblePeritext, { name: NAME });
  if (restored) { node = restored; restoredCommits = restored.dag.size - 1; }
} catch (e) {
  console.warn('[idb] local store unavailable:', e?.message ?? e);
  store = null;
}
let persistedGid = node.headGid;
function persistIfChanged() {
  if (!store) return;
  const g = node.headGid;
  if (g === persistedGid || node.dag.size <= 1) return; // nothing authored yet
  persistedGid = g;
  store.persistNode(ROOM, node).catch((e) => console.warn('[idb] persist failed:', e?.message ?? e));
}

// ---- DOC SWITCHER ----------------------------------------------------------
// Docs are identified by their room name (no rename): this makes creating and
// switching between them a visible affordance instead of hand-editing the URL.
// The picker lists docs saved in THIS browser (RefStore.listDocs) plus the
// current one; creating or picking a doc navigates, carrying the editor name.
function gotoDoc(room) {
  const u = new URL(location.href);
  u.searchParams.set('room', room);
  u.searchParams.set('name', DISPLAY); // carry the display name (a fresh session id is minted on load)
  location.href = u.toString();
}
async function populateDocPicker() {
  const names = new Set([ROOM]); // the current doc is always listed and selected
  if (store) { try { for (const d of await store.listDocs()) names.add(d.docId); } catch {} }
  $('docPicker').innerHTML = [...names].sort().map((n) =>
    `<option value="${esc(n)}"${n === ROOM ? ' selected' : ''}>${esc(n)}</option>`).join('');
}
$('docPicker').addEventListener('change', (e) => { if (e.target.value !== ROOM) gotoDoc(e.target.value); });
$('newDocBtn').addEventListener('click', () => {
  $('newDocBar').classList.add('show'); $('newDocInput').value = ''; $('newDocInput').focus();
});
$('newDocCancel').addEventListener('click', () => $('newDocBar').classList.remove('show'));
function createDoc() {
  const room = slug($('newDocInput').value);
  if (!room) { $('newDocInput').focus(); return; }
  if (room === ROOM) { $('newDocBar').classList.remove('show'); return; } // already here
  gotoDoc(room);
}
$('newDocCreate').addEventListener('click', createDoc);
$('newDocInput').addEventListener('keydown', (e) => {
  if (e.key === 'Enter') createDoc();
  else if (e.key === 'Escape') $('newDocBar').classList.remove('show');
});
populateDocPicker();

// ---- RENAME (your display name) --------------------------------------------
// Click your name to change it. Renaming REOPENS the doc under the new name
// (a reload with ?name=): the history and roster are kept, a fresh authoring
// seq starts, and the choice is remembered in this browser for future docs.
$('me').addEventListener('click', () => {
  $('nameBar').classList.add('show'); $('nameInput').value = DISPLAY; $('nameInput').select();
});
$('nameCancel').addEventListener('click', () => $('nameBar').classList.remove('show'));
function commitRename() {
  const name = slug($('nameInput').value.replace(/~.*/, ''));
  if (!name) { $('nameInput').focus(); return; }
  if (name === DISPLAY) { $('nameBar').classList.remove('show'); return; }
  rememberName(name); // sticky, then reopen under it (?name= is scrubbed on load)
  const u = new URL(location.href);
  u.searchParams.set('room', ROOM);
  u.searchParams.set('name', name);
  location.href = u.toString();
}
$('nameSave').addEventListener('click', commitRename);
$('nameInput').addEventListener('keydown', (e) => {
  if (e.key === 'Enter') commitRename();
  else if (e.key === 'Escape') $('nameBar').classList.remove('show');
});

// ---- DEBOUNCED FLUSH: the default commit granularity is a typing RUN -------
// Local ops buffer in `pending`; the editor renders the SPECULATIVE state
// (head + pending, src/peritextbind.js specRead). flush() seals the buffer as
// ONE group-op commit (commitBatch) and announces. Triggers: a short idle
// pause, a MAX-LATENCY DEADLINE (a continuous typist must still sync: the
// idle timer alone would defer forever), blur, before a format gesture,
// before a manual merge, on unload. Pending ops are self-contained CRDT ops,
// so a remote merge landing mid-buffer is harmless (specRead re-derives on
// the new head).
const FLUSH_IDLE_MS = 300;  // seal after this pause...
const FLUSH_MAX_MS = 1000;  // ...but never later than this after the first buffered op
let pending = [];
let flushTimer = null;
let deadlineTimer = null;
const curDoc = () => specRead(node, pending);

function flush() {
  if (flushTimer) { clearTimeout(flushTimer); flushTimer = null; }
  if (deadlineTimer) { clearTimeout(deadlineTimer); deadlineTimer = null; }
  if (!pending.length) return;
  commitOps(node, pending.splice(0)); // one commit for the whole run
  net.announce();
  renderConv();
}
function scheduleFlush() {
  if (flushTimer) clearTimeout(flushTimer);
  flushTimer = setTimeout(flush, FLUSH_IDLE_MS);
  if (!deadlineTimer) deadlineTimer = setTimeout(flush, FLUSH_MAX_MS);
}
window.addEventListener('beforeunload', flush);
// browsers FREEZE hidden tabs (timers fully suspended): seal + announce the
// run at the moment of hiding, or it would sit unflushed until refocus
document.addEventListener('visibilitychange', () => { if (document.visibilityState === 'hidden') flush(); });

// mint: strictly-increasing, unique per peer, and ABOVE every char id already
// in the doc (so a new mark's ts outranks pre-existing chars: end-side growth
// grabs only text typed after the mark). Scans the SPECULATIVE doc (pending
// included), salted per peer.
let lamport = 0;
function mint() {
  let mx = 0; for (const e of curDoc()) if (e.id > mx) mx = e.id;
  lamport = Math.max(lamport, Math.floor(mx / 1000)) + 1;
  return lamport * 1000 + SALT;
}

// ---- state cache: flat text + char ids aligned with it (speculative) -------
let lastText = '';
let lastIds = [];
function refreshCache() {
  const doc = curDoc();
  lastIds = doc.map((e) => e.id);
  lastText = doc.map((e) => e.char).join('');
}

// ---- PM schema: paragraphs are presentation; the model is flat -------------
const schema = new Schema({
  nodes: {
    doc: { content: 'paragraph+' },
    paragraph: { content: 'text*', toDOM: () => ['p', 0], parseDOM: [{ tag: 'p' }] },
    text: {},
  },
  marks: {
    bold: { toDOM: () => ['strong', 0], parseDOM: [{ tag: 'strong' }, { tag: 'b' }] },
    italic: { toDOM: () => ['em', 0], parseDOM: [{ tag: 'em' }, { tag: 'i' }] },
    underline: { toDOM: () => ['u', 0], parseDOM: [{ tag: 'u' }] },
    // inclusive:false matches the datatype's exclusive-end gravity (PM then
    // does not extend these under typing at the edge; read() is the truth
    // either way via the reconcile)
    link: {
      attrs: { href: { default: '' } }, inclusive: false,
      // href only for http(s) (no javascript: vectors); Cmd/Ctrl+Click opens
      toDOM: (m) => {
        const safe = /^https?:\/\//i.test(m.attrs.href) ? m.attrs.href : null;
        return ['a', { ...(safe ? { href: safe } : {}), title: `${m.attrs.href} (Cmd/Ctrl+Click opens)`, class: 'plink' }, 0];
      },
      parseDOM: [{ tag: 'a' }],
    },
    // excludes:'' lets DIFFERENT comments coexist on the same char -- the PM
    // face of the datatype's unique-mtype encoding (comment:<id>, note in value)
    comment: {
      attrs: { id: {}, text: { default: '' } }, inclusive: false, excludes: '',
      toDOM: (m) => ['span', { class: 'pcomment', title: m.attrs.text }, 0],
      parseDOM: [],
    },
  },
});

/** The PM marks for one read() entry (unknown mtypes are preserved in state
 *  but not rendered). */
function pmMarksForEntry(e) {
  const out = [];
  for (const m of e.marks) {
    if (m.mtype === 'bold') out.push(schema.marks.bold.create());
    else if (m.mtype === 'italic') out.push(schema.marks.italic.create());
    else if (m.mtype === 'underline') out.push(schema.marks.underline.create());
    else if (m.mtype === 'link') out.push(schema.marks.link.create({ href: m.value ?? '' }));
    else if (m.mtype.startsWith('comment:')) {
      out.push(schema.marks.comment.create({ id: m.mtype.slice(8), text: m.value ?? '' }));
    }
  }
  return out;
}

/** read() -> PM doc: '\n' splits paragraphs, mark runs become marked text. */
function pmDocFromRead() {
  const paras = [];
  let inl = [], run = '', sig = null, cur = [];
  const emit = () => { if (run) { inl.push(schema.text(run, cur)); run = ''; } };
  for (const e of curDoc()) { // SPECULATIVE doc: head + pending
    if (e.char === '\n') { emit(); paras.push(schema.node('paragraph', null, inl)); inl = []; sig = null; continue; }
    const k = JSON.stringify(e.marks); // marks are mtype-sorted in read()
    if (k !== sig) { emit(); sig = k; cur = pmMarksForEntry(e); }
    run += e.char;
  }
  emit(); paras.push(schema.node('paragraph', null, inl));
  return schema.node('doc', null, paras);
}

/** PM doc -> flat text (paragraph boundaries are '\n'). */
function flatFromDoc(d) {
  const parts = [];
  d.forEach((p) => parts.push(p.textContent));
  return parts.join('\n');
}

// flat offset f <-> PM position: each char costs 1, each '\n' (a paragraph
// boundary: close + open) costs 2, and the first paragraph open costs 1.
function flatToPm(f, flat) {
  let nl = 0;
  for (let i = 0; i < f; i++) if (flat[i] === '\n') nl++;
  return 1 + f + nl;
}
function pmToFlat(pos, flat) {
  for (let f = 0; f <= flat.length; f++) if (flatToPm(f, flat) >= pos) return f;
  return flat.length;
}

function selFlat(state) {
  const flat = flatFromDoc(state.doc);
  return { anchor: pmToFlat(state.selection.anchor, flat), focus: pmToFlat(state.selection.head, flat) };
}
function setFlatSel(tr, anchor, focus) {
  const flat = flatFromDoc(tr.doc);
  const c = (x) => Math.max(0, Math.min(x, flat.length));
  try { tr.setSelection(TextSelection.create(tr.doc, flatToPm(c(anchor), flat), flatToPm(c(focus), flat))); } catch {}
  return tr;
}

/** Carry a caret across a remote change by char ids: keep it after the
 *  nearest SURVIVING char it used to sit after. */
function mapOffset(oldIds, newIds, off) {
  for (let i = Math.min(off, oldIds.length) - 1; i >= 0; i--) {
    const j = newIds.indexOf(oldIds[i]);
    if (j !== -1) return j + 1;
  }
  return 0;
}

// ---- transport + presence ---------------------------------------------------
const peerHeads = new Map();
// ttl generous (90s): hidden tabs get their timers throttled to ~1/min, so a
// backgrounded peer's heartbeat stretches; leave/keepalive still removes the
// genuinely departed promptly
const presence = new Presence(90000);     // ephemeral, off-DAG peer cursors/selections
let connected = false;
const tp = new WsTransport(`${location.protocol === 'https:' ? 'wss' : 'ws'}://${location.host}`, ROOM, NAME, { dt: 'peritext' });
const net = new NetworkNode(node, tp, { passive: false, onChange: () => onRemote() });
tp.on('have', (m) => { if (m.from) { peerHeads.set(m.from, m.head); renderConv(); } });
tp.on('delta', (m) => { if (m.from && m.head) { peerHeads.set(m.from, m.head); renderConv(); } });
tp.on('leave', (m) => { peerHeads.delete(m.name); presence.remove(m.name); renderConv(); presenceTick(); });
// PRESENCE is a plain room broadcast the relay forwards (tagged with `from`);
// never ingested, merged, or persisted -- it just paints where peers are.
tp.on('presence', (m) => {
  if (m.from && m.from !== NAME) { presence.update(m.from, { anchor: m.anchor, focus: m.focus }, Date.now()); presenceTick(); }
});
tp.on('join', () => sendPresence()); // greet a newcomer with my cursor
// the transport auto-reconnects after a drop (backgrounded tabs get their
// sockets closed); on 'up' NetworkNode already re-announces to catch up
tp.on('down', () => { $('conn').textContent = 'reconnecting…'; $('connDot').className = 'dot'; });
tp.on('up', () => { $('conn').textContent = 'connected'; $('connDot').className = 'dot on'; sendPresence(); renderConv(); });
tp.ready.then(() => { connected = true; $('conn').textContent = 'connected'; $('connDot').className = 'dot on'; net.announce(); sendPresence(); renderConv(); })
  .catch(() => { $('conn').textContent = 'no relay (local only)'; });

// presence is THROTTLED (every caret move used to broadcast: that is the
// dominant message volume, and Durable Object requests are metered): at most
// one send per PRESENCE_MIN_MS with a trailing send, plus a slow heartbeat
const PRESENCE_MIN_MS = 300;
let lastPresence = { anchor: 0, focus: 0 };
let lastPresenceAt = 0;
let presenceTrailer = null;
/** Broadcast my caret/selection (flat offsets). Ephemeral: fire-and-forget. */
function sendPresence(sel) {
  if (!connected) return;
  let s = sel;
  if (!s) { try { s = selFlat(view.state); } catch { s = lastPresence; } }
  lastPresence = { anchor: s.anchor, focus: s.focus };
  const now = Date.now();
  if (now - lastPresenceAt < PRESENCE_MIN_MS) {
    if (!presenceTrailer) {
      presenceTrailer = setTimeout(() => { presenceTrailer = null; sendPresence(); },
        PRESENCE_MIN_MS - (now - lastPresenceAt));
    }
    return; // the trailing send will carry the latest lastPresence
  }
  lastPresenceAt = now;
  try { tp.send({ t: 'presence', anchor: s.anchor, focus: s.focus }); } catch {}
}
setInterval(() => sendPresence(), 20000);                                   // heartbeat
setInterval(() => {
  presence.prune(Date.now());                       // drop vanished presence
  const live = presence.peers;                      // and their stale advertised heads:
  for (const n of [...peerHeads.keys()]) {           // a gone peer must not linger as "syncing"
    if (n !== NAME && n !== '#hub' && !live.has(n)) peerHeads.delete(n);
  }
  presenceTick();
  renderConv();                                     // refresh the badge (a peer may have dropped out)
}, 10000);

// ---- presence rendering: PM decorations + the chip bar ---------------------
function caretElt(p) {
  const bar = document.createElement('span');
  bar.className = 'pcaret'; bar.style.borderColor = p.color;
  const flag = document.createElement('span');
  flag.className = 'pflag'; flag.style.background = p.color; flag.textContent = displayOf(p.name);
  bar.appendChild(flag);
  return bar;
}

const presencePlugin = new Plugin({
  props: {
    decorations(state) {
      const flat = flatFromDoc(state.doc);
      const len = flat.length;
      const decos = [];
      for (const p of presence.list()) {
        const [lo, hi] = presenceSpan(p);
        const a = Math.min(lo, len), b = Math.min(hi, len);
        if (b > a) decos.push(Decoration.inline(flatToPm(a, flat), flatToPm(b, flat),
          { style: `background: color-mix(in srgb, ${p.color} 25%, transparent)` }));
        decos.push(Decoration.widget(flatToPm(Math.min(p.focus ?? 0, len), flat),
          () => caretElt(p), { key: `caret-${p.name}` }));
      }
      return DecorationSet.create(state.doc, decos);
    },
  },
});

/** Nudge the view so decorations recompute, and refresh the chip bar AND the
 *  roster (its live/dark dots read presence, so they must update when presence
 *  moves, not only when the head changes). */
function presenceTick() {
  renderPresenceBar();
  renderRoster();
  try { view.dispatch(view.state.tr.setMeta('remote', true)); } catch {}
}

function renderPresenceBar() {
  $('presenceBar').innerHTML = presence.list().map((p) => {
    const [lo, hi] = presenceSpan(p);
    const where = lo === hi ? `@${lo}` : `${lo}-${hi}`;
    return `<span class="ptag" style="border-color:${p.color}"><span class="pdot" style="background:${p.color}"></span>${esc(displayOf(p.name))} ${where}</span>`;
  }).join('');
}

// ---- the editor view --------------------------------------------------------
/** All transactions funnel here. Local doc changes are diffed into ops and
 *  committed (ONE batched commit per gesture), then reconciled against
 *  read(). Remote-flagged transactions are display-only. */
function dispatch(tr) {
  let newState = view.state.apply(tr);
  if (!tr.getMeta('remote') && tr.docChanged) {
    const neu = flatFromDoc(newState.doc);
    const ops = textEditOps(lastIds, lastText, neu, mint);
    pending.push(...ops);   // DEBOUNCED: buffer the ops, commit on flush
    scheduleFlush();
    refreshCache();
    const target = pmDocFromRead(); // speculative read() wins on mark boundaries
    if (!newState.doc.eq(target)) {
      const sel = selFlat(newState);
      let fix = newState.tr.replaceWith(0, newState.doc.content.size, target.content).setMeta('remote', true);
      fix = setFlatSel(fix, sel.anchor, sel.focus);
      newState = newState.apply(fix);
    }
    view.updateState(newState);
    renderConv(); // announce happens at flush, not per keystroke
  } else {
    view.updateState(newState);
  }
  const s = selFlat(newState);
  if (s.anchor !== lastPresence.anchor || s.focus !== lastPresence.focus) sendPresence(s);
  refreshToolbar(); // active-mark states follow the caret/selection
}

/** A remote delta was absorbed (already MERGED automatically): swap in the
 *  new doc, carrying my caret across the change by char ids. */
function onRemote() {
  const oldIds = lastIds;
  const sel = selFlat(view.state);
  refreshCache();
  const target = pmDocFromRead();
  let tr = view.state.tr.replaceWith(0, view.state.doc.content.size, target.content).setMeta('remote', true);
  tr = setFlatSel(tr, mapOffset(oldIds, lastIds, sel.anchor), mapOffset(oldIds, lastIds, sel.focus));
  view.dispatch(tr);
  renderConv();
  refreshToolbar();
}

// ---- formatting: toggle a mark / link / comment on the selection -----------
/** Commit format ops as ONE batch, rebuild from read(), restore selection.
 *  Flushes the typing buffer first so the run precedes the mark in the DAG. */
function applyFormatOps(ops, sel) {
  if (!ops.length) return;
  flush();
  commitOps(node, ops);
  refreshCache();
  const st = view.state;
  const target = pmDocFromRead();
  let tr = st.tr.replaceWith(0, st.doc.content.size, target.content).setMeta('remote', true);
  tr = setFlatSel(tr, sel.anchor, sel.focus);
  view.dispatch(tr);
  view.focus();
  net.announce();
  renderConv();
  refreshToolbar();
}

/** Light up the toolbar buttons whose mark covers the current selection (or,
 *  for a bare cursor, the character to its left). Read-only; runs on every
 *  transaction and selection move. Null-safe on buttons not yet present. */
function refreshToolbar() {
  if (!view) return;
  const s = selFlat(view.state);
  const from = Math.min(s.anchor, s.focus), to = Math.max(s.anchor, s.focus);
  const lo = to > from ? from : Math.max(0, from - 1);
  const hi = to > from ? to : from;
  const doc = curDoc();
  const has = (mtype) => hi > lo && selectionHas(doc, lo, hi, mtype);
  for (const [id, mtype] of [['boldBtn', 'bold'], ['italicBtn', 'italic'], ['underBtn', 'underline'],
    ['strikeBtn', 'strike'], ['linkBtn', 'link']]) {
    $(id)?.classList.toggle('is-active', has(mtype));
  }
  $('commentBtn')?.classList.toggle('is-active', hi > lo && coveringMarkTypes(doc, lo, hi, 'comment:').length > 0);
}

/** The current selection as {sel, from, to}, or null if collapsed. */
function selRange() {
  const sel = selFlat(view.state);
  const from = Math.min(sel.anchor, sel.focus), to = Math.max(sel.anchor, sel.focus);
  return to <= from ? null : { sel, from, to };
}

function applyMark(mtype) {
  const r = selRange(); if (!r) return;
  const remove = selectionHas(curDoc(), r.from, r.to, mtype); // fully set -> toggle off
  applyFormatOps(formatOps(lastIds, r.from, r.to, mtype, mint, { remove }), r.sel);
}

/** Link: toggle off if the selection is linked, else ask for a URL (inline
 *  input, never window.prompt). Links use the NON-GROWING gravity. */
function applyLink() {
  const r = selRange(); if (!r) return;
  if (selectionHas(curDoc(), r.from, r.to, 'link')) {
    applyFormatOps(formatOps(lastIds, r.from, r.to, 'link', mint, { remove: true }), r.sel);
  } else {
    openArgbar('link', 'URL for the selection', r);
  }
}

/** Comment: if comments fully cover the selection, remove each over its WHOLE
 *  span; else ask for the note. One comment = one `comment:<id>` mtype (note
 *  in value), so overlapping comments coexist. Non-growing gravity. */
function applyComment() {
  const r = selRange(); if (!r) return;
  const doc = curDoc();
  const covering = coveringMarkTypes(doc, r.from, r.to, 'comment:');
  if (covering.length) {
    const ops = covering.flatMap((mt) => {
      const [lo, hi] = markSpan(doc, mt);
      return formatOps(lastIds, lo, hi, mt, mint, { remove: true });
    });
    applyFormatOps(ops, r.sel); // one batch removes them all
  } else {
    openArgbar('comment', 'Comment on the selection', r);
  }
}

// the inline argument bar (URL / comment text)
let pendingArg = null;
function openArgbar(kind, label, r) {
  pendingArg = { kind, r };
  $('argLabel').textContent = label;
  $('argbar').classList.add('show');
  const inp = $('argInput'); inp.value = ''; inp.focus();
}
function closeArgbar() {
  pendingArg = null;
  $('argbar').classList.remove('show');
  view.focus();
}
function applyArgbar() {
  if (!pendingArg) return closeArgbar();
  const { kind, r } = pendingArg;
  let text = $('argInput').value.trim();
  if (text) {
    if (kind === 'link') {
      // bare "example.org" becomes a real URL (the renderer only links http(s))
      if (!/^[a-z][a-z0-9+.-]*:/i.test(text)) text = 'https://' + text;
      applyFormatOps(formatOps(lastIds, r.from, r.to, 'link', mint,
        { value: text, endSide: 'before' }), r.sel);
    } else {
      applyFormatOps(formatOps(lastIds, r.from, r.to, `comment:${mint()}`, mint,
        { value: text, endSide: 'before' }), r.sel);
    }
  }
  closeArgbar();
}
$('argApply').addEventListener('click', applyArgbar);
$('argCancel').addEventListener('click', closeArgbar);
$('argInput').addEventListener('keydown', (e) => {
  if (e.key === 'Enter') { e.preventDefault(); applyArgbar(); }
  if (e.key === 'Escape') { e.preventDefault(); closeArgbar(); }
});

// mousedown preventDefault keeps focus (and the selection) in the editor
for (const [id, fn] of [
  ['boldBtn', () => applyMark('bold')], ['italicBtn', () => applyMark('italic')],
  ['underBtn', () => applyMark('underline')], ['linkBtn', applyLink], ['commentBtn', applyComment],
]) {
  $(id).addEventListener('mousedown', (e) => e.preventDefault());
  $(id).addEventListener('click', fn);
}

// ---- merge policy: auto (live co-editing) vs manual (git-style fetch/merge) --
$('modeBtn').addEventListener('click', () => {
  flush(); // my typing run is committed before any policy change merges
  net.setManual(!net.manual); // leaving manual drains the staged backlog
  $('modeBtn').textContent = net.manual ? 'merge: manual' : 'merge: auto';
  renderConv();
});
$('mergeBtn').addEventListener('click', () => { flush(); net.mergeStaged(); renderConv(); });

/** The live comment chips: every comment:<id> in the doc with its note + span. */
function renderComments() {
  const doc = curDoc();
  const seen = new Map(); // mtype -> {value, lo, hi}
  for (let i = 0; i < doc.length; i++) {
    for (const m of doc[i].marks) {
      if (!m.mtype.startsWith('comment:')) continue;
      const c = seen.get(m.mtype);
      if (c) c.hi = i + 1; else seen.set(m.mtype, { value: m.value, lo: i, hi: i + 1 });
    }
  }
  $('commentsBar').innerHTML = [...seen.entries()].map(([mt, c]) =>
    `<span class="ptag ctag" title="${esc(mt)}">💬 ${esc(c.value ?? '')} <span class="cwhere">${c.lo}-${c.hi}</span></span>`
  ).join('');
}

refreshCache();
const view = new EditorView($('editor'), {
  state: EditorState.create({
    doc: pmDocFromRead(),
    plugins: [
      keymap({
        'Mod-b': () => { applyMark('bold'); return true; },
        'Mod-i': () => { applyMark('italic'); return true; },
        'Mod-u': () => { applyMark('underline'); return true; },
        'Mod-k': () => { applyLink(); return true; },
      }),
      keymap(baseKeymap),
      presencePlugin,
    ],
  }),
  dispatchTransaction: dispatch,
});
view.dom.addEventListener('blur', flush); // leaving the editor seals the run
// contentEditable swallows plain clicks on links; Cmd/Ctrl+Click opens them
view.dom.addEventListener('click', (e) => {
  const a = e.target.closest ? e.target.closest('a.plink') : null;
  if (a && a.href && (e.metaKey || e.ctrlKey)) {
    e.preventDefault();
    window.open(a.href, '_blank', 'noopener');
  }
});

// ---- metadata cost + certified GC ------------------------------------------
// The COST PANEL shows what the doc drags around beyond its visible text:
// tombstones, mark records, coordinate symbols, encoded-state bytes, commit
// count, wire-summary size. The GC button runs the CERTIFIED compactStable
// (marks-layer GC #110): it fires only when the stability cut is complete
// (evidence from every registered peer), preserves reads, and advances the
// epoch. Epochs are linearized: after one peer compacts, others' merges are
// deferred until they GC too (the button turns into the barrier).
// the SAVE cost (run-table serializer, task #104) is computed per HEAD, not
// per keystroke: the encode is the real serializer, cheap at demo scale but
// not free, and the head only moves on flush/merge/GC
let saveCache = { gid: null, bytes: 0 };
function saveBytesCached() {
  const g = node.headGid;
  if (saveCache.gid !== g) saveCache = { gid: g, bytes: node.saveBytes() };
  return saveCache.bytes;
}

function renderStats() {
  const st = node.head.state;
  const chars = node.read().length;
  const sc = node.stableCut();
  // [label, value, hover explanation] -- the third entry becomes a native
  // title tooltip, so each chip says what it counts and why it matters
  const chips = [
    ['chars', chars,
      'Visible characters in the document. Everything else on this row is overhead the doc carries beyond this.'],
    ['tombstones', st.text.deleted.size,
      'Deleted characters still remembered as markers. Concurrent edits need them (an insert next to a deleted char still has an anchor). Certified GC removes the settled ones.'],
    ['mark records', st.marks.size,
      'Formatting records (bold, links, comments): each carries its range and a timestamp for conflict resolution. GC drops the ones fully overwritten or unmarked.'],
    ['coord symbols', node.symbolCount(),
      'Position-identifier building blocks across all characters, live and deleted. Each char’s identity is a path; this counts the path pieces. The main thing GC shrinks.'],
    ['in-memory bytes', node.snapshotBytes(),
      'Size of the whole document state as kept in memory right now (encoded form). Falls after GC re-codes coordinates.'],
    ['save bytes (run table)', saveBytesCached(),
      'What the document costs on disk or wire using the run-table serializer: consecutive typing compresses into runs. The honest durable size (roughly 1-2 bytes per char after GC).'],
    ['commits', node.dag.size,
      'Version-history entries held locally (like git commits: one per typing run, merge, or GC). History pruning forgets settled ones, keeping recent commits only.'],
    ['wire summary', node.ancestryGids().size,
      'Commit ids advertised when syncing, so peers can compute exactly what to send. Shrinks with history pruning.'],
    ['epoch', node.epoch,
      'How many certified GC compactions this document has been through. Peers must reach the same epoch before merging (they fast-forward onto the compacted chain).'],
    ['stable cut', sc.complete ? `${sc.meet.size} settled` : `waiting: ${sc.missing.join(',') || '?'}`,
      'Operations every known peer has provably seen: these can never conflict again, so GC may forget their bookkeeping. “waiting: X” means peer X has not been heard from since the cut, so GC refuses.'],
    ['local store', store ? (restoredCommits ? `restored ${restoredCommits}` : 'on') : 'off',
      'IndexedDB copy in this browser: the doc survives tab close and reload, and opens offline. “restored N” = commits loaded from it on startup.'],
  ];
  $('statsRow').innerHTML = chips.map(([k, v, tip]) =>
    `<span class="stat" title="${tip}"><span class="sk">${k}</span> ${v}</span>`).join('');
  $('gcBtn').disabled = !sc.complete || sc.meet.size === 0;
}

function runCertifiedGc(label) {
  flush(); // seal my typing run first
  // NEVER compact while diverged: a compaction opens a new epoch, and two peers
  // on different epochs cannot merge (the runtime linearizes epochs). Compact
  // only when the room agrees on a head, so followers fast-forward.
  if (!convergedWithPeers()) {
    const st = $('gcStatus'); st.className = 'status warnc';
    st.textContent = `${label || 'GC'} deferred: syncing with peers first (compacting while diverged would split epochs).`;
    return false;
  }
  const b = { syms: node.symbolCount(), bytes: node.snapshotBytes(), tomb: node.head.state.text.deleted.size, marks: node.head.state.marks.size };
  const r = node.compactStable();
  const st = $('gcStatus');
  if (!r.compacted) {
    st.className = 'status warnc';
    st.textContent = `${label} refused: ${r.reason ?? JSON.stringify(r.missing ?? r)}`;
  } else {
    st.className = 'status good';
    st.textContent = `${label} compacted (epoch ${node.epoch}): ${b.syms}→${node.symbolCount()} symbols, `
      + `${b.bytes}→${node.snapshotBytes()} bytes, ${b.tomb}→${node.head.state.text.deleted.size} tombstones, `
      + `${b.marks}→${node.head.state.marks.size} mark records. Reads preserved.`;
  }
  renderConv();
  net.announce();
  return r.compacted;
}
$('gcBtn').addEventListener('click', () => runCertifiedGc(''));

// DOWNLOAD the doc as a .saldoc bundle: the WHOLE commit DAG (records +
// heads, wire SHAs) as plain JSON -- the same shape every durable backend
// uses. scripts/bundle2git.mjs turns it into a pushable git repo; load()
// of that repo rejoins live sync with identical SHAs. Full history: deleted
// text and authorship ride along (say so in the UI title).
$('dlBtn').addEventListener('click', () => {
  flush(); // seal the typing run so the bundle carries it
  const bundle = { v: 1, doc: ROOM, datatype: 'peritext', ...nodeRecords(node, { datatypeLabel: 'peritext' }) };
  const blob = new Blob([JSON.stringify(bundle)], { type: 'application/json' });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = `${ROOM}.saldoc.json`;
  a.click();
  URL.revokeObjectURL(a.href);
  const st = $('gcStatus');
  st.className = 'status good';
  st.textContent = `downloaded ${ROOM}.saldoc.json (${bundle.records.length} commits). `
    + `To git: node scripts/bundle2git.mjs ~/Downloads/${ROOM}.saldoc.json --repo <path>`;
});

// OPEN (restore/import) a .saldoc bundle into THIS room: ingest through the
// content-address gate (tamper-proof, SHA-dedup idempotent), then merge.
// Same lineage fast-forwards; a different doc merges as a CRDT union.
$('openBtn').addEventListener('click', () => $('openFile').click());
$('openFile').addEventListener('change', async () => {
  const st = $('gcStatus');
  const f = $('openFile').files[0];
  $('openFile').value = '';
  if (!f) return;
  try {
    const bundle = JSON.parse(await f.text());
    if (bundle.v !== 1 || !Array.isArray(bundle.records) || !bundle.heads) throw new Error('not a v1 .saldoc bundle');
    if (bundle.datatype !== 'peritext') throw new Error(`bundle datatype is ${bundle.datatype}; this editor is peritext`);
    flush();
    const added = node.ingest(wireFromRecords(bundle.records));
    node.mergeWithGid(bundle.heads.head);
    onRemote(); // rebuild the view from the merged read, caret carried by ids
    net.announce();
    st.className = 'status good';
    st.textContent = `imported ${f.name}: ${added} new commits (${bundle.records.length} in bundle), head ${short(node.headGid)}`;
  } catch (e) {
    st.className = 'status warnc';
    st.textContent = `import failed: ${e.message}`;
  }
});

// CONVERGED = every LIVE peer shares my head (solo => true). The gate for all
// compaction: two peers that compact while diverged land on different epochs,
// so we compact only when the room agrees. Quantify over LIVE peers (in
// presence), NOT the accumulated peerHeads: a peer that left without a clean
// leave lingers in peerHeads with a STALE head, and it cannot diverge from us
// anymore (it re-bootstraps on return), so it must not block the GC. A live
// peer whose head we have not learned yet counts as not-converged (conservative
// -- wait until we know it).
function livePeers() { return [...presence.peers.keys()].filter((n) => n !== NAME && n !== '#hub'); }
function convergedWithPeers() {
  for (const n of livePeers()) if (peerHeads.get(n) !== node.headGid) return false;
  return true;
}

// AUTO-GC: the leader fires the certified compaction when the coordinate
// cost crosses the policy threshold (src/autogc.js; the leader guard keeps
// epochs linear -- followers reach the new epoch by fast-forward). Checked
// on a slow tick; one attempt per head (a refusal is not retried until the
// head moves). Gated on convergence: never compact while diverged.
let autoGcTried = null;
// fire only on real growth past the last outcome; seeded with the LOADED
// state so a restored doc is its own baseline (no spurious boot attempt)
let autoGcFloor = node.symbolCount();
setInterval(() => {
  if (node.headGid === autoGcTried) return;
  if (!convergedWithPeers()) return; // wait until the room agrees on a head
  const sc = node.stableCut();
  if (!shouldCompact({
    symbols: node.symbolCount(),
    visibleChars: node.read().length,
    cutComplete: sc.complete,
    meetSize: sc.meet.size,
    name: NAME,
    roster: node.registered,
    floorSymbols: autoGcFloor,
  })) return;
  autoGcTried = node.headGid;
  runCertifiedGc('auto-GC:');
  autoGcFloor = node.symbolCount();
}, 5000);

// EPOCH-BASE PRUNING (the answer to "why keep full history?"): once a
// compaction SETTLES -- the cut is complete and every author's evidence has
// reached the compact epoch -- history below the compact commit can never be
// needed again (no delta, no LCA), so drop it. The compact commit becomes a
// parent-free epoch base whose content id still verifies, fresh peers
// bootstrap from it at O(document), and the local store forgets the same
// records. pruneToEpochBase carries the gate; a refusal is just "not yet".
// NOT inside runCertifiedGc: right after compacting, the compactor's own
// evidence is still below the new epoch, so the gate opens only after the
// next authored run. One attempt per head, on the same slow cadence.
let pruneTried = null;
setInterval(() => {
  if (typeof node.pruneToEpochBase !== 'function') return; // defensive
  if (node.epoch === 0 || node.headGid === pruneTried) return;
  pruneTried = node.headGid;
  const pr = node.pruneToEpochBase();
  if (!pr.pruned) return;
  const st = $('gcStatus');
  st.className = 'status good';
  st.textContent = `history pruned: ${pr.pruned} commits below epoch ${pr.epoch} forgotten (${node.dag.size} kept)`;
  renderStats();
  if (store) {
    store.persistNode(ROOM, node, { pruneStored: true }) // drop the same records from IndexedDB
      .catch((e) => console.warn('[idb] prune persist failed:', e?.message ?? e));
  }
}, 5000);

// THE ROSTER, with LIVENESS + a forget control. A registered peer that is not
// currently in presence is DARK (grey dot). A dark peer that authored pins the
// certified GC's horizon at its last-synced position (a departed writer stays
// registered conservatively), so it gets a ✕: forgetting it drops it from the
// roster (node.forget) and lets the horizon advance. The tradeoff is on the
// tooltip -- a forgotten peer that returns re-syncs fresh from the current
// version and loses edits it made offline and never shared.
function renderRoster() {
  enforceForgotten(); // keep forgotten peers out of the roster across re-registration
  const el = $('peers');
  const roster = [...node.registered].sort();
  if (!roster.length) { el.textContent = ''; return; }
  const live = new Set(presence.peers.keys());
  // show the HUMAN name; when two sessions share one (e.g. two tabs both
  // "kc-laptop") disambiguate with the session tag so the roster is honest
  const counts = {};
  for (const n of roster) { const d = displayOf(n); counts[d] = (counts[d] || 0) + 1; }
  const label = (n) => counts[displayOf(n)] > 1 ? `${displayOf(n)}·${n.split('~')[1] ?? '?'}` : displayOf(n);
  const tail = ` · head ${short(node.headGid)}${pending.length ? ` · ${pending.length} pending` : ''}`;
  el.innerHTML = 'peers: ' + roster.map((n) => {
    const lab = esc(label(n));
    if (n === NAME) return `<span class="pchip"><span class="pdot on"></span>${lab} (you)</span>`;
    if (live.has(n)) return `<span class="pchip"><span class="pdot on"></span>${lab}</span>`;
    const tip = `forget ${esc(displayOf(n))}: this peer looks offline and pins the certified GC's `
      + `horizon at its last-synced position. Forgetting it lets GC advance; if it `
      + `returns it re-syncs fresh from the current version and loses any `
      + `edits it made offline and never shared.`;
    return `<span class="pchip"><span class="pdot"></span>${lab}`
      + `<button class="forget" data-peer="${esc(n)}" title="${tip}">✕ forget</button></span>`;
  }).join(' ') + tail;
  // NUDGE: a peer you forgot is live again -> offer to un-forget (a forgotten
  // peer that stays gone shows nothing; only a returning one nudges).
  const back = [...forgotten].filter((n) => presence.peers.has(n));
  if (back.length) {
    el.innerHTML += '<div class="forgot-back">' + back.map((n) =>
      `↩ ${esc(displayOf(n))} is back · <button class="unforget" data-peer="${esc(n)}">un-forget</button>`).join(' &nbsp; ') + '</div>';
  }
  for (const b of el.querySelectorAll('.forget')) b.addEventListener('click', () => forgetPeer(b.getAttribute('data-peer')));
  for (const b of el.querySelectorAll('.unforget')) b.addEventListener('click', () => unforget(b.getAttribute('data-peer')));
}
function forgetPeer(name) {
  // refuse to forget a LIVE peer: forget is for peers that have left. Forgetting
  // an active peer while GC advances past it is the unsound case (it should
  // stay, or re-bootstrap on return).
  if (presence.peers.has(name)) {
    const st = $('gcStatus'); st.className = 'status warnc';
    st.textContent = `${displayOf(name)} is live right now; forget is for peers that have left.`;
    return;
  }
  forgotten.add(name); saveForgotten(); // remembered on this device across reloads/reconnects
  node.forget(name);
  const st = $('gcStatus'); st.className = 'status good';
  st.textContent = `forgot ${displayOf(name)} (remembered on this device); the GC horizon can advance past it.`;
  const sc = node.stableCut();
  if (sc.complete && sc.meet.size) runCertifiedGc('after forget:');
  else renderConv();
  net.announce();
}
function unforget(name) {
  forgotten.delete(name); saveForgotten();
  node.register(name);
  const st = $('gcStatus'); st.className = 'status good';
  st.textContent = `un-forgot ${displayOf(name)}: back in the roster.`;
  renderConv();
}

// ---- convergence badge -----------------------------------------------------
function renderConv() {
  const mine = node.headGid;
  const others = livePeers(); // only LIVE peers count -- gone peers left stale heads
  const badge = $('convBadge');
  if (others.length === 0) { badge.className = 'conv no'; badge.textContent = 'solo'; }
  else {
    const agree = others.filter((n) => peerHeads.get(n) === mine).length;
    if (agree === others.length) { badge.className = 'conv yes'; badge.textContent = `✓ converged (${others.length})`; }
    else { badge.className = 'conv no'; badge.textContent = `syncing ${agree}/${others.length}`; }
  }
  renderRoster();
  // manual-merge affordances: the merge button appears with the staged count
  const mb = $('mergeBtn');
  mb.style.display = net.manual ? '' : 'none';
  if (net.manual) mb.textContent = `merge ⤵ ${net.staged.size}`;
  renderComments(); // doc-derived, kept in step with every state change
  renderStats();
  persistIfChanged(); // durable store follows every head change (gid-guarded)
}

renderConv();
refreshToolbar();
