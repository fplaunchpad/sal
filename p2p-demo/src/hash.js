// Content addressing for the demo: a THIN RE-EXPORT of the runtime's core hash
// (task #108). The pure-JS SHA-256 and the canonical content-id derivation now
// live in the runtime (runtime/src/hash.js) so the WIRE (src/sync.js's Peer,
// the DistributedReplica) and the DISK (git persistence here) name the same
// commit the same way, with no FNV-vs-SHA seam. The demo imports the core hash
// rather than carrying its own; this file exists only so existing importers
// (and the SHA self-check test) keep resolving `./hash.js`.

export { sha256hex, stableStringify, contentId, commitContentId } from '../../runtime/src/hash.js';
