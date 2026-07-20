// Node: the p2p replica -- now a THIN ADAPTER over the runtime's first-class
// DistributedReplica (task #108).
//
// This file used to BE the fold: it glued sync.js's separate-store gossip
// (delta/ingest/mergeWithGid) to runtime.js's certified state GC (compactStable)
// under an ad-hoc SHA hash local to the demo, and was cross-checked against the
// FNV `Peer` because the two hashed differently. #108 folded that combination
// into the core as `runtime/src/replica.js` (`DistributedReplica`): ONE
// content-addressed store with BOTH wire sync AND certified compaction, SHA
// throughout, datatype-parametric. The demo now just re-uses it.
//
// `Node` is `DistributedReplica` with the demo's historical defaults (the embed
// RGA, name 'n0'). Everything the transport, git codec, and browser editor call
// -- commit / ancestryGids / delta / ingest / mergeWithGid / register /
// stableCut / compactStable / read / headGid / epoch / symbolCount -- is
// inherited unchanged, so gitstore.js, transport.js, and web/app.js keep
// working against the core object. The SHA content id and the epoch barrier now
// live in the core (src/hash.js, src/replica.js).

import { DistributedReplica } from '../../runtime/src/replica.js';
import { compactibleEmbedRGA } from '../../runtime/src/compact.js';

export class Node extends DistributedReplica {
  constructor(datatype = compactibleEmbedRGA, name = 'n0') {
    super(datatype, name);
  }
}
