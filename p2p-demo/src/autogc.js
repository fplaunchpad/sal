// AUTO-GC POLICY (pure, headless-testable): when should a peer fire the
// certified compactStable on its own? Fires only when
//   - the stability cut is COMPLETE with a nonempty meet (the theorem's
//     precondition; compactStable would refuse otherwise),
//   - the coordinate cost is worth reclaiming (symbols exceed a floor AND a
//     per-visible-char ratio; below that, compaction is a no-op refusal),
//   - this peer is the LEADER: the lexicographically least rostered name.
// The leader guard is what avoids the #97 trap: two peers auto-firing
// near-simultaneously would mint RIVAL same-epoch compact commits whose
// cross-epoch merge is the deferred protocol half. One deterministic firer
// per roster keeps epochs linear; everyone else reaches the new epoch by
// fast-forwarding onto the compacted chain (verified behavior).

export const AUTOGC_DEFAULTS = Object.freeze({ minSymbols: 4000, ratio: 32, growth: 1.5 });

export function shouldCompact({ symbols, visibleChars, cutComplete, meetSize, name, roster, floorSymbols = 0 }, opts = {}) {
  const { minSymbols, ratio, growth } = { ...AUTOGC_DEFAULTS, ...opts };
  if (!cutComplete || !(meetSize > 0)) return false;
  if (!(symbols > minSymbols)) return false;
  if (!(symbols > ratio * Math.max(1, visibleChars))) return false;
  // ADAPTIVE FLOOR: a pure typing chain's COMPACTED cost already exceeds any
  // fixed ratio (live depth is the intrinsic cost no GC may touch), so a
  // ratio test alone would re-fire forever against the floor. Require real
  // growth since the last attempt's outcome before trying again.
  if (!(symbols > growth * floorSymbols)) return false;
  const leader = [...roster].sort()[0];
  return name === leader;
}
