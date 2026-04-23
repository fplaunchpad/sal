# Sal CRDT playgrounds

Interactive playgrounds for the CRDTs verified in the [Sal framework](../). Each CRDT runs on three in-browser replicas; you apply local ops, merge any pair explicitly, and watch the abstract value converge. Toggle **Show concrete state** to see the lattice representation that makes merge associative/commutative/idempotent.

Currently shipped: Increment-Only Counter, PN-Counter, OR-Set. The remaining 15 CRDTs are a mechanical application of the same pattern — see [`../.claude/plans/composed-strolling-mist.md`](../.claude/plans/composed-strolling-mist.md) for the phased rollout.

## Local development

```sh
cd demos
npm install
npm run dev         # Vite dev server, typically on :5173
npm run test        # fast-check lattice-law invariants, ~300 ms
npm run build       # TS typecheck + production bundle → dist/
```

## Architecture

Each CRDT lives in `src/crdts/<name>.tsx` and exports a `CRDTSpec<Concrete, Abstract, Op>` with:

- `init`, `apply(s, op, meta)`, `merge(a, b)`, `abstract(s)` — the semantics.
- `renderAbstract`, `renderConcrete`, `opForm` — the UI pieces.

The shared `harness/Playground.tsx` manages replica state, merge selection, and the abstract/concrete toggle. Invariants tests in `src/crdts/__tests__/` use [fast-check](https://fast-check.dev/) to property-check idempotence, commutativity, associativity, and strong convergence of `merge` (500 cases × 4 properties per CRDT).

The CRDT modules are hand-ported from the Lean specs under [`../Sal/CRDTs/`](../Sal/CRDTs); see [`../docs/porting-op-based-crdts.md`](../docs/porting-op-based-crdts.md) for the translation recipe.

## Deployment

[`.github/workflows/demos-deploy.yml`](../.github/workflows/demos-deploy.yml) builds and deploys to GitHub Pages on every push to `main` that touches `demos/**`. The Pages setting must be manually switched to **Source: GitHub Actions** in the repo settings before the first deploy will succeed.
