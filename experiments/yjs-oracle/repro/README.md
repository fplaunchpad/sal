# Plain-Yjs reproductions

One self-contained script per defect class, importing only `yjs`. Each
prints the observed and the expected document and exits non-zero when the
defect shows. `run-all.mjs` runs the seven and reports which reproduce on
the installed version. `v14/` holds the same scripts against the v14
release candidate, published as `@y/y`, whose text type is `doc.get(name)`
and whose delta is a node tree; the scripts differ only in those two calls.

    npm install && node run-all.mjs
    cd v14 && npm install && node run-all.mjs

Expected documents are hand-derived from the sequential specification in
`../SPEC.md`: Y-001 to Y-005 give the document both orders of the two
concurrent operations produce; Y-006 gives the result of the list edit;
Y-007 lists the three causally closed states and the script fails when the
replica shows none of them.
`skip-plain.mjs` is the plain-text form of the same condition on the v14
candidate, whose store fills a client's clock gap with a `Skip` and
integrates the struct behind it when its origins exist; 13.x holds the
struct pending.

| Class | 13.6.31 | 13.6.33 | 14.0.0-rc.29 |
|---|---|---|---|
| Y-001 marker ownership | reproduces | reproduces | reproduces |
| Y-002 opener judged redundant | reproduces | reproduces | reproduces |
| Y-003 delete removes neighbour's closer | reproduces | reproduces | reproduces |
| Y-004 boundary spread | reproduces | reproduces | reproduces |
| Y-005 overlapping same key | reproduces | reproduces | reproduces |
| Y-006 opened document | reproduces | reproduces | does not reproduce |
| Y-007 delete set before its predecessor | reproduces | reproduces | reproduces |
| Y-008 struct past a same-client clock gap (`skip-plain.mjs`, plain text) | does not reproduce | does not reproduce | reproduces |

Measured on Node 26.3.1 on 2026-10-29.

Posted upstream on 2026-10-29: Y-001 to Y-003 as yjs/yjs#828, Y-005 as a
comment on #382, Y-004 as a comment on #385, Y-007 and Y-008 as yjs/yjs#829.
`upstream-drafts.md` holds the posted texts.
