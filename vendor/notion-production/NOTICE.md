# Notion production editing code: not covered by this repository's licence

This directory holds code that belongs to Notion Labs, Inc.: 4,335 module
slices of the editing code shipped in Notion's web client, extracted
verbatim from 63 application assets pinned by URL and SHA-256 in
`sources.json`, together with the small loader (`index.mjs`, `runtime.mjs`,
`client.mjs`, `requests.mjs`) that runs them offline.

The MIT licence at the root of this repository does not apply to anything in
this directory. The authors hold no rights in Notion's code and grant none.
It is included for one purpose only: so that the measurements in
`docs/notion-production-text.md` and `docs/notion-production-blocks.md` can be
repeated against exactly the bytes they were made on. The authors use it for
no other purpose, and nothing here may be reused, modified or redistributed
on the strength of this repository's licence.

The export is produced by `experiments/notion-production-client/extract.mjs`
from the pinned assets; `ra-pbt/instances/notion-production-*/verify-sources.js`
checks the digests of these files before and after every run.
