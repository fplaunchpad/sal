# Runtime conformance fixtures

`fugue-conformance.json` records the reviewed outputs of the independent
full-policy Fugue model for the named sequential and merge anomaly cases. The
runtime test replays the operations through every maintained sided RGA
representation and compares its visible identifier order with this corpus.

The fixture was generated from the archived `js_sided_oracle.py` model before
the plain-MRDT repository cutover. Keeping the corpus here makes the release
gate deterministic and avoids a production dependency on historical Python
whiteboard code. Changes to the fixture require an explicit semantic review;
they must not be regenerated merely to make a failing implementation pass.
