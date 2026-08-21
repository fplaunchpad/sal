#!/usr/bin/env python3
"""Run-table PROJECTION for the save-size matrix (task #98, fair-play
column iii). Imports the exact bit accounting of
benchmarks/models/run_table_measure.py and runs its measure()
on the requested sequential traces; dumps machine-readable totals to
benchmarks/results/projection.json.

These are MEASURED-IN-MODEL numbers: the accounting model's bits over the
same trace and the same dense-Lamport id stream as the shipped runtime,
NOT a shipped serializer. Charged bits per the model: per-record run-id +
offset, per-entry headers (liveness, parent ref+offset, head delta,
length). NOT charged: the (ts, agent) tie-break, the text itself, any
framing. projected_save_bytes below = ceil(bits/8) + UTF-8 bytes of the
final text, so it can sit in the same table as real save files; the id
exclusion is stated wherever it is quoted.

Usage: python3 tools/run_table_projection.py [trace ...]
"""

import json
import math
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MODELS = os.path.abspath(os.path.join(HERE, "..", "models"))
TRACES_DIR = os.path.abspath(os.path.join(HERE, "..", "traces"))
sys.path.insert(0, MODELS)

import run_table_measure as RTM  # noqa: E402
import gzip  # noqa: E402

TRACES = sys.argv[1:] or [
    "friendsforever_flat", "clownschool_flat", "seph-blog1", "automerge-paper"]

out = {"model": "run_table_measure.py (task #73), family 1-sided",
       "note": "measured-in-model, not a shipped serializer; bits exclude "
               "(ts,agent) ids and text; projected_save_bytes = "
               "ceil(bits/8) + utf8(endContent)",
       "traces": {}}

rng = random.Random(2026)
for name in TRACES:
    path = os.path.join(TRACES_DIR, f"{name}.json.gz")
    with gzip.open(path, "rt", encoding="utf-8") as f:
        text_bytes = len(RTM.json.load(f)["endContent"].encode("utf-8"))
    res = RTM.measure(path, rng)
    m = res["rows"]["1-sided"]
    gates_ok = bool(m["g_order"][0] and m["g_order"][1] and m["end_ok"]
                    and m["cmp_gates"][0][0] == m["cmp_gates"][0][1]
                    and m["cmp_gates"][1][0] == m["cmp_gates"][1][1])
    chars = res["chars"]
    out["traces"][name] = {
        "chars": chars,
        "utf8_text_bytes": text_bytes,
        "gates_ok": gates_ok,
        "bits": {
            "chain_before": m["chain_before"],
            "chain_fused": m["chain_fused"],
            "run_table_raw": m["raw"]["total"],
            "run_table_composed": m["cmpd"]["total"],
        },
        "bits_per_char": {
            "chain_before": m["chain_before"] / chars,
            "chain_fused": m["chain_fused"] / chars,
            "run_table_raw": m["raw"]["total"] / chars,
            "run_table_composed": m["cmpd"]["total"] / chars,
        },
        "projected_save_bytes": {
            "chain_before": math.ceil(m["chain_before"] / 8) + text_bytes,
            "chain_fused": math.ceil(m["chain_fused"] / 8) + text_bytes,
            "run_table_raw": math.ceil(m["raw"]["total"] / 8) + text_bytes,
            "run_table_composed": math.ceil(m["cmpd"]["total"] / 8) + text_bytes,
        },
    }

dst = os.path.join(HERE, "..", "results", "projection.json")
os.makedirs(os.path.dirname(dst), exist_ok=True)
with open(dst, "w") as f:
    json.dump(out, f, indent=1)
print("\nwrote", os.path.relpath(dst, os.path.join(HERE, "..")))
for name, t in out["traces"].items():
    bpc = t["bits_per_char"]
    print(f"  {name}: chars={t['chars']} gates_ok={t['gates_ok']} "
          f"chain_before={bpc['chain_before']:.2f} b/ch "
          f"rt_composed={bpc['run_table_composed']:.2f} b/ch "
          f"-> {t['projected_save_bytes']['run_table_composed']} B projected")
