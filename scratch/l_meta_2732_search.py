#!/usr/bin/env python3
"""L-meta-2732: search Monotone2 fan-in-2 circuit with <=26 gates for Heawood edge-OR.

Reuses row-reduced SAT from pequalnp-582 (58 constraints on 2^14 inputs).
Shard layout matches heawood_sat_shard: 54 skeleton patterns from 27-gate cover
minus one gate, split across nshards.

Usage:
  python3 l_meta_2732_search.py <shard> <nshards>

Witness: writes /tmp/heawood/circuit26_L2732_shard<N>.json
No witness in shard: prints 'shard done, no circuit' and exits 0.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

# vendored path for agent runs inside pequalnp-proofs
_SCRATCH582 = Path(__file__).resolve().parents[1].parent / "pequalnp-582" / "scratch"
if _SCRATCH582.is_dir():
    sys.path.insert(0, str(_SCRATCH582))
else:
    sys.path.insert(0, "/agent/pequalnp-582/scratch")

from heawood_sat import cover_ops, solve_skeleton  # noqa: E402
from heawood_sat_shard import patterns  # noqa: E402


def main() -> None:
    shard = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    nshards = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    allp = list(patterns())
    print(f"L-meta-2732 total patterns {len(allp)} shard {shard}/{nshards}", flush=True)
    for i, (del_i, ops) in enumerate(allp):
        if i % nshards != shard:
            continue
        print(f"[{i}] del@{del_i} len={len(ops)} first={ops[:3]}", flush=True)
        t0 = time.time()
        circ = solve_skeleton(ops)
        dt = time.time() - t0
        if circ:
            out = Path(f"/tmp/heawood/circuit26_L2732_shard{shard}.json")
            out.write_text(json.dumps(circ))
            print(f"FOUND del@{del_i} time={dt:.1f}s", circ, flush=True)
            return
        print(f"  unsat del@{del_i} time={dt:.1f}s", flush=True)
    print("shard done, no circuit", flush=True)


if __name__ == "__main__":
    main()