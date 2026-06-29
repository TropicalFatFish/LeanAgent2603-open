# LeanAgent2603 Open Proof Pack

This package is a sanitized Lean 4 proof pack extracted from LeanAgent2603.
It contains final proof files only: no model logs, prompts, temporary caches,
DWQ/SLURM output, private absolute paths, old audit JSON, or API credentials.

## Contents

- `proofs/MiniF2F/`: 197 solved MiniF2F Test proofs out of 244 Test files.
- `proofs/FormalMATH-Lite/`: 222 solved FormalMATH-Lite proofs out of 424 reconstructed theorem files.
- `MANIFEST.json`: package-level counts, SHA-256 hashes, and static audit results.
- `proofs/*/MANIFEST.json`: dataset-level proof file manifests.
- `scripts/verify_proofs.py`: static checks plus optional Lean compilation.

Each proof file contains its theorem statement and proof. Comments and metadata
headers were stripped. Some FormalMATH-Lite proofs keep top-level auxiliary
definitions because their theorem statements or proofs depend on them.

All 222 local FormalMATH-Lite proof files are included in `proofs/` and are
checked by the verifier.

## Verification

Install Lean using `elan`, then from this directory run:

```bash
lake exe cache get
python3 scripts/verify_proofs.py --jobs 8
```

The verifier checks that every proof file has exactly one theorem, contains no
`sorry`, `admit`, `axiom`, or `unsafe`, contains no comment markers, and then
runs `lake env lean` on each file.

For verification from the original LeanAgent2603 checkout without downloading
dependencies again, run:

```bash
python3 dist/LeanAgent2603-open-20260629/scripts/verify_proofs.py \
  --root dist/LeanAgent2603-open-20260629 \
  --lake-root . \
  --jobs 8
```

## Provenance

- MiniF2F statements: local `third_party/miniF2F-lean4` mirror of MiniF2F Lean 4.
- FormalMATH-Lite statements: reconstructed from FormalMATH-Lite data into one theorem file per item.
- Lean toolchain: `leanprover/lean4:v4.27.0-rc1`.
- Mathlib dependency: `leanprover-community/mathlib4` at `v4.27.0-rc1`.

## License Notes

This package uses Apache-2.0 as the release license for the packaging scripts
and newly collected proof files. Upstream theorem statements retain their
original licenses and notices. See `LICENSES/THIRD_PARTY.md`.
