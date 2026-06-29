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

## Quick Start

Install Lean using `elan`, clone this repository, then fetch Mathlib cache and
verify the proof pack:

```bash
git clone https://github.com/TropicalFatFish/LeanAgent2603-open.git
cd LeanAgent2603-open
lake exe cache get
python3 scripts/verify_proofs.py --jobs 8
```

The verifier checks that every proof file has exactly one theorem, contains no
`sorry`, `admit`, `axiom`, or `unsafe`, contains no comment markers, and then
runs `lake env lean` on each file.

To check one proof file directly:

```bash
lake env lean proofs/FormalMATH-Lite/formalmath_0351_omni_theorem_3620.lean
```

For verification from the original LeanAgent2603 checkout without downloading
dependencies again, run:

```bash
python3 dist/LeanAgent2603-open-20260629/scripts/verify_proofs.py \
  --root dist/LeanAgent2603-open-20260629 \
  --lake-root . \
  --jobs 8
```

## Using The Proofs

Every proof file is standalone and starts from `import Mathlib`. You can read
the files as a proof corpus, copy individual files into another Lean 4 project
that uses the same toolchain, or run `lake env lean <file>` to check a proof.

For proof search, repair, or agent workflows, install the optional Lean MCP
tooling:

```bash
git clone https://github.com/optsuite/lean-tools-mcp.git
cd lean-tools-mcp
pip install -e ".[sse,dev]"
lean-tools-mcp --project-root <path-to-this-repo>
```

`lean-tools-mcp` provides Lean goal inspection, diagnostics, local declaration
search, Mathlib search, and tactic trials through MCP. It is optional for
verifying this proof pack; it is useful when extending or repairing proofs.

For local model-assisted proof repair experiments, a practical starting model
is `Qwen/Qwen3.5-9B`:

- Model card: https://huggingface.co/Qwen/Qwen3.5-9B
- Example local serving command with vLLM: `vllm serve "Qwen/Qwen3.5-9B"`

## Provenance

- MiniF2F statements: local `third_party/miniF2F-lean4` mirror of MiniF2F Lean 4.
- FormalMATH-Lite statements: reconstructed from FormalMATH-Lite data into one theorem file per item.
- Lean toolchain: `leanprover/lean4:v4.27.0-rc1`.
- Mathlib dependency: `leanprover-community/mathlib4` at `v4.27.0-rc1`.

## License Notes

This package uses Apache-2.0 as the release license for the packaging scripts
and newly collected proof files. Upstream theorem statements retain their
original licenses and notices. See `LICENSES/THIRD_PARTY.md`.
