#!/usr/bin/env python3
"""Static and Lean compiler verification for this proof pack."""

from __future__ import annotations

import argparse
import concurrent.futures
import os
import re
import subprocess
import sys
from pathlib import Path


FORBIDDEN_RE = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
LOCAL_PATH_MARKERS = ["/" + "Users" + "/", "/" + "public" + "/" + "home" + "/"]
PRIVATE_RE = re.compile(
    r"(" + "|".join(re.escape(marker) for marker in LOCAL_PATH_MARKERS) +
    r"|OPENAI|ANTHROPIC|API[_-]?KEY|TOKEN|PASSWORD|SECRET|"
    r"Qwen|DeepSeek|Claude|ChatGPT|jsonl|slurm|dwq)",
    re.IGNORECASE,
)
THEOREM_RE = re.compile(r"(?m)^\s*theorem\s+")


def static_errors(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    errors: list[str] = []
    if FORBIDDEN_RE.search(text):
        errors.append("forbidden token")
    if PRIVATE_RE.search(text):
        errors.append("private/log token")
    if "--" in text or "/-" in text:
        errors.append("comment marker")
    theorem_count = len(THEOREM_RE.findall(text))
    if theorem_count != 1:
        errors.append(f"theorem_count={theorem_count}")
    return errors


def compile_one(path: Path, lake_root: Path, timeout: int) -> tuple[Path, int, str]:
    proc = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=lake_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=timeout,
    )
    return path, proc.returncode, proc.stdout[-4000:]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lake-root", type=Path)
    parser.add_argument("--jobs", type=int, default=max(1, min(os.cpu_count() or 4, 8)))
    parser.add_argument("--timeout", type=int, default=180)
    parser.add_argument("--no-compile", action="store_true")
    args = parser.parse_args()

    root = args.root.resolve()
    lake_root = (args.lake_root or root).resolve()
    files = sorted((root / "proofs").rglob("*.lean"))
    print(f"proof_files={len(files)}", flush=True)

    static_failures = [(p, static_errors(p)) for p in files]
    static_failures = [(p, errs) for p, errs in static_failures if errs]
    if static_failures:
        print("static check failed:", flush=True)
        for path, errs in static_failures[:30]:
            print(f"  {path.relative_to(root)}: {', '.join(errs)}", flush=True)
        return 1
    print("static_ok=1", flush=True)

    if args.no_compile:
        return 0

    failures = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = [pool.submit(compile_one, path.resolve(), lake_root, args.timeout) for path in files]
        for index, future in enumerate(concurrent.futures.as_completed(futures), 1):
            path, code, output = future.result()
            if code != 0:
                failures.append((path, output))
            if index % 25 == 0 or index == len(files):
                print(f"compiled={index}/{len(files)} failures={len(failures)}", flush=True)

    if failures:
        print("compile failed:", flush=True)
        for path, output in failures[:20]:
            rel = path.relative_to(root) if path.is_relative_to(root) else path
            print(f"--- {rel} ---", flush=True)
            print(output, flush=True)
        return 1

    print("compile_ok=1", flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
