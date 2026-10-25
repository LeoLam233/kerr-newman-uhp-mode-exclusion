# Reproduction of the published Lean project

Source/revision controls:

1. Verify `python3 release_checks/verify_release.py .` (checks all 342 original files and the exact allowed release delta, including every `.lean` and the manuscript).
2. Install Lean 4.34.1 from `lean-toolchain` and use `lake-manifest.json` at its exact pinned package commits. Mathlib caches may be used, but do not silently change dependencies.
3. From a new worktree without project `.lake/build` objects, run `lake build KN AuditKN` and capture stdout/stderr and exit code. For a fully clean Lake check the already-audited invocations included `lake -R -H build KN AuditKN`; this may be expensive.
4. Run `lake env lean -j1 -DwarningAsError=true AuditKN.lean` and `lake env leanchecker --fresh --verbose KN` with complete native logs.
5. In a separate new directory run the supplied `validation/run_controls.py` for all thirty supplied control fixtures, and verify diagnostic origin manually or with a stricter independent validator; exit code alone is insufficient.
6. Compute source, executable/dependency and final Git commit identities and retain them in the release receipt.

The auditor's **known-good original source** was `dd09e7f6…c665ff`. The publication tree corrects an auxiliary runner and a README without changing any theorem or manuscript bytes, and therefore has a *different* source identity. Only actual new invocations may be recorded as successful for that exact publication tree.

The full Codex review archive is separate; the Pro reproduction ZIP is unavailable. Preserve the distinction between verified original audits, static release tests, and actual native publication checks.

## Publication verification on 25 October 2026

The [native publication receipt](../release_checks/NATIVE_VERIFICATION.json) records the actual clean build, strict check, fresh kernel replay, all 30 corrected controls, independent diagnostic validation, and native import-failure probes. The complete path-redacted log archive has been prepared with the filename and checksum in that receipt. Its attachment to a GitHub Release is a separate publication step; consult the receipt for the actual upload status. Their exact native and published-copy hashes are distinguished.

The [native root types and axiom output](../release_checks/NATIVE_ROOT_TYPES_AND_AXIOMS.txt) was compared with the preserved successful Codex audit output. Recheck a new strict output with `python3 release_checks/compare_archived_roots.py path/to/strict.stdout.log`. The baseline archive hash is retained; the unavailable Pro archive is not reconstructed.
