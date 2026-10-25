# Audit and source provenance

**Controlling manuscript:** `manuscript/C002_v1.0.pdf` (11 pages), SHA-256 `3918225f220943dcdf67a2db7646ab7c375238d0a7ec204a1368a938a6173797`.

**Original frozen mathematical/Lean source identity:** `dd09e7f6962f7e09b083a46d942083773b4c734821e9d8012dca8387d6c665ff`; 342 files. The precise originals are bound by `provenance/ORIGINAL_SOURCE_MANIFEST.json`. The release-derived identity and the exact modified/additional paths are in `release_checks/RELEASE_DELTA.json`.

## Completed audit records

- Dot: implementation, clean build, official fresh-kernel replay and three internal adversarial reviews (original completion record).
- Codex 6.1 Sol Max: independent mathematical/Lean adjudication `EXHAUSTED`, with four actual successful `lake build KN AuditKN`, strict-check and fresh-kernel replay instances. Full reproducibility archive SHA-256 `b63abf88234062d5430cfe09eff26b1e24dc1b976c907567b6195596980cfb33` is retained separately, **not embedded in this Git repository**.
- ChatGPT Pro: separate mathematical/Lean adjudication `EXHAUSTED`, with an independent coordinator clean build, strict elaboration and official fresh-kernel replay; three new-context workers additionally investigated and submitted sealed initial reports. The coordinator disclosed pre-seal historical-memory/filename exposure; it is not described as four perfectly memory-blind workers.

## Pro archival loss

The Pro reproducibility ZIP `KN_UHP_C002_PRO_AUDIT_REPRODUCIBILITY_20261024.zip` was created and checked in the original Pro execution, with reported size 186,773,029 bytes and SHA-256 `9eb22090523da917e8d2c0e38556b83c0caf9faf1c84e0bb2aecdbe6a7ac9c97`. The original archive is **not retrievable**. The full final report (SHA-256 `b8c49c7a3e1e052ddcf40a45f3264d2e369f17e624a16bf87ee6d515f6f32f16`), verification JSON, recorded checksum and delivery-status JSON survived in the user's Library; an abbreviated report is included in the *private handoff*, not presented as the original full log collection. The lost four initial Pro reports and intermediate logs are not recreated or claimed as existing.

This affects retained audit reproducibility, **not the content of the frozen Lean proof**. No replacement package is advertised as having the original missing ZIP's SHA-256.

## Actual mathematical and formal boundaries

The physical-entry bridge remains a parameter to the main Lean theorem. The classical necessary equations/normalization were independently read against primary sources; no new physical-entry construction was added. The 23 classical interfaces were audited, and 22 are reachable from either final physical root. Whiting/TdC is used only for negative Kerr spins after a proved Teukolsky–Starobinsky reversal. The frozen proof and exact kernel closures contain no `sorryAx` or compiler-trust axiom in their four audited roots.

## Auxiliary verification fix

Codex and Pro found that the old `validation/run_controls.py` could count a missing-import compiler error as a successful negative control. Its negative-result forbidden-diagnostic list lacked `failed to read file`. The publication derivative adds this and a few equivalent import-missing diagnostics. Old script, exact diff, and static replay tests are included. Codex must re-run **actual** control fixtures and source/kernel checks on the publication tree before pushing.
