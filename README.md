# Upper-half-plane radiative mode exclusion for subextremal Kerr–Newman

The accompanying paper develops an analytic upper-half-plane exclusion argument for the radiative linearized Einstein–Maxwell modes of strictly subextremal Kerr–Newman black holes. The Lean 4 project formalizes the complete exclusion chain from the **explicitly stated published physical necessary-data interface**, including the charged, nonseparated angular/PDE argument and the separate Kerr spin-reversal branch.

## Contents

- [`manuscript/C002_v1.0.pdf`](manuscript/C002_v1.0.pdf) — governing 11-page mathematical manuscript; TeX and Markdown counterparts are alongside it.
- [`KN/`](KN/) — Lean proof development; [`KN.lean`](KN.lean) and [`AuditKN.lean`](AuditKN.lean) provide entry points and strict theorem/axiom queries.
- [`EXTERNAL_INTERFACES.md`](EXTERNAL_INTERFACES.md) — exact external mathematical facts and physical-entry contracts.
- [`COVERAGE.md`](COVERAGE.md) with [`docs/COVERAGE_CORRECTION_APPENDIX.md`](docs/COVERAGE_CORRECTION_APPENDIX.md) — manuscript correspondence and corrections to legacy reachability labels.
- [`docs/AUDIT_AND_PROVENANCE.md`](docs/AUDIT_AND_PROVENANCE.md) — version identity and external audit status.
- [`docs/REPRODUCTION.md`](docs/REPRODUCTION.md) — build and kernel-replay instructions.

## Formal endpoints

- `KN.Physics.radiative_mode_exclusion` — vanishing of the four specified radiative curvature–Maxwell invariants for full-domain supplied necessary data;
- `KN.Physics.physical_mode_exclusion` — composition with a supplied published physical-entry mapping and admissibility proof;
- `KN.Angular.original_source_exclusion` — both original charged source systems;
- `KN.Kerr.kerr_full_field_exclusion` — the full Kerr spin ±1, ±2 branch, not merely a separated scalar candidate.

Parameters cover every real `M > 0` with `a² + Q² < M²`, both signs of `Q`, every integer azimuthal number, and every complex frequency with positive imaginary part. The outgoing/axis/horizon requirements are those of the manuscript. The conclusion is about the specified **radiative invariants**; it is not a classification of all gauge/parameter modes.

## Physical-entry boundary

The formal physical theorem requires `PublishedEinsteinMaxwellEntry` and `entry.smoothOutgoingMode p`; the more direct radiative theorem requires `PublishedPhysicalNecessaryData`. These arguments contain the published necessary equations, normalization and physical boundary data. They do **not** contain a radiative-vanishing or mode-exclusion premise. The project has not constructed a complete tensor-level Einstein–Maxwell perturbation theory instance; the classical one-way necessity bridge is documented and separately audited. There are 23 custom classical interfaces; 22 are reachable from the physical roots. See [`EXTERNAL_INTERFACES.md`](EXTERNAL_INTERFACES.md).

## Reproduction

Use the pinned Lean toolchain (`lean-toolchain`) and exact dependency lock (`lake-manifest.json`):

```sh
lake build KN AuditKN
lake env lean -j1 -DwarningAsError=true AuditKN.lean
lake env leanchecker --fresh --verbose KN
```

The author controls are in `validation/controls_*`. Run `python3 validation/run_controls.py --project . --lean-bin-dir /path/to/lean/bin --results /path/to/new/results`. The release version corrects an auxiliary negative-control diagnostic filter; neither the Lean proof declarations nor mathematical manuscript was modified. See the version delta and test receipt in `release_checks/`.

## Identity and publication

Original math/Lean audit source identity: `dd09e7f6962f7e09b083a46d942083773b4c734821e9d8012dca8387d6c665ff` (342 manifested files). This repository is a **documented derivative**: only the auxiliary control runner and this README change among those 342 files, while new release documentation is added. The mathematical `.lean` and manuscript bytes are identical to the audited candidate. The publication copy receives its own new identity; do not relabel it as the unmodified freeze.

The original C002 paper, Dot internal three audits and independent Codex/Pro mathematical–Lean audits are covered in the provenance notes. The original Pro reproducibility ZIP was lost after successful archival verification; its report and verification receipt were retained. No replacement ZIP is claimed to be that lost archive.

No authorship, institutional affiliation or open-source license has been invented for this release. Bibliographic and licensing decisions should be made explicitly by the repository owner.
