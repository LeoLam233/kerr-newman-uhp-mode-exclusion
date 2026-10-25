# KN-UHP-C002 Lean development

Pinned Lean 4.34.1 and Mathlib commit d13f23b723b8a846827a245b89c10fc7d3f11612.
All dependency revisions are in lake-manifest.json.

## Main declarations

- KN.Physics.radiative_mode_exclusion: all four literal radiative invariants vanish, for every strictly subextremal background, integer azimuthal number and upper-half-plane frequency, including signed charge, Q=0, and the closed angular interval.
- KN.Physics.physical_mode_exclusion: the explicitly typed one-way published physical-entry implication composed with that theorem.
- KN.Angular.original_source_exclusion: both original four-component charged necessary source systems, with original physical boundary data, vanish pointwise.
- KN.Kerr.kerr_full_field_exclusion: actual full canonical Kerr fields for spins +2,+1,-1,-2, including exceptional positive-spin horizon frequencies.

The classical physical entry is an explicit interface argument. A full differential-geometric Einstein–Maxwell theory instance is not independently constructed here. The exact contract, named published mathematical interfaces and sources are in EXTERNAL_INTERFACES.md. All C002-specific source conversion, spectral, radial-transform, coercivity, endpoint and spin-reversal steps are implemented, not imported as exclusion assumptions.

## Reproduce

Install the pinned toolchain, restore the exact locked dependencies, then run:

    lake build KN AuditKN
    lake env lean -j1 -DwarningAsError=true AuditKN.lean
    lake env leanchecker --fresh --verbose KN

The complete clean build and official fresh kernel replay are distinct checks.
For isolated source-bound verification, use validation/run_full_gate.py with the supplied frozen source/runtime manifests and a NEW clean project directory. It rejects pre-existing project objects and dependency revision/source mismatches.

Author contract controls are under validation/controls_*. They include mathematical counterexamples and intended compilation failures. The portable aggregate runner is validation/run_controls.py. These controls are not independent adversarial audits.

COVERAGE.md maps the manuscript to the code. Final acceptance requires the exact source identity, complete build and replay receipts, all three independent whole-proof audit reports and coordinator adjudication. Those evidence records are delivered separately; no status is inferred merely from the existence of this source package.

No manuscript modifications, external scholarly communications or public repository publication are part of this project.
