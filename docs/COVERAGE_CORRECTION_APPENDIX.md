# Coverage correction appendix (separate from frozen COVERAGE.md)

Machine-checked exact names, kinds, imported-environment type/value reachability paths and explanatory direct proof-value edges. Interpretations are limited to the included frozen source and types. This is not an independent mathematical audit or proof of physical adequacy.

The frozen COVERAGE.md remains unchanged. Seven original labels are examined below. Replacement/alternate names are checked against the imported environment and their paths from physical_mode_exclusion; distinctions between proof, definition, contract projection and unused wrapper are preserved.

## KN.Background.Parameters

Obligation: Background and signed charge, Eq. (1)

Relation: module_label_with_exact_declarations

The original table permits a source as well as a declaration. KN.Background.Parameters is the existing module KN/Background/Parameters.lean, not a missing implementation. These are exact reachable declarations in that module; Background is an inductive structure, the remaining named entries are proved identities.

Actual reachable declarations:

- `KN.Background` (inductive; module `KN.Background.Parameters`).
- `KN.Background.discriminant_pos` (theorem; module `KN.Background.Parameters`).
- `KN.Background.delta_factor` (theorem; module `KN.Background.Parameters`).
- `KN.Background.kappa_sq_sub_c_sq` (theorem; module `KN.Background.Parameters`).
- `KN.Background.beta_mul_c` (theorem; module `KN.Background.Parameters`).

Source evidence: `KN/Background/Parameters.lean`.

## KN.Physics.positive_source_horizon_transport

Obligation: Horizon weights, Eq. (7)

Relation: parallel_hilbert_space_proof_route

The unused theorem is a finite-dimensional matrix transport statement. The reachable route instead proves Hilbert-space transport, derives it from OriginalSourceBoundary and packs the full projections. Its type explicitly has weights -1/4 and -3/4. These are not aliases or identical theorem types; the source implements a parallel Hilbert-space argument for the obligation used by the endpoint.

Actual reachable declarations:

- `KN.Physics.positive_hilbert_horizon_transport` (theorem; module `KN.Physics.SourceHilbertBoundaryHorizon`).
- `KN.Physics.source_hilbert_horizon_positive` (theorem; module `KN.Physics.SourceHilbertBoundaryHorizonFinal`).
- `KN.Physics.sourcePack_horizons` (theorem; module `KN.Physics.SourceFullPacking`).
- `KN.Angular.OriginalSourceField.transformed_horizons` (theorem; module `KN.Angular.OriginalSourceBoundary`).

Source evidence: `KN/Physics/SourceHorizonRegularity.lean`, `KN/Physics/SourceHilbertBoundaryHorizon.lean`, `KN/Physics/SourceHilbertBoundaryHorizonFinal.lean`, `KN/Angular/OriginalSourceBoundary.lean`.

## KN.Physics.negative_source_horizon_transport

Obligation: Horizon weights, Eq. (7)

Relation: parallel_hilbert_space_proof_route

The unused theorem is a finite-dimensional matrix transport statement. The reachable route instead proves Hilbert-space transport, derives it from OriginalSourceBoundary and packs the full projections. Its type explicitly has weights 3/4 and 5/4. These are not aliases or identical theorem types; the source implements a parallel Hilbert-space argument for the obligation used by the endpoint.

Actual reachable declarations:

- `KN.Physics.negative_hilbert_horizon_transport` (theorem; module `KN.Physics.SourceHilbertBoundaryHorizon`).
- `KN.Physics.source_hilbert_horizon_negative` (theorem; module `KN.Physics.SourceHilbertBoundaryHorizonFinal`).
- `KN.Physics.sourcePack_horizons` (theorem; module `KN.Physics.SourceFullPacking`).
- `KN.Angular.OriginalSourceField.transformed_horizons` (theorem; module `KN.Angular.OriginalSourceBoundary`).

Source evidence: `KN/Physics/SourceHorizonRegularity.lean`, `KN/Physics/SourceHilbertBoundaryHorizon.lean`, `KN/Physics/SourceHilbertBoundaryHorizonFinal.lean`, `KN/Angular/OriginalSourceBoundary.lean`.

## KN.Physics.physical_radiative_zero_of_source_transforms

Obligation: Radiative invariants, Eq. (8a)–(8b)

Relation: alternate_composition_through_original_source_recovery

The unused theorem combines pointwise sourceTransform inversion with phantom recovery. The endpoint instead recovers original components from the full Hilbert transform via original_source_exclusion, invokes phantom_radiative_zero directly, and uses the explicit PhantomIdentification assumption. This is a different composition, not an alias; the claimed physical identification remains an argument contract.

Actual reachable declarations:

- `KN.Physics.sourceFullTransform_original_pointwise_zero` (theorem; module `KN.Physics.SourceHilbertRecovery`).
- `KN.Angular.original_source_exclusion` (theorem; module `KN.Angular.OriginalSourceExclusion`).
- `KN.Physics.phantom_radiative_zero` (theorem; module `KN.Physics.RadiativeRecovery`).
- `KN.Physics.charged_radiative_pointwise_zero` (theorem; module `KN.Physics.Main`).
- `KN.Physics.PhantomIdentification` (definition; module `KN.Physics.PhysicalEntry`).

Source evidence: `KN/Physics/PhysicalRadiativeRecovery.lean`, `KN/Physics/SourceHilbertRecovery.lean`, `KN/Angular/OriginalSourceExclusion.lean`, `KN/Physics/RadiativeRecovery.lean`, `KN/Physics/Main.lean`, `KN/Physics/PhysicalEntry.lean`.

## KN.Physics.electromagneticPlus_zero_charge

Obligation: Radiative invariants and zero-charge normalization, Eq. (8a)–(8b)

Relation: no_like_for_like_reachable_normalization_theorem_identified

Retain the original identity as an independently proved, unused algebraic lemma. No like-for-like reachable proof of that zero-charge normalization is identified here. The actual endpoint path works on the literal radiativeValue and uses the explicit kerr field of PublishedPhysicalNecessaryData to obtain the necessary equations and almost-everywhere identification. The reachable definition and contract projection are not substitutes for a proved normalization theorem. A corrected endpoint map should state this alternate conditional route separately, not relabel the unused identity as reachable.

Actual reachable declarations:

- `KN.Physics.electromagneticPlus` (definition; module `KN.Physics.NPSystem`).
- `KN.Physics.backgroundPsiTwo` (definition; module `KN.Physics.PhysicalEntry`).
- `KN.Physics.radiativeValue` (definition; module `KN.Physics.PhysicalEntry`).
- `KN.Physics.PublishedPhysicalNecessaryData.kerr` (theorem; module `KN.Physics.PhysicalEntry`).
- `KN.Physics.KerrRadiativeNecessarySystem` (inductive; module `KN.Physics.KerrRadiativeExclusion`).
- `KN.Physics.kerr_all_radiative_fields_zero` (theorem; module `KN.Physics.KerrRadiativeExclusion`).
- `KN.Physics.kerr_radiative_pointwise_zero` (theorem; module `KN.Physics.KerrRadiativePointwise`).

Source evidence: `KN/Physics/NPSystem.lean`, `KN/Physics/RadiativeRecovery.lean`, `KN/Physics/PhysicalEntry.lean`, `KN/Physics/KerrRadiativeExclusion.lean`, `KN/Physics/KerrRadiativePointwise.lean`.

## KN.Physics.electromagneticMinus_zero_charge

Obligation: Radiative invariants and zero-charge normalization, Eq. (8a)–(8b)

Relation: no_like_for_like_reachable_normalization_theorem_identified

Retain the original identity as an independently proved, unused algebraic lemma. No like-for-like reachable proof of that zero-charge normalization is identified here. The actual endpoint path works on the literal radiativeValue and uses the explicit kerr field of PublishedPhysicalNecessaryData to obtain the necessary equations and almost-everywhere identification. The reachable definition and contract projection are not substitutes for a proved normalization theorem. A corrected endpoint map should state this alternate conditional route separately, not relabel the unused identity as reachable.

Actual reachable declarations:

- `KN.Physics.electromagneticMinus` (definition; module `KN.Physics.NPSystem`).
- `KN.Physics.backgroundPsiTwo` (definition; module `KN.Physics.PhysicalEntry`).
- `KN.Physics.radiativeValue` (definition; module `KN.Physics.PhysicalEntry`).
- `KN.Physics.PublishedPhysicalNecessaryData.kerr` (theorem; module `KN.Physics.PhysicalEntry`).
- `KN.Physics.KerrRadiativeNecessarySystem` (inductive; module `KN.Physics.KerrRadiativeExclusion`).
- `KN.Physics.kerr_all_radiative_fields_zero` (theorem; module `KN.Physics.KerrRadiativeExclusion`).
- `KN.Physics.kerr_radiative_pointwise_zero` (theorem; module `KN.Physics.KerrRadiativePointwise`).

Source evidence: `KN/Physics/NPSystem.lean`, `KN/Physics/RadiativeRecovery.lean`, `KN/Physics/PhysicalEntry.lean`, `KN/Physics/KerrRadiativeExclusion.lean`, `KN/Physics/KerrRadiativePointwise.lean`.

## KN.Angular.full_field_exclusion

Obligation: Charged complete field

Relation: unused_signed_wrapper_of_reachable_boolean_sign_theorem

full_field_exclusion splits the signed hypothesis sigma = 1 or sigma = -1 and calls charged_full_field_exclusion with true or false. original_source_exclusion calls the Boolean-sign theorem directly. The supplemental closure comparison shows that the wrapper itself is its only project declaration absent from the physical endpoint closure.

Actual reachable declarations:

- `KN.Angular.charged_full_field_exclusion` (theorem; module `KN.Angular.FullFieldExclusion`).
- `KN.Angular.original_source_exclusion` (theorem; module `KN.Angular.OriginalSourceExclusion`).

Source evidence: `KN/Angular/FullFieldExclusion.lean`, `KN/Angular/OriginalSourceExclusion.lean`.

## Machine checks

- Seven map entries; 18 explanatory direct proof-value edges verified.
- Every listed alternative exists and is reachable from the final physical endpoint through types and/or values. Edge kinds are explicit in the JSON.
- Original six theorem names remain absent from that endpoint closure; Background.Parameters remains a module label, not a declaration.
- The originating appendix refers to `coverage_correction_appendix.json` for exact types, reachability paths and frozen excerpts. That JSON is absent from both this source handoff and the retained Codex audit ZIP examined for this release. The coverage notes above are retained as historical documentation; current native root types and axiom sets are checked separately in `release_checks/`.
- These checks do not establish equivalence between differently typed alternatives, literature fidelity, or validity of external physical contracts. In particular, the zero-charge normalization identities are not silently replaced by a contract projection.
