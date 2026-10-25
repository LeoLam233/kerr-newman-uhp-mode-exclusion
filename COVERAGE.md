# Active C002 source-to-theorem map

This is the initial complete implementation candidate, not a final verification or audit outcome. All production modules have been individually compiled. The frozen clean build, separate kernel replay and three independent audits are still required.

| Manuscript obligation | Lean declaration or source | Scope | Current status |
|---|---|---|---|
| Background and signed charge, Eq. (1) | KN.Background.Parameters | Discriminant, horizon factorization, kappa/c and beta/c identities | compiled |
| Source matrices, Eq. (6) | KN.Physics.physicalSourceMatrix_det; KN.Physics.sourceMatrix_adjugate; KN.Physics.sourceMatrix_conjTranspose_real | Actual determinant and complex-frequency-independent source matrices | compiled |
| Source PDE conversion, Eq. (2)–(5) | KN.Physics.source_chiral_transport; KN.Physics.source_four_transport | Actual derivatives of source matrices and original published Eq. (4) | compiled, including actual Hilbert constructor |
| Horizon weights, Eq. (7) | KN.Physics.positive_source_horizon_transport; KN.Physics.negative_source_horizon_transport; KN.Physics.sourcePack_horizons | Pointwise algebra and actual full projections; original Hilbert boundary normalization | compiled, including original Hilbert source boundary |
| Radiative invariants, Eq. (8a)–(8b) | KN.Physics.physical_radiative_zero_of_source_transforms; KN.Physics.electromagneticPlus_zero_charge; KN.Physics.electromagneticMinus_zero_charge | Exact gauge mixtures and charge split normalization | compiled |
| Static angular spectrum and exceptional branch, Eq. (9)–(14) | KN.Angular.Jacobi.staticHilbertBasis | Actual graph eigenvectors, complete Jacobi basis and optional unpaired branch | compiled |
| Charged signed coercivity, Eq. (15)–(19) | KN.Angular.physical_angular_form_nonneg | Actual normalized eigenvector expectations; no positivity interface | compiled |
| Full adjoint spectral/Jordan detection, Eq. (20)–(24) | KN.Angular.fullFrequencyOperator_dense_adjoint_roots; KN.Angular.full_chiral_chain_extraction | Actual operator, compact-resolvent estimates and globally first detecting chain pair | compiled |
| Actual rescaling and supported distribution correction, Eq. (25)–(35) | KN.ChargedRadial.physical_supported_pair_elimination; KN.ChargedRadial.physical_resonant_factorized_supported_pair | Division-free elimination and exceptional supported delta correction | compiled |
| Actual transform and energy, Eq. (36)–(49) | KN.Energy.physical_supported_pair_transformedEquation; KN.ChargedRadial.charged_original_eigenmode_exclusion | Both radial fields vanish with all growth, endpoint and angular obligations derived | compiled |
| Charged complete field | KN.Angular.full_field_exclusion | Both signs, actual maximal angular graph and exact horizon projections | compiled |
| Kerr source operator and full-field reduction, Eq. (50)–(52) | KN.Kerr.kerr_full_field_exclusion | Actual canonical spherical spin-bundle graph, adjoint chains and all four spins | compiled |
| Kerr spin reversal, Eq. (53)–(59) | KN.Kerr.positive_spin_separated_exclusion; KN.Kerr.negative_spin_separated_exclusion; KN.Kerr.kerr_separated_exclusion | Actual operator intertwiners, reflected angular field, exceptional horizon and outgoing injectivity | compiled |
| Kerr four physical components | KN.Physics.kerr_all_radiative_fields_zero | Separate Q=0 necessary-system composition, not charged limit | compiled |
| Final physical parameter-uniform theorem | KN.Physics.radiative_mode_exclusion; KN.Physics.physical_mode_exclusion | Explicit published physical entry, original source recovery, charge split and closed-axis conclusion | compiled; full frozen verification and independent audits pending |

Physical-entry scope: the exact classical necessary-system implication is an explicit theorem argument, described fully in EXTERNAL_INTERFACES.md. It is not a constructed formal Einstein–Maxwell theory instance.
