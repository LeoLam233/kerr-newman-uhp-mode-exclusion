import KN.Angular.FullMultiplier
import KN.Analysis.OperatorAnticommutation
import KN.Analysis.FullChiralAlgebra
import KN.Analysis.ResolventAdjoint

namespace KN.Angular
noncomputable section
open scoped ComplexInnerProductSpace

private theorem fullFrequencyOperator_anti (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (U : FullAngularHilbert →L[ℂ] FullAngularHilbert)
    (hgraph : ∀ u v, FullStaticGraph σ b.beta m u v → FullStaticGraph σ b.beta m (U u) (-U v))
    (hfreq : ∀ u, fullFrequencyMultiplier b σ (U u) = -U (fullFrequencyMultiplier b σ u))
    (x : (fullFrequencyOperator b hQ σ hσ m ω).domain) :
    ∃ hx : U x ∈ (fullFrequencyOperator b hQ σ hσ m ω).domain,
      fullFrequencyOperator b hQ σ hσ m ω ⟨U x,hx⟩ =
        -U (fullFrequencyOperator b hQ σ hσ m ω x) := by
  have hg := (fullStaticOperator_graph b hQ σ hσ m x
    (fullStaticOperator b hQ σ hσ m x)).mp ⟨x.property,rfl⟩
  obtain ⟨hmem,he⟩ := (fullStaticOperator_graph b hQ σ hσ m _ _).mpr (hgraph _ _ hg)
  refine ⟨hmem,?_⟩
  change fullStaticOperator b hQ σ hσ m ⟨U x,hmem⟩ + ω • fullFrequencyMultiplier b σ (U x) =
    -U (fullStaticOperator b hQ σ hσ m x + ω • fullFrequencyMultiplier b σ x)
  rw [he,hfreq,map_add,map_smul,smul_neg,neg_add]

theorem fullFrequencyOperator_I (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (x : (fullFrequencyOperator b hQ σ hσ m ω).domain) :
    ∃ hx : fullI x ∈ (fullFrequencyOperator b hQ σ hσ m ω).domain,
      fullFrequencyOperator b hQ σ hσ m ω ⟨fullI x,hx⟩ =
        -fullI (fullFrequencyOperator b hQ σ hσ m ω x) :=
  fullFrequencyOperator_anti b hQ σ hσ m ω fullI
    (fun _ _ h => fullStaticGraph_I σ b.beta m h) (fullFrequencyMultiplier_I b σ) x

theorem fullFrequencyOperator_J (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (x : (fullFrequencyOperator b hQ σ hσ m ω).domain) :
    ∃ hx : fullJ x ∈ (fullFrequencyOperator b hQ σ hσ m ω).domain,
      fullFrequencyOperator b hQ σ hσ m ω ⟨fullJ x,hx⟩ =
        -fullJ (fullFrequencyOperator b hQ σ hσ m ω x) :=
  fullFrequencyOperator_anti b hQ σ hσ m ω fullJ
    (fun _ _ h => fullStaticGraph_J σ b.beta m h) (fullFrequencyMultiplier_J b σ) x

theorem fullI_symmetric (u v : FullAngularHilbert) : ⟪fullI u,v⟫=⟪u,fullI v⟫ := by
  rw [MeasureTheory.L2.inner_def,MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [fullI_ae u,fullI_ae v] with θ hu hv
  rw [hu,hv]
  change ⟪KN.Physics.I4.toEuclideanLin (u θ),v θ⟫=⟪u θ,KN.Physics.I4.toEuclideanLin (v θ)⟫
  rw [← LinearMap.adjoint_inner_right,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    KN.Analysis.I4_conjTranspose]

theorem fullFrequencyOperator_adjoint_I (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (x : (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain) :
    ∃ hx : fullI x ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain,
      (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨fullI x,hx⟩ =
        -fullI ((fullFrequencyOperator b hQ σ hσ m ω).adjoint x) :=
  KN.Analysis.adjoint_anticommutes (fullFrequencyOperator b hQ σ hσ m ω) (fullStaticOperator_selfAdjoint b hQ σ hσ m).dense_domain
    fullI (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fullI_symmetric)
    (fullFrequencyOperator_I b hQ σ hσ m ω) x

theorem fullFrequencyOperator_adjoint_J (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (x : (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain) :
    ∃ hx : fullJ x ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain,
      (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨fullJ x,hx⟩ =
        -fullJ ((fullFrequencyOperator b hQ σ hσ m ω).adjoint x) :=
  KN.Analysis.adjoint_anticommutes (fullFrequencyOperator b hQ σ hσ m ω) (fullStaticOperator_selfAdjoint b hQ σ hσ m).dense_domain
    fullJ (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr KN.Analysis.fullJ_symmetric)
    (fullFrequencyOperator_J b hQ σ hσ m ω) x

theorem fullFrequencyOperator_adjoint_chiral (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ)
    (x : (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain) :
    ∃ hx : chiralLpMap (chiralProjection x) ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain,
      (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨chiralLpMap (chiralProjection x),hx⟩ =
        chiralLpMap (chiralProjection ((fullFrequencyOperator b hQ σ hσ m ω).adjoint x)) := by
  simp only [KN.Analysis.full_chiral_projection]
  exact KN.Analysis.chiralProjection_commutes _ fullI fullJ
    (fullFrequencyOperator_adjoint_I b hQ σ hσ m ω)
    (fullFrequencyOperator_adjoint_J b hQ σ hσ m ω) x

end
end KN.Angular
