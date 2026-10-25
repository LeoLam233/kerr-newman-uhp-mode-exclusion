import KN.Angular.FullOperatorSymmetry
import KN.Angular.ChiralPairing
import KN.Angular.ReducedMultiplier
import KN.Angular.GraphLinearity
import KN.Analysis.FullConjugationChiral
import KN.Analysis.FullConjugationMultiplier

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory

theorem fullFrequencyMultiplier_chiral (b : KN.Background) (σ : ℝ) (u : AngularHilbert) :
    fullFrequencyMultiplier b σ (chiralLpMap u)=chiralLpMap (reducedFrequencyMultiplier b σ u) := by
  apply Lp.ext
  filter_upwards [fullFrequencyMultiplier_ae b σ (chiralLpMap u),chiralLpMap_ae u,
    chiralLpMap_ae (reducedFrequencyMultiplier b σ u),reducedFrequencyMultiplier_ae b σ u]
    with θ h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  change ((fullStaticPotential _ _).toEuclideanLin.comp chiralEmbedding.toEuclideanLin) (u θ)=
    (chiralEmbedding.toEuclideanLin.comp (massPotential _ _).toEuclideanLin) (u θ)
  rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2,chiral_potential]

theorem fullFrequencyOperator_adjoint (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω : ℂ) :
    (fullFrequencyOperator b hQ σ hσ m ω).adjoint =
      fullFrequencyOperator b hQ σ hσ m (star ω) := by
  have hV : (fullFrequencyMultiplier b σ).adjoint=fullFrequencyMultiplier b σ :=
    IsSelfAdjoint.adjoint_eq
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (fullFrequencyMultiplier_symmetric b σ))
  unfold fullFrequencyOperator
  rw [KN.Analysis.boundedPerturbation_adjoint _ (fullStaticOperator_selfAdjoint b hQ σ hσ m),
    map_smulₛₗ,hV]
  rfl

/-- The explicit antilinear real structure supplies a right eigenvector at the
conjugate adjoint eigenvalue, retaining the actual chiral maximal domain. -/
theorem reduced_eigenvector_of_chiral_adjoint (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω z : ℂ)
    (e : FullAngularHilbert) (he : e ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain)
    (hee : (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨e,he⟩=z • e)
    (hne : e≠0) (hchiral : ChiralVector e) :
    ∃ u : AngularHilbert, u≠0 ∧
      StaticGraph σ b.beta m u ((star z) • u-ω • reducedFrequencyMultiplier b σ u) := by
  have hpack : ∃ he : e ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain,
      (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨e,he⟩=z • e := ⟨he,hee⟩
  rw [fullFrequencyOperator_adjoint] at hpack
  have hg := (fullFrequencyOperator_graph b hQ σ hσ m (star ω) e (z • e)).mp hpack
  have hc := KN.Analysis.fullRealStructure_graph σ b.beta m hg
  rw [map_sub,KN.Analysis.fullRealStructure_smul,KN.Analysis.fullRealStructure_smul,
    star_star,KN.Analysis.fullRealStructure_multiplier] at hc
  obtain ⟨a,ha⟩ := hchiral
  have heC := KN.Analysis.fullRealStructure_chiral a
  rw [← ha] at heC
  rw [heC,fullFrequencyMultiplier_chiral] at hc
  have hm : star z • chiralLpMap (KN.Analysis.chiralRealMap a) -
      ω • chiralLpMap (reducedFrequencyMultiplier b σ (KN.Analysis.chiralRealMap a)) =
      chiralLpMap (star z • KN.Analysis.chiralRealMap a -
        ω • reducedFrequencyMultiplier b σ (KN.Analysis.chiralRealMap a)) := by
    rw [map_sub,map_smul,map_smul]
  rw [hm] at hc
  refine ⟨KN.Analysis.chiralRealMap a,?_,(fullStaticGraph_chiral_iff σ b.beta m _ _).mp hc⟩
  intro hz
  have hh := KN.Analysis.fullRealStructure_ne_zero hne
  rw [heC,hz,map_zero] at hh
  exact hh rfl


theorem normalized_reduced_eigenvector_of_chiral_adjoint (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (ω z : ℂ)
    (e : FullAngularHilbert) (he : e ∈ (fullFrequencyOperator b hQ σ hσ m ω).adjoint.domain)
    (hee : (fullFrequencyOperator b hQ σ hσ m ω).adjoint ⟨e,he⟩=z • e)
    (hne : e≠0) (hchiral : ChiralVector e) :
    ∃ u v : AngularHilbert, ‖u‖=1 ∧ StaticGraph σ b.beta m u v ∧
      v+ω • reducedFrequencyMultiplier b σ u=(star z) • u := by
  obtain ⟨a,hane,hag⟩ := reduced_eigenvector_of_chiral_adjoint b hQ σ hσ m ω z e he hee hne hchiral
  let c : ℂ := (‖a‖⁻¹ : ℝ)
  refine ⟨c • a,c • ((star z) • a-ω • reducedFrequencyMultiplier b σ a),?_,
    StaticGraph.smul σ b.beta m hag c,?_⟩
  · dsimp only [c]
    rw [Complex.ofReal_inv]
    exact norm_smul_inv_norm (𝕜 := ℂ) hane
  · rw [map_smul,smul_sub,smul_comm c (star z),smul_comm c ω]
    abel

end
end KN.Angular
