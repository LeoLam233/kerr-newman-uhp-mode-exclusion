import KN.Kerr.NegativeHorizon
import KN.Kerr.WhitingInterface
import KN.Kerr.GaugeConjugation

namespace KN.Kerr
open Set Filter
open scoped Topology ContDiff

/-- Converts weighted-smooth negative-spin horizon data to the precise classical
non-special branch. The proof uses only general Fuchs theory and verified Kerr
indicial coefficients; it does not assume a nonzero horizon coefficient. -/
theorem negative_horizon_to_non_special
    (b : KN.Background) (m s : ℤ) (omega Λ : ℂ)
    (hs : s = -1 ∨ s = -2) (homega : 0 < omega.im)
    (R f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (heq : ConjugatedEquation b m omega Λ s f)
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r)
    (hne : ∃ r ∈ Ioi b.rPlus, R r ≠ 0) :
    NonSpecialIngoing b m s omega R := by
  have hsneg : (s : ℝ) < 0 := by rcases hs with rfl | rfl <;> norm_num
  have hfne : ∃ r ∈ Ici b.rPlus, f r ≠ 0 := by
    obtain ⟨r, hr, hnr⟩ := hne
    refine ⟨r, ?_, ?_⟩
    · exact le_of_lt (show b.rPlus < r from hr)
    · intro hzero
      apply hnr
      rw [hrep r hr, hzero, mul_zero]
  obtain ⟨g, hg, hfg, hgnz⟩ :=
    negative_horizon_analytic_nonzero b m omega Λ s hsneg homega f hf heq hfne
  refine ⟨g, hg, hgnz, ?_⟩
  have hfg' : f =ᶠ[𝓝[>] b.rPlus] g :=
    hfg.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)
  filter_upwards [hfg', self_mem_nhdsWithin] with r hfg hr
  rw [hrep r hr, hfg]
  rfl

/-- Negative-spin exclusion once the actual conjugation bridge has supplied (53).
The physical equation is retained explicitly; this is not yet the full Kerr theorem. -/
theorem negative_exclusion_of_conjugated_equation
    (b : KN.Background) (hQ : b.Q = 0) (m s : ℤ) (omega Λ : ℂ)
    (hs : s = -1 ∨ s = -2) (homega : 0 < omega.im)
    (u R f : ℝ → ℂ)
    (hu : RegularAngularEigenfunction b m s omega Λ u)
    (hR : ContDiffOn ℝ ∞ R (Ioi b.rPlus))
    (hphysical : PhysicalRadialEquation b m omega Λ s R)
    (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (heq : ConjugatedEquation b m omega Λ s f)
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r)
    (hout : KN.Boundary.Outgoing b m omega R) :
    ∀ r ∈ Ioi b.rPlus, R r = 0 := by
  by_contra hnonzero
  push Not at hnonzero
  have hhor := negative_horizon_to_non_special b m s omega Λ hs homega R f hf heq hrep hnonzero
  have hzero := External.whiting_negative_spin_non_special b hQ m s hs omega Λ homega u R
    hu hR hphysical hhor hout
  obtain ⟨r, hr, hnr⟩ := hnonzero
  exact hnr (hzero r hr)

end KN.Kerr
