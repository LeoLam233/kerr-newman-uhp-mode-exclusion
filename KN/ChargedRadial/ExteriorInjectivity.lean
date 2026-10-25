import KN.ChargedRadial.CanonicalInterface
import KN.ChargedRadial.ExceptionalPair
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

/-- Actual compact-test detection on the exterior, followed by the continuity
upgrade from almost-everywhere equality to pointwise equality. -/
theorem exterior_zero_of_test_pairings (r : ℝ) (v : ℝ → ℂ)
    (hv : ContinuousOn v (Ioi r))
    (htest : ∀ phi : 𝓓((⊤ : Opens ℝ), ℝ), tsupport phi ⊆ Ioi r →
      (∫ t in Ioi r, phi t • v t) = 0) : EqOn v 0 (Ioi r) := by
  have hae := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hv.locallyIntegrableOn measurableSet_Ioi) (fun phi hp hc hs => by
      let p : 𝓓((⊤ : Opens ℝ), ℝ) := ⟨phi, hp, hc, by simp⟩
      have hh := htest p hs
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hh
      · exact hh
      · intro t ht
        rw [show p t = 0 from image_eq_zero_of_notMem_tsupport (fun hh => ht (hs hh))]
        exact zero_smul _ _)
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' measurableSet_Ioi).2 hae)
    isOpen_Ioi hv continuousOn_const

/-- Vanishing of the canonical supported extension forces the original radial
function to vanish on the entire exterior. -/
theorem finitePartAt_exterior_injective (r : ℝ) (alpha : ℂ)
    (ha : -2 < alpha.re) (hne : alpha ≠ -1) (f v : ℝ → ℂ)
    (hf : Smooth f) (hv : ContinuousOn v (Ioi r))
    (he : ∀ t > r, v t = ((t-r):ℂ)^alpha*f t)
    (hzero : finitePartAt r alpha f = 0) : EqOn v 0 (Ioi r) := by
  apply exterior_zero_of_test_pairings r v hv
  intro phi hphi
  have hh := External.canonical_power_calculus.agrees r alpha ha hne f hf phi hphi
  rw [hzero] at hh
  have hi : (∫ t in Ioi r, phi t • v t) =
      ∫ t in Ioi r, phi t • (((t-r):ℂ)^alpha*f t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [he t ht]
  rw [hi]
  exact hh.symm

/-- The delta correction is invisible to tests strictly inside the exterior;
its vanishing therefore also forces the original smooth component to vanish. -/
theorem corrected_zeroExtension_exterior_injective (r : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (c : ℂ)
    (hzero : zeroExtension r f+deltaValue r c = 0) : EqOn f 0 (Ioi r) := by
  apply exterior_zero_of_test_pairings r f hf.continuousOn
  intro phi hphi
  have hh := congrArg (fun T : CDist => T phi) hzero
  change zeroExtension r f phi+deltaValue r c phi = 0 at hh
  rw [zeroExtension_apply r f hf, deltaValue_apply] at hh
  have hp : phi r = 0 := image_eq_zero_of_notMem_tsupport
    (fun hh => (lt_irrefl r) (hphi hh))
  simpa only [hp, zero_smul, add_zero] using hh

end KN.ChargedRadial
