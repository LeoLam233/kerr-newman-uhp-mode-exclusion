import KN.ChargedRadial.LaplaceAdmissibility
import KN.ChargedRadial.ExceptionalPair

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace KN.ChargedRadial
open KN.Analysis

lemma damped_add_matches (T S : CDist) (beta : ℝ)
    (U V : TemperedDistribution ℝ ℂ)
    (hU : DampedMatches T beta U) (hV : DampedMatches S beta V) :
    DampedMatches (T+S) beta (U+V) := by
  intro phi
  change U (testSchwartz phi)+V (testSchwartz phi) =
    T (mulTest (damping beta) (damping_smooth beta) phi)+
    S (mulTest (damping beta) (damping_smooth beta) phi)
  rw [hU,hV]
  rfl

/-- A point source is exponentially tempered at every damping height, with
its exact coefficient. -/
lemma damped_delta_matches (r beta : ℝ) (c : ℂ) :
    DampedMatches (deltaValue r c) beta
      (((Real.exp (beta*r):ℂ)*c) • TemperedDistribution.delta r) := by
  intro phi
  change ((Real.exp (beta*r):ℂ)*c)*(phi r:ℂ) = (phi r*Real.exp (beta*r)) • c
  rw [Complex.real_smul, Complex.ofReal_mul]
  ring

lemma regularPowerAt_zero (r : ℝ) (f : ℝ → ℂ) :
    regularPowerAt r 0 f = zeroExtension r f := by
  simp [regularPowerAt, zeroExtension]

/-- The exceptional smooth extension plus its forced delta correction is an
actual Laplace-admissible distribution whenever the outgoing smooth component
has the corresponding damped L¹ bounds. -/
theorem corrected_zeroExtension_laplaceAdmissible (r c : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (coeff : ℂ)
    (hi : ∀ beta < c, IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*f t) (Ioi r)) :
    LaplaceAdmissible r c (zeroExtension r f+deltaValue r coeff) := by
  refine ⟨corrected_zeroExtension_support r f hf coeff, ?_⟩
  intro beta hb
  have hi' : Integrable (dampedPowerFunction r beta 0 f) := by
    simpa [dampedPowerFunction] using (integrable_indicator_iff measurableSet_Ioi).2 (hi beta hb)
  have hmatch := damped_regularPower_matches r beta 0 (by norm_num) f hf hi'
  rw [regularPowerAt_zero] at hmatch
  exact ⟨_, damped_add_matches _ _ beta _ _ hmatch (damped_delta_matches r beta coeff)⟩

end KN.ChargedRadial
