import KN.ChargedRadial.ExceptionalTransform
import KN.Energy.PhysicalAdmissibility

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
namespace KN.ChargedRadial
open KN.Analysis KN.Boundary KN.Energy

/-- The ordinary smooth representative in the exceptional correction has every
damped moment integrable, directly from the original outgoing conormal class. -/
theorem physical_smooth_extension_damped_moments
    (b : KN.Background) (m : ℤ) (omega : ℂ) (sigma : ℝ) (hsigma : sigma=1 ∨ sigma= -1)
    (w z f : ℝ → ℂ) (hf : Continuous f)
    (hrescale : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m omega (3*sigma/4) r*z r)
    (he : ∀ r ∈ Ioi b.rPlus,
      f r=radialMultiplier b m omega (-(1+3*sigma)/2) r*w r)
    (hout : PolynomialConormal (fun r => gauge b m omega r*z r))
    (beta : ℝ) (hb : beta < -(b.eta*omega.im)) (j : ℕ) :
    IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*(f t*(t:ℂ)^j)) (Ioi b.rPlus) := by
  let U := fun r => gauge b m omega r*z r
  have hq : -(1+3*sigma)/2+3*sigma/4 ≤ 1 := by
    rcases hsigma with rfl|rfl <;> norm_num
  have hgrowth : ExpPolyGrowth (b.eta*omega.im) f := by
    apply (outgoingTail_expPolyGrowth b omega (-(1+3*sigma)/2+3*sigma/4) hq U hout).congr
    filter_upwards [eventually_gt_atTop b.rPlus] with r hr
    rw [he r hr,hrescale r hr]
    dsimp [outgoingTail,U]
    simp only [← mul_assoc]
    rw [multiplier_rescale_identity b m omega (-(1+3*sigma)/2) (3*sigma/4) hr]
    rfl
  have hm : PolyBound (fun t : ℝ => (t:ℂ)^j) :=
    (polynomialConormal_pow 0 (fun t : ℝ => (t:ℂ))
      Complex.ofRealCLM.contDiff.contDiffOn polynomialConormal_coordinate j) 0
  have hdamp := expPolyGrowth_damping (hgrowth.mul_poly hm) beta (by linarith)
  have hi := dampedPower_integrable_of_exp_bound b.rPlus beta (-(beta+b.eta*omega.im)/2)
    (by linarith) 0 (by norm_num) (fun t : ℝ => f t*(t:ℂ)^j)
    (hf.mul (Complex.continuous_ofReal.pow j)) (by
      simpa only [Complex.cpow_zero,one_mul,neg_div,neg_neg] using hdamp)
  have hh := (integrable_indicator_iff measurableSet_Ioi).1 hi
  simpa only [Complex.cpow_zero,one_mul] using hh

/-- The exceptional corrected transform has analytic continuation and both
actual real-ray endpoint bounds, with no extra growth hypotheses. -/
theorem physical_exceptional_transform_bounds
    (b : KN.Background) (m : ℤ) (omega : ℂ) (hw : 0 < omega.im)
    (sigma : ℝ) (hsigma : sigma=1 ∨ sigma= -1) (w z f : ℝ → ℂ)
    (hf : Continuous f) (coeff : ℂ)
    (hrescale : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m omega (3*sigma/4) r*z r)
    (he : ∀ r ∈ Ioi b.rPlus,
      f r=radialMultiplier b m omega (-(1+3*sigma)/2) r*w r)
    (hout : PolynomialConormal (fun r => gauge b m omega r*z r)) :
    AnalyticOnNhd ℂ (correctedLaplace b.rPlus f coeff) {xi : ℂ | xi.im < -(b.eta*omega.im)} ∧
    IsFourierLaplaceTransform (zeroExtension b.rPlus f+deltaValue b.rPlus coeff)
      (-(b.eta*omega.im)) (correctedLaplace b.rPlus f coeff) ∧
    (fun x : ℝ => correctedLaplace b.rPlus f coeff (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*b.rPlus*x)) ∧
    deriv (fun x : ℝ => correctedLaplace b.rPlus f coeff (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*b.rPlus*x)) := by
  exact corrected_zeroExtension_transform_bounds b.rPlus (-(b.eta*omega.im)) f hf coeff omega hw
    (physical_smooth_extension_damped_moments b m omega sigma hsigma w z f hf hrescale he hout)

end KN.ChargedRadial
