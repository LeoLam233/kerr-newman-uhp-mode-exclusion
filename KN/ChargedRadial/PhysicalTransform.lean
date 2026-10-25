import KN.ChargedRadial.TransformEndpointBounds
import KN.Energy.PhysicalAdmissibility

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
namespace KN.ChargedRadial
open KN.Analysis KN.Boundary KN.Energy

/-- Concrete transform and both endpoint estimates from the original outgoing
conormal condition and exact horizon factor, for either physical chirality.
No transform bound or exponential-temperedness condition is assumed. -/
theorem physical_nonresonant_transform_bounds
    (b : KN.Background) (m : ℤ) (omega : ℂ) (hw : 0 < omega.im)
    (sigma : ℝ) (hsigma : sigma=1 ∨ sigma= -1) (w z f : ℝ → ℂ)
    (hf : Smooth f)
    (hrescale : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m omega (3*sigma/4) r*z r)
    (hfactor : ∀ r ∈ Ioi b.rPlus,
      radialMultiplier b m omega (-(1+3*sigma)/2) r*w r =
        ((r-b.rPlus:ℝ):ℂ)^(horizonAlpha b m omega sigma)*f r)
    (hsmooth : ExteriorSmooth b.rPlus (fun r => gauge b m omega r*z r))
    (hout : PolynomialConormal (fun r => gauge b m omega r*z r))
    (hne : horizonAlpha b m omega sigma ≠ -1) :
    let alpha := horizonAlpha b m omega sigma
    let F := finitePartLaplace b.rPlus alpha (powerFunction b.rPlus (alpha+1) f)
      (powerFunction b.rPlus (alpha+1) (deriv f))
    AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)} ∧
    IsFourierLaplaceTransform (finitePartAt b.rPlus alpha f) (-(b.eta*omega.im)) F ∧
    (fun x : ℝ => F (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*b.rPlus*x)) ∧
    deriv (fun x : ℝ => F (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*b.rPlus*x)) := by
  have hq : -(1+3*sigma)/2+3*sigma/4 ≤ 1 := by
    rcases hsigma with rfl|rfl <;> norm_num
  have ha : -2 < (horizonAlpha b m omega sigma).re := by
    rcases hsigma with rfl|rfl
    · exact horizonAlpha_positive_gt_neg_two b m omega hw
    · linarith [horizonAlpha_negative_gt_one b m omega hw]
  have hi := fun beta hb j => KN.Energy.multiplier_rescaled_damped_integrable b m omega
    (-(1+3*sigma)/2) (3*sigma/4) hq w z f (horizonAlpha b m omega sigma) ha
    (hf.of_le (by simp)) hrescale hfactor hsmooth hout beta hb j
  have hi0 : ∀ beta < -(b.eta*omega.im),
      Integrable (dampedPowerFunction b.rPlus beta (horizonAlpha b m omega sigma+1) f) ∧
      Integrable (dampedPowerFunction b.rPlus beta (horizonAlpha b m omega sigma+1) (deriv f)) := by
    intro beta hb
    simpa only [pow_zero,mul_one] using hi beta hb 0
  have hF := finitePart_transform_ray_bound b.rPlus (-(b.eta*omega.im))
    (horizonAlpha b m omega sigma) omega hw ha f (hf.of_le (by simp)) hi0
  refine ⟨hF.1,hF.2.1,hF.2.2,?_⟩
  apply ray_derivative_isBigO b.rPlus (-(b.eta*omega.im)) _ hF.1 omega hw
  exact finitePart_transform_derivative_ray_bound b.rPlus (-(b.eta*omega.im))
    (horizonAlpha b m omega sigma) omega hw ha hne f hf hi

end KN.ChargedRadial
