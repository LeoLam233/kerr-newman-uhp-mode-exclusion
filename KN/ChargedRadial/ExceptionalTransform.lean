import KN.ChargedRadial.DeltaTransform
import KN.ChargedRadial.TransformEndpointBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
namespace KN.ChargedRadial
open KN.Analysis

def correctedLaplace (r : ℝ) (f : ℝ → ℂ) (coeff : ℂ) (xi : ℂ) : ℂ :=
  laplaceIntegral r f xi+deltaLaplace r coeff xi

theorem corrected_zeroExtension_transform (r c : ℝ) (f : ℝ → ℂ)
    (hf : Continuous f) (coeff : ℂ)
    (hi : ∀ beta < c, IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*f t) (Ioi r)) :
    AnalyticOnNhd ℂ (correctedLaplace r f coeff) {z : ℂ | z.im < c} ∧
    IsFourierLaplaceTransform (zeroExtension r f+deltaValue r coeff) c (correctedLaplace r f coeff) := by
  have hh := KN.Analysis.External.fourier_laplace_regular_integral r c f
    (hf.locallyIntegrable.mono_measure Measure.restrict_le_self) hi
  exact ⟨hh.1.add (deltaLaplace_analytic r coeff c),hh.2.add (deltaValue_transform r coeff c)⟩

theorem correctedLaplace_isBigO (r beta : ℝ) (f : ℝ → ℂ) (coeff omega : ℂ)
    (hw : 0 < omega.im)
    (hi : IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*f t) (Ioi r)) :
    (fun x : ℝ => correctedLaplace r f coeff (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x)) := by
  apply Asymptotics.IsBigO.of_bound (laplaceNormConstant r beta f+‖coeff‖)
  filter_upwards [eventually_le_atBot (beta/omega.im)] with x hx
  have hxi : omega.im*x ≤ beta := by
    have hh := (le_div_iff₀ hw).mp hx
    nlinarith
  have hh := laplace_ray_norm_bound r beta f omega x hxi hi
  change ‖laplaceIntegral r f (omega*x)‖ ≤ laplaceNormConstant r beta f*Real.exp (omega.im*r*x) at hh
  have hd : ‖deltaLaplace r coeff (omega*x)‖ = ‖coeff‖*Real.exp (omega.im*r*x) := by
    rw [deltaLaplace, norm_mul, laplaceKernel_norm]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    congr 2
    ring
  have hb := norm_add_le (laplaceIntegral r f (omega*x)) (deltaLaplace r coeff (omega*x))
  rw [hd] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
  change ‖laplaceIntegral r f (omega*x)+deltaLaplace r coeff (omega*x)‖ ≤ _
  nlinarith [mul_nonneg (laplaceNormConstant_nonneg r beta f)
    (mul_nonneg (abs_nonneg x) (Real.exp_pos (omega.im*r*x)).le),
    mul_nonneg (norm_nonneg coeff) (mul_nonneg (abs_nonneg x) (Real.exp_pos (omega.im*r*x)).le)]

lemma coordinate_corrected_zeroExtension (r : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (coeff : ℂ) :
    coordinateMultiply (zeroExtension r f+deltaValue r coeff) =
      zeroExtension r (fun t : ℝ => (t:ℂ)*f t)+deltaValue r ((r:ℂ)*coeff) := by
  rw [coordinateMultiply_eq_complex, map_add, mulComplexDist_zeroExtension r f
    (fun t : ℝ => (t:ℂ)) hf Complex.ofRealCLM.contDiff,
    mulComplexDist_deltaValue]

/-- Both ray estimates for the exceptional smooth-plus-delta extension follow
from ordinary damped moments and the exact delta transform. -/
theorem corrected_zeroExtension_transform_bounds
    (r c : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (coeff omega : ℂ) (hw : 0 < omega.im)
    (hi : ∀ beta < c, ∀ j : ℕ,
      IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*(f t*(t:ℂ)^j)) (Ioi r)) :
    AnalyticOnNhd ℂ (correctedLaplace r f coeff) {z : ℂ | z.im < c} ∧
    IsFourierLaplaceTransform (zeroExtension r f+deltaValue r coeff) c (correctedLaplace r f coeff) ∧
    (fun x : ℝ => correctedLaplace r f coeff (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x)) ∧
    deriv (fun x : ℝ => correctedLaplace r f coeff (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x)) := by
  have hi0 : ∀ beta < c,
      IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*f t) (Ioi r) := by
    intro beta hb
    simpa only [pow_zero,mul_one] using hi beta hb 0
  have hi1 : ∀ beta < c,
      IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*((t:ℂ)*f t)) (Ioi r) := by
    intro beta hb
    convert hi beta hb 1 using 1
    ext t
    simp only [pow_one]
    ring
  have hg : Continuous (fun t : ℝ => (t:ℂ)*f t) := Complex.continuous_ofReal.mul hf
  have hF := corrected_zeroExtension_transform r c f hf coeff hi0
  have hG := corrected_zeroExtension_transform r c _ hg ((r:ℂ)*coeff) hi1
  have hb : c-1 < c := by linarith
  refine ⟨hF.1,hF.2,correctedLaplace_isBigO r (c-1) f coeff omega hw (hi0 _ hb),?_⟩
  apply ray_derivative_isBigO r c _ hF.1 omega hw
  have hDF := KN.Analysis.External.fourier_laplace_coordinate _ c _ hF.2 hF.1
  rw [coordinate_corrected_zeroExtension r f hf coeff] at hDF
  have he := KN.Analysis.External.fourier_laplace_single_valued _ c _ _ hDF hG.2
    (analyticOnNhd_const.mul hF.1.deriv) hG.1
  have hgrowth := correctedLaplace_isBigO r (c-1) _ ((r:ℂ)*coeff) omega hw (hi1 _ hb)
  apply (hgrowth.const_smul_left (-Complex.I)).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_le_atBot ((c-1)/omega.im)] with x hx
  have hxc : (omega*x).im < c := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    have hh := (le_div_iff₀ hw).mp hx
    nlinarith
  have hh := he (omega*x) hxc
  change -Complex.I*correctedLaplace r (fun t : ℝ => (t:ℂ)*f t) ((r:ℂ)*coeff) (omega*x) = _
  rw [← hh]
  simp [← mul_assoc]

end KN.ChargedRadial
