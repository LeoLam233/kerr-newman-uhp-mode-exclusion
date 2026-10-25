import KN.ChargedRadial.FinitePartTransform
import KN.ChargedRadial.CoordinateFinitePart

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
namespace KN.ChargedRadial
open KN.Analysis

lemma radial_factor_derivative (f : ℝ → ℂ) (hf : Differentiable ℝ f) :
    deriv (fun t : ℝ => (t:ℂ)*f t) = fun t => f t+(t:ℂ)*deriv f t := by
  ext t
  have hh := ((hasDerivAt_id t).ofReal_comp.fun_mul (hf t).hasDerivAt).deriv
  simpa only [id_eq, Complex.ofReal_one, one_mul] using hh

/-- Moment L¹ estimates automatically cover the derivative of the new smooth
coefficient r f, as required for applying (48a) to the coordinate multiple. -/
lemma coordinate_factor_damped_integrable (r beta : ℝ) (alpha : ℂ) (f : ℝ → ℂ)
    (hf : Differentiable ℝ f)
    (hi : ∀ j : ℕ, Integrable (dampedPowerFunction r beta (alpha+1) (fun t => f t*(t:ℂ)^j)) ∧
      Integrable (dampedPowerFunction r beta (alpha+1) (fun t => deriv f t*(t:ℂ)^j))) :
    Integrable (dampedPowerFunction r beta (alpha+1) (fun t : ℝ => (t:ℂ)*f t)) ∧
    Integrable (dampedPowerFunction r beta (alpha+1) (deriv (fun t : ℝ => (t:ℂ)*f t))) := by
  constructor
  · simpa only [pow_one, mul_comm] using (hi 1).1
  · rw [radial_factor_derivative f hf]
    convert (hi 0).1.add (hi 1).2 using 1
    ext t
    by_cases ht : t ∈ Ioi r
    · simp only [dampedPowerFunction, Pi.add_apply, indicator_of_mem ht, pow_zero, mul_one, pow_one]
      ring
    · simp [dampedPowerFunction, ht]

/-- The actual canonical transform has the polynomial-exponential bound at
minus infinity. A fixed damping height c-1 is sufficient. -/
theorem finitePart_transform_ray_bound (r c : ℝ) (alpha omega : ℂ) (hw : 0 < omega.im)
    (ha : -2 < alpha.re) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : ∀ beta < c, Integrable (dampedPowerFunction r beta (alpha+1) f) ∧
      Integrable (dampedPowerFunction r beta (alpha+1) (deriv f))) :
    let F := finitePartLaplace r alpha (powerFunction r (alpha+1) f)
      (powerFunction r (alpha+1) (deriv f))
    AnalyticOnNhd ℂ F {z : ℂ | z.im < c} ∧
    IsFourierLaplaceTransform (finitePartAt r alpha f) c F ∧
    (fun x : ℝ => F (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x)) := by
  have ht := finitePartAt_transform r c alpha ha f hf hi
  refine ⟨ht.1,ht.2,?_⟩
  have hb : c-1 < c := by linarith
  exact finitePartLaplace_isBigO r (c-1) alpha omega hw _ _
    ((integrable_indicator_iff measurableSet_Ioi).1 (hi (c-1) hb).1)
    ((integrable_indicator_iff measurableSet_Ioi).1 (hi (c-1) hb).2)

/-- The first complex derivative satisfies the same degree-one bound, by the
actual coordinate multiplication theorem and the first damped moment. -/
theorem finitePart_transform_derivative_ray_bound
    (r c : ℝ) (alpha omega : ℂ) (hw : 0 < omega.im)
    (ha : -2 < alpha.re) (hne : alpha ≠ -1) (f : ℝ → ℂ) (hf : Smooth f)
    (hi : ∀ beta < c, ∀ j : ℕ,
      Integrable (dampedPowerFunction r beta (alpha+1) (fun t => f t*(t:ℂ)^j)) ∧
      Integrable (dampedPowerFunction r beta (alpha+1) (fun t => deriv f t*(t:ℂ)^j))) :
    let F := finitePartLaplace r alpha (powerFunction r (alpha+1) f)
      (powerFunction r (alpha+1) (deriv f))
    (fun x : ℝ => deriv F (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x)) := by
  let F := finitePartLaplace r alpha (powerFunction r (alpha+1) f)
    (powerFunction r (alpha+1) (deriv f))
  let g : ℝ → ℂ := fun t => (t:ℂ)*f t
  have hg : Smooth g := Complex.ofRealCLM.contDiff.mul hf
  have hfi : ∀ beta < c, Integrable (dampedPowerFunction r beta (alpha+1) f) ∧
      Integrable (dampedPowerFunction r beta (alpha+1) (deriv f)) := by
    intro beta hb
    simpa only [pow_zero,mul_one] using hi beta hb 0
  have hgi := fun beta hb => coordinate_factor_damped_integrable r beta alpha f
    (hf.differentiable (by simp)) (hi beta hb)
  have hF := finitePartAt_transform r c alpha ha f (hf.of_le (by simp)) hfi
  have hG := finitePart_transform_ray_bound r c alpha omega hw ha g (hg.of_le (by simp)) hgi
  have hDF := KN.Analysis.External.fourier_laplace_coordinate _ c _ hF.2 hF.1
  rw [coordinate_finitePartAt r alpha ha hne f hf] at hDF
  have he := KN.Analysis.External.fourier_laplace_single_valued _ c _ _ hDF hG.2.1
    (analyticOnNhd_const.mul hF.1.deriv) hG.1
  apply (hG.2.2.const_smul_left (-Complex.I)).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_le_atBot ((c-1)/omega.im)] with x hx
  have hxc : (omega*x).im < c := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    have hh := (le_div_iff₀ hw).mp hx
    nlinarith
  have hh := he (omega*x) hxc
  symm
  change deriv F (omega*x) = -Complex.I*_
  dsimp only
  rw [← hh]
  simp [F, ← mul_assoc]

/-- Actual real differentiation along the complex-frequency ray. -/
lemma laplace_ray_hasDerivAt (c : ℝ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z.im < c}) (omega : ℂ) (x : ℝ)
    (hx : (omega*x).im < c) :
    HasDerivAt (fun t : ℝ => F (omega*t)) (omega*deriv F (omega*x)) x := by
  have h := (hF (omega*x) hx).differentiableAt.hasDerivAt
  have hh := (h.comp (x:ℂ) ((hasDerivAt_id (x:ℂ)).const_mul omega)).comp_ofReal
  convert! hh using 1
  simp [mul_comm]

/-- Complex-derivative estimates give the actual real derivative Y' used in
the transformed ordinary differential equation and energy identity. -/
theorem ray_derivative_isBigO (r c : ℝ) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z.im < c}) (omega : ℂ) (hw : 0 < omega.im)
    (hb : (fun x : ℝ => deriv F (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x))) :
    deriv (fun x : ℝ => F (omega*x)) =O[atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x)) := by
  apply (hb.const_smul_left omega).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_le_atBot ((c-1)/omega.im)] with x hx
  have hxc : (omega*x).im < c := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
    have hh := (le_div_iff₀ hw).mp hx
    nlinarith
  exact (laplace_ray_hasDerivAt c F hF omega x hxc).deriv.symm

end KN.ChargedRadial
