import KN.ChargedRadial.ExceptionalAdmissibility
import KN.ChargedRadial.LaplaceBounds
import KN.Analysis.LaplaceCalculus

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped FourierTransform SchwartzMap
namespace KN.ChargedRadial
open KN.Analysis

def deltaLaplace (r : ℝ) (coeff : ℂ) (xi : ℂ) : ℂ :=
  coeff*Complex.exp (-Complex.I*xi*r)

lemma deltaLaplace_analytic (r : ℝ) (coeff : ℂ) (c : ℝ) :
    AnalyticOnNhd ℂ (deltaLaplace r coeff) {z : ℂ | z.im < c} := by
  exact analyticOnNhd_const.mul
    (((analyticOnNhd_const.mul analyticOnNhd_id).mul analyticOnNhd_const).cexp)

lemma deltaLaplace_horizontal (r beta x : ℝ) (coeff : ℂ) :
    deltaLaplace r coeff ((2*Real.pi*x:ℝ)+Complex.I*beta) =
      ((Real.exp (beta*r):ℂ)*coeff)*Complex.exp (((-2*Real.pi*(x*r):ℝ):ℂ)*Complex.I) := by
  unfold deltaLaplace
  have he : -Complex.I*((2*Real.pi*x:ℝ)+Complex.I*beta)*(r:ℂ) =
      (beta*r:ℝ)+(((-2*Real.pi*(x*r):ℝ):ℂ)*Complex.I) := by
    push_cast
    linear_combination -(beta:ℂ)*(r:ℂ)*Complex.I_sq
  rw [he, Complex.exp_add, Complex.ofReal_exp]
  ring

/-- The delta's Fourier–Laplace transform is proved from the actual Mathlib
Schwartz Fourier integral and point evaluation, not supplied as an interface. -/
theorem deltaValue_transform (r : ℝ) (coeff : ℂ) (c : ℝ) :
    IsFourierLaplaceTransform (deltaValue r coeff) c (deltaLaplace r coeff) := by
  intro beta hb
  refine ⟨((Real.exp (beta*r):ℂ)*coeff) • TemperedDistribution.delta r,
    damped_delta_matches r beta coeff, ?_⟩
  intro phi
  have hphase : Integrable (fun x : ℝ =>
      Complex.exp (((-2*Real.pi*(x*r):ℝ):ℂ)*Complex.I)*phi x) := by
    apply phi.integrable.bdd_mul (c := 1)
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · apply Filter.Eventually.of_forall
      intro x
      rw [Complex.norm_exp]
      simp
  constructor
  · simp_rw [deltaLaplace_horizontal, mul_assoc]
    simpa only [mul_assoc] using hphase.const_mul ((Real.exp (beta*r):ℂ)*coeff)
  · rw [TemperedDistribution.fourier_apply]
    change ((Real.exp (beta*r):ℂ)*coeff)*(𝓕 phi) r = _
    rw [SchwartzMap.fourier_coe, Real.fourier_eq']
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [deltaLaplace_horizontal]
    simp only [smul_eq_mul, RCLike.inner_apply, conj_trivial]
    ring

end KN.ChargedRadial
