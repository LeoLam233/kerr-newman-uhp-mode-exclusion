import KN.ChargedRadial.LaplaceBounds
import KN.Analysis.LaplaceCalculus

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace KN.ChargedRadial
open KN.Analysis

def powerFunction (r : ℝ) (alpha : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => ((t-r):ℂ)^alpha*f t

/-- The actual ordinary Laplace integral of each locally integrable term in
(48a) represents its actual regular distribution. -/
theorem regularPowerAt_transform (r c : ℝ) (alpha : ℂ) (ha : -1 < alpha.re)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hi : ∀ beta < c, Integrable (dampedPowerFunction r beta alpha f)) :
    AnalyticOnNhd ℂ (laplaceIntegral r (powerFunction r alpha f)) {z : ℂ | z.im < c} ∧
    IsFourierLaplaceTransform (regularPowerAt r alpha f) c
      (laplaceIntegral r (powerFunction r alpha f)) := by
  have hl := ((shifted_cpow_locallyIntegrable r alpha ha).mul_continuous hf).mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioi r))
  exact KN.Analysis.External.fourier_laplace_regular_integral r c (powerFunction r alpha f) hl
    (fun beta hb => (integrable_indicator_iff measurableSet_Ioi).1 (hi beta hb))

/-- Formula (48a) yields an explicit analytic transform, not merely an abstract
holomorphic function with an unproved endpoint estimate. -/
theorem finitePartAt_transform (r c : ℝ) (alpha : ℂ) (ha : -2 < alpha.re)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : ∀ beta < c,
      Integrable (dampedPowerFunction r beta (alpha+1) f) ∧
      Integrable (dampedPowerFunction r beta (alpha+1) (deriv f))) :
    let F := finitePartLaplace r alpha (powerFunction r (alpha+1) f)
      (powerFunction r (alpha+1) (deriv f))
    AnalyticOnNhd ℂ F {z : ℂ | z.im < c} ∧
      IsFourierLaplaceTransform (finitePartAt r alpha f) c F := by
  have ha' : -1 < (alpha+1).re := by simpa using (show -1 < alpha.re+1 by linarith)
  have h1 := regularPowerAt_transform r c (alpha+1) ha' f hf.continuous (fun b hb => (hi b hb).1)
  have h2 := regularPowerAt_transform r c (alpha+1) ha' (deriv f)
    (hf.continuous_deriv le_rfl) (fun b hb => (hi b hb).2)
  constructor
  · exact analyticOnNhd_const.mul
      (((analyticOnNhd_const.mul analyticOnNhd_id).mul h1.1).sub h2.1)
  · have hd := KN.Analysis.External.fourier_laplace_derivative _ c _ h1.2
    have hh := (hd.add (h2.2.smul (-1))).smul ((alpha+1)⁻¹)
    convert hh using 1
    · unfold finitePartAt
      congr 1
      module
    · funext z
      unfold finitePartLaplace
      ring

end KN.ChargedRadial
