import KN.ChargedRadial.RayRegularity
import KN.ChargedRadial.ExteriorInjectivity
import KN.Energy.Injectivity
import KN.Analysis.LaplaceCalculus

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial
open KN.Analysis

/-- Vanishing on the physical energy ray kills the actual supported distribution,
by holomorphic continuation and the proved Mathlib Fourier injectivity bridge. -/
theorem physical_distribution_zero_of_ray (b : KN.Background) (omega : ℂ)
    (hw : 0 < omega.im) (T : CDist) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)})
    (htransform : IsFourierLaplaceTransform T (-(b.eta*omega.im)) F)
    (hzero : ∀ x < -b.h, F (omega*(x:ℂ)) = 0) : T = 0 := by
  have hn : omega ≠ 0 := by intro he; simp [he] at hw
  have hall := KN.Energy.holomorphic_zero_of_ray F omega (-b.h)
    (-(b.eta*omega.im)) hn hF (fun x hx => physical_ray_mem b omega hw (by
      dsimp [KN.Background.h] at hx
      linarith)) hzero
  exact KN.Analysis.External.fourier_laplace_unique T 0 (-(b.eta*omega.im))
    F (fun _ => 0) htransform (laplace_zero _) hall

/-- Canonical continuation injectivity for the actual physical ray. -/
theorem physical_nonresonant_exterior_zero (b : KN.Background) (omega alpha : ℂ)
    (hw : 0 < omega.im) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f v : ℝ → ℂ) (hf : Smooth f) (hv : ContinuousOn v (Ioi b.rPlus))
    (he : ∀ t > b.rPlus, v t = ((t-b.rPlus):ℂ)^alpha*f t)
    (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)})
    (htransform : IsFourierLaplaceTransform (finitePartAt b.rPlus alpha f)
      (-(b.eta*omega.im)) F)
    (hzero : ∀ x < -b.h, F (omega*(x:ℂ)) = 0) : EqOn v 0 (Ioi b.rPlus) := by
  exact finitePartAt_exterior_injective b.rPlus alpha ha hne f v hf hv he
    (physical_distribution_zero_of_ray b omega hw _ F hF htransform hzero)

/-- The delta correction cannot hide a nonzero exterior radial function. -/
theorem physical_resonant_exterior_zero (b : KN.Background) (omega coeff : ℂ)
    (hw : 0 < omega.im) (f v : ℝ → ℂ) (hf : Continuous f)
    (he : EqOn f v (Ioi b.rPlus)) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)})
    (htransform : IsFourierLaplaceTransform
      (zeroExtension b.rPlus f+deltaValue b.rPlus coeff) (-(b.eta*omega.im)) F)
    (hzero : ∀ x < -b.h, F (omega*(x:ℂ)) = 0) : EqOn v 0 (Ioi b.rPlus) := by
  have hz := corrected_zeroExtension_exterior_injective b.rPlus f hf coeff
    (physical_distribution_zero_of_ray b omega hw _ F hF htransform hzero)
  exact he.symm.trans hz

end KN.ChargedRadial
