import KN.ChargedRadial.PhysicalTransform
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial

/-- The physical finite endpoint lies strictly inside the holomorphy half-plane. -/
theorem physical_ray_mem (b : KN.Background) (omega : ℂ) (hw : 0 < omega.im)
    {x : ℝ} (hx : x < -b.eta) :
    (omega * (x : ℂ)).im < -(b.eta * omega.im) := by
  simp only [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  nlinarith

/-- Restricting a genuine Fourier--Laplace transform to the physical ray is
real analytic, including a neighborhood of the finite energy endpoint. -/
theorem physical_ray_analyticAt (b : KN.Background) (omega : ℂ) (hw : 0 < omega.im)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)})
    {x : ℝ} (hx : x < -b.eta) :
    AnalyticAt ℝ (fun t : ℝ => F (omega * (t : ℂ))) x := by
  have ho : AnalyticAt ℝ F (omega * (x : ℂ)) :=
    (hF _ (physical_ray_mem b omega hw hx)).restrictScalars
  have hi : AnalyticAt ℝ (fun t : ℝ => omega * (t : ℂ)) x := by
    exact analyticAt_const.mul (Complex.ofRealCLM.analyticAt x)
  exact ho.comp (f := fun t : ℝ => omega * (t : ℂ)) hi

/-- The finite-endpoint continuity hypotheses used by the energy argument
follow from half-plane holomorphy; they are not extra boundary conditions. -/
theorem physical_ray_finite_continuity (b : KN.Background) (omega : ℂ) (hw : 0 < omega.im)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)}) :
    ContinuousAt (fun x : ℝ => F (omega * (x : ℂ))) (-b.h) ∧
    ContinuousAt (deriv (fun x : ℝ => F (omega * (x : ℂ)))) (-b.h) := by
  have hx : -b.h < -b.eta := by dsimp [KN.Background.h]; linarith
  have ha := physical_ray_analyticAt b omega hw F hF hx
  have hc : ContDiffAt ℝ 1 (fun x : ℝ => F (omega * (x : ℂ))) (-b.h) := ha.contDiffAt
  exact ⟨ha.continuousAt, (hc.derivWithin (m := 0) (by norm_num)).continuousAt⟩

/-- All real-ray regularity needed for integration by parts follows locally
from holomorphy, with no global differentiability of the transform assumed. -/
theorem physical_ray_differentiable (b : KN.Background) (omega : ℂ) (hw : 0 < omega.im)
    (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)}) :
    (∀ x < -b.h, HasDerivAt (fun t : ℝ => F (omega*(t:ℂ)))
      (deriv (fun t : ℝ => F (omega*(t:ℂ))) x) x) ∧
    ContinuousOn (deriv (fun t : ℝ => F (omega*(t:ℂ)))) (Iio (-b.h)) := by
  have ha : ∀ x < -b.h, AnalyticAt ℝ (fun t : ℝ => F (omega*(t:ℂ))) x := by
    intro x hx
    apply physical_ray_analyticAt b omega hw F hF
    dsimp [KN.Background.h] at hx
    linarith
  constructor
  · intro x hx
    exact (ha x hx).differentiableAt.hasDerivAt
  · intro x hx
    have hc : ContDiffAt ℝ 1 (fun t : ℝ => F (omega*(t:ℂ))) x := (ha x hx).contDiffAt
    exact (hc.derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

theorem physical_ray_deriv_differentiableOn (b : KN.Background) (omega : ℂ)
    (hw : 0 < omega.im) (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)}) :
    DifferentiableOn ℝ (deriv (fun t : ℝ => F (omega*(t:ℂ)))) (Iio (-b.h)) := by
  intro x hx
  have ha := physical_ray_analyticAt b omega hw F hF (show x < -b.eta by
    change x < -(b.eta+2) at hx
    linarith)
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => F (omega*(t:ℂ))) x := ha.contDiffAt
  exact ((hc.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).differentiableWithinAt

end KN.ChargedRadial
