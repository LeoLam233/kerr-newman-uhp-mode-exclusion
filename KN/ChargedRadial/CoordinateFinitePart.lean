import KN.ChargedRadial.CanonicalInterface
import KN.ChargedRadial.DistributionAlgebra
import KN.Analysis.LaplaceInterface

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

lemma coordinateMultiply_eq_complex (T : CDist) :
    KN.Analysis.coordinateMultiply T =
      mulComplexDist (fun t : ℝ => (t:ℂ)) Complex.ofRealCLM.contDiff T := by
  unfold mulComplexDist KN.Analysis.coordinateMultiply
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  change mulDist (fun t : ℝ => t) contDiff_id T =
    mulDist (fun t : ℝ => t) contDiff_id T+Complex.I •
      mulDist (fun _ : ℝ => 0) contDiff_const T
  rw [mulDist_const]
  ext phi
  change T (mulTest (fun t : ℝ => t) contDiff_id phi) =
    T (mulTest (fun t : ℝ => t) contDiff_id phi)+Complex.I*((0:ℝ) • T phi)
  simp

/-- Multiplying the concrete canonical extension by the physical radial
coordinate remains the same finite-part construction with coefficient r f.
This gives derivative bounds for the transform via its general coordinate rule. -/
theorem coordinate_finitePartAt (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re)
    (hne : alpha ≠ -1) (f : ℝ → ℂ) (hf : Smooth f) :
    KN.Analysis.coordinateMultiply (finitePartAt r alpha f) =
      finitePartAt r alpha (fun t : ℝ => (t:ℂ)*f t) := by
  rw [coordinateMultiply_eq_complex]
  exact External.canonical_power_calculus.mul r alpha ha hne f
    (fun t : ℝ => (t:ℂ)) hf Complex.ofRealCLM.contDiff

end KN.ChargedRadial
