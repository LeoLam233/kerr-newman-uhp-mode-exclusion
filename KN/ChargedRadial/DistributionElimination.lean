import KN.ChargedRadial.DistributionAlgebra
import KN.ChargedRadial.Elimination

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Distributions ContDiff
namespace KN.ChargedRadial

/-- The general common-slope affine elimination identity on ordinary distributions. -/
theorem distribution_affine_elimination
    (A B : ℝ → ℂ) (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (u : ℂ) (hDA : deriv A = fun _ => u) (hDB : deriv B = fun _ => u)
    (T v z : CDist)
    (hfirst : T = mulComplexDist A hA z)
    (hsecond : (Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) z = mulComplexDist B hB v) :
    (Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) T) -
      mulComplexDist (fun r => A r*B r) (hA.mul hB) ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) v) -
      mulComplexDist (fun r => (2*B r+A r)*u) ((contDiff_const.mul hB).add hA |>.mul contDiff_const) v = 0 := by
  have hD (S : CDist) : (Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) (mulComplexDist A hA S) =
      mulComplexDist A hA ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) S) + u • S := by
    rw [derivative_mulComplexDist, mulComplexDist_congr _ _ _ contDiff_const hDA, mulComplexDist_const]
  have hE (S : CDist) : (Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) (mulComplexDist B hB S) =
      mulComplexDist B hB ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) S) + u • S := by
    rw [derivative_mulComplexDist, mulComplexDist_congr _ _ _ contDiff_const hDB, mulComplexDist_const]
  rw [hfirst, hD, map_add, derivative_complex_smul, hsecond, hD, hE, map_add,
    mulComplexDist_complex_smul, mulComplexDist_comp, mulComplexDist_mul_const,
    mulComplexDist_add_fun, mulComplexDist_const_mul]
  module
  all_goals fun_prop

/-- C002 (29) on genuine complex distributions, with no division by either
coupling and therefore valid at every zero of A or B. -/
theorem distribution_division_free_third_order
    (u b s lam : ℂ) (hs : s = 1 ∨ s = -1)
    (Delta L : ℝ → ℂ) (hDelta : ContDiff ℝ ∞ Delta) (hL : ContDiff ℝ ∞ L)
    (v z : CDist)
    (hfirst : mulComplexDist Delta hDelta ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) v) + mulComplexDist L hL v =
      mulComplexDist (couplingA u b s lam) (by unfold couplingA radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop) z)
    (hsecond : (Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) z =
      mulComplexDist (couplingB u b s lam) (by unfold couplingB radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop) v) :
    (Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist)
      (mulComplexDist Delta hDelta ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) v) + mulComplexDist L hL v)) -
      mulComplexDist (fun r => radialAffine u b r ^ 2 + lam ^ 2)
        (by unfold radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop) ((Distribution.lineDerivCLM (1:ℝ) : CDist →L[ℝ] CDist) v) -
      mulComplexDist (fun r => (3 * radialAffine u b r - Complex.I * s * lam) * u)
        (by unfold radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop) v = 0 := by
  have hA : ContDiff ℝ ∞ (couplingA u b s lam) := by unfold couplingA radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop
  have hB : ContDiff ℝ ∞ (couplingB u b s lam) := by unfold couplingB radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop
  have hDA : deriv (couplingA u b s lam) = fun _ => u := funext (fun r => (couplingA_hasDerivAt u b s lam r).deriv)
  have hDB : deriv (couplingB u b s lam) = fun _ => u := funext (fun r => (couplingB_hasDerivAt u b s lam r).deriv)
  have h := distribution_affine_elimination (couplingA u b s lam) (couplingB u b s lam) hA hB u hDA hDB
    _ v z hfirst hsecond
  have hprod : (fun r => couplingA u b s lam r * couplingB u b s lam r) =
      fun r => radialAffine u b r^2+lam^2 := funext (coupling_product u b s lam hs)
  have hcoeff : (fun r => (2*couplingB u b s lam r+couplingA u b s lam r)*u) =
      fun r => (3*radialAffine u b r-Complex.I*s*lam)*u := by
    funext r
    unfold couplingA couplingB
    ring
  rwa [mulComplexDist_congr _ _ _ (by unfold radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop) hprod,
    mulComplexDist_congr _ _ _ (by unfold radialAffine; have hc : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff; fun_prop) hcoeff] at h

end KN.ChargedRadial
