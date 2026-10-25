import KN.ChargedRadial.DistributionMultiplication
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Distributions ContDiff
namespace KN.ChargedRadial

/-- Leibniz rule on the LF space of ordinary distributions. -/
theorem derivative_mulDist (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (T : CDist) :
    Distribution.lineDerivCLM (1:ℝ) (mulDist g hg T) =
      mulDist g hg (Distribution.lineDerivCLM (1:ℝ) T) +
      mulDist (deriv g) (contDiff_infty_iff_deriv.mp hg).2 T := by
  ext phi
  have ht : TestFunction.lineDerivCLM ℝ (1:ℝ) (mulTest g hg phi) =
      mulTest g hg (TestFunction.lineDerivCLM ℝ (1:ℝ) phi) +
      mulTest (deriv g) (contDiff_infty_iff_deriv.mp hg).2 phi := by
    ext r
    simp only [FunLike.coe_add, Pi.add_apply, mulTest_apply]
    rw [testFunction_deriv, testFunction_deriv]
    change deriv ((phi : ℝ → ℝ) * g) r = _
    exact deriv_mul (phi.contDiff.differentiable (by simp) r) (hg.differentiable (by simp) r)
  simp only [Distribution.lineDerivCLM_apply, mulDist_apply]
  have h := congrArg (fun q => T q) ht
  simp only [map_add] at h
  change -T (mulTest g hg (TestFunction.lineDerivCLM ℝ (1:ℝ) phi)) =
    -T (TestFunction.lineDerivCLM ℝ (1:ℝ) (mulTest g hg phi)) +
      T (mulTest (deriv g) (contDiff_infty_iff_deriv.mp hg).2 phi)
  rw [h]
  abel

theorem mulDist_comp (g h : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (T : CDist) :
    mulDist g hg (mulDist h hh T) = mulDist (fun r => g r*h r) (hg.mul hh) T := by
  ext phi
  change T (mulTest h hh (mulTest g hg phi)) = T (mulTest (fun r => g r*h r) (hg.mul hh) phi)
  congr 1
  ext r
  change (phi r*g r)*h r = phi r*(g r*h r)
  ring

theorem derivative_complex_smul (c : ℂ) (T : CDist) :
    (Distribution.lineDerivCLM (1:ℝ) (c • T) : CDist) = c • Distribution.lineDerivCLM (1:ℝ) T := by
  ext phi
  change -(c * T (TestFunction.lineDerivCLM ℝ (1:ℝ) phi)) = c * (-T (TestFunction.lineDerivCLM ℝ (1:ℝ) phi))
  ring

theorem mulDist_complex_smul (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (c : ℂ) (T : CDist) :
    mulDist g hg (c • T) = c • mulDist g hg T := by
  ext phi
  rfl

theorem mulDist_congr (g h : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (he : g = h) : mulDist g hg = mulDist h hh := by subst h; rfl

/-- Complex smooth-coefficient Leibniz rule, including non-tempered distributions. -/
theorem derivative_mulComplexDist (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (T : CDist) :
    Distribution.lineDerivCLM (1:ℝ) (mulComplexDist g hg T) =
      mulComplexDist g hg (Distribution.lineDerivCLM (1:ℝ) T) +
      mulComplexDist (deriv g) (contDiff_infty_iff_deriv.mp hg).2 T := by
  have hre : deriv (fun r => (g r).re) = fun r => (deriv g r).re :=
    funext (realPart_deriv g (hg.differentiable (by simp)))
  have him : deriv (fun r => (g r).im) = fun r => (deriv g r).im :=
    funext (imagPart_deriv g (hg.differentiable (by simp)))
  simp only [mulComplexDist, add_apply, smul_apply,
    map_add, derivative_complex_smul, derivative_mulDist, smul_add]
  rw [mulDist_congr _ _ _ (Complex.reCLM.contDiff.comp (contDiff_infty_iff_deriv.mp hg).2) hre,
    mulDist_congr _ _ _ (Complex.imCLM.contDiff.comp (contDiff_infty_iff_deriv.mp hg).2) him]
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply]
  abel

end KN.ChargedRadial
