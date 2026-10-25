import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

/-- Integration-by-parts against an actual compactly supported test function.
The boundary term does not disappear merely because f is smooth at the horizon. -/
theorem zero_extension_pairing (r : ℝ) (f : ℝ → ℂ) (phi : ℝ → ℝ)
    (hf : ContDiff ℝ 1 f) (hp : ContDiff ℝ 1 phi) (hc : HasCompactSupport phi) :
    -(∫ t in Ioi r, deriv phi t • f t) =
      (∫ t in Ioi r, phi t • deriv f t) + phi r • f r := by
  have hder : deriv (phi • f) = fun t => deriv phi t • f t + phi t • deriv f t := by
    funext t
    simpa only [add_comm] using deriv_smul (hp.differentiable one_ne_zero t) (hf.differentiable one_ne_zero t)
  have hh := HasCompactSupport.integral_Ioi_deriv_eq (hp.smul hf) hc.smul_right r
  have hi1 : IntegrableOn (fun t => deriv phi t • f t) (Ioi r) :=
    ((hp.continuous_deriv le_rfl).smul hf.continuous).integrable_of_hasCompactSupport
      hc.deriv.smul_right |>.integrableOn
  have hi2 : IntegrableOn (fun t => phi t • deriv f t) (Ioi r) :=
    (hp.continuous.smul (hf.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      hc.smul_right |>.integrableOn
  rw [hder, integral_add hi1 hi2] at hh
  change _ = -(phi r • f r) at hh
  exact neg_eq_iff_add_eq_zero.mpr (by linear_combination hh)

abbrev CDist := Distribution (⊤ : Opens ℝ) ℂ ⊤

/-- Actual distribution obtained by zero-extending a function across r. -/
def zeroExtension (r : ℝ) (f : ℝ → ℂ) : CDist :=
  Distribution.ofFun (⊤ : Opens ℝ) f (volume.restrict (Ioi r)) ⊤

/-- Delta with an arbitrary complex coefficient, on real-valued test functions. -/
def deltaValue (r : ℝ) (z : ℂ) : CDist :=
  Distribution.mapCLM (ContinuousLinearMap.toSpanSingleton ℝ z) (Distribution.delta r)

lemma deltaValue_apply (r : ℝ) (z : ℂ) (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    deltaValue r z phi = phi r • z := rfl

lemma zeroExtension_apply (r : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    zeroExtension r f phi = ∫ t in Ioi r, phi t • f t := by
  exact Distribution.ofFun_apply (hf.locallyIntegrable.locallyIntegrableOn _)

lemma testFunction_deriv (phi : 𝓓((⊤ : Opens ℝ), ℝ)) (t : ℝ) :
    (TestFunction.lineDerivCLM ℝ (1:ℝ) phi : 𝓓((⊤ : Opens ℝ), ℝ)) t = deriv phi t := by
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  rw [(phi.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
  rfl

/-- The exact delta source of a half-line zero extension, proved in Mathlib's
space of continuous linear distributions, not assumed as an external interface. -/
theorem derivative_zeroExtension (r : ℝ) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    Distribution.lineDerivCLM (1:ℝ) (zeroExtension r f) =
      zeroExtension r (deriv f) + deltaValue r (f r) := by
  ext phi
  rw [Distribution.lineDerivCLM_apply, zeroExtension_apply r f hf.continuous]
  change -(∫ t in Ioi r, (TestFunction.lineDerivCLM ℝ (1:ℝ) phi : 𝓓((⊤ : Opens ℝ), ℝ)) t • f t) =
    zeroExtension r (deriv f) phi + deltaValue r (f r) phi
  simp_rw [testFunction_deriv]
  rw [zeroExtension_apply r (deriv f) (hf.continuous_deriv le_rfl), deltaValue_apply]
  exact zero_extension_pairing r f phi hf (phi.contDiff.of_le (by simp)) phi.hasCompactSupport

end KN.ChargedRadial
