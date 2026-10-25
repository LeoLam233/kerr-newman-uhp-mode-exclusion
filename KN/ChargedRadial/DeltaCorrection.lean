import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! The finite horizon delta correction of C002 (35).
The delta and its derivative here are actual continuous functionals on Schwartz space,
not formal symbols. The full supported non-tempered continuation is a separate obligation. -/
noncomputable section
open scoped SchwartzMap
namespace KN.ChargedRadial
open TemperedDistribution

abbrev TD := TemperedDistribution ℝ ℂ

def mulTD (g : ℝ → ℂ) : TD →L[ℂ] TD := TemperedDistribution.smulLeftCLM ℂ g

def derivTD : TD →L[ℂ] TD := TemperedDistribution.derivCLM ℂ

lemma mul_delta (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (r : ℝ) :
    mulTD g (TemperedDistribution.delta r) = g r • TemperedDistribution.delta r := by
  ext φ
  simp [mulTD, hg]

lemma mul_deriv_delta (g : ℝ → ℂ) (hg : g.HasTemperateGrowth) (r : ℝ) :
    mulTD g (derivTD (TemperedDistribution.delta r)) =
      g r • derivTD (TemperedDistribution.delta r) -
        deriv g r • TemperedDistribution.delta r := by
  ext φ
  simp only [mulTD, derivTD, TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.derivCLM_apply_apply, TemperedDistribution.delta_apply,
    neg_apply, SchwartzMap.derivCLM_apply]
  have he : (SchwartzMap.smulLeftCLM ℂ g φ : ℝ → ℂ) = fun t => g t * φ t := by
    simpa only [smul_eq_mul] using SchwartzMap.smulLeftCLM_apply hg φ
  rw [he]
  change -deriv (g * (φ : ℝ → ℂ)) r = _
  rw [((hg.1.differentiable (by simp)).differentiableAt.hasDerivAt.mul
    φ.differentiableAt.hasDerivAt).deriv]
  change -(deriv g r * φ r + g r * deriv φ r) = g r * (-deriv φ r) - deriv g r * φ r
  ring

/-- Resonant cancellation is the exact equality `L(r₊)=Δ'(r₊)`, not vanishing
of the delta's coefficient. This theorem verifies the distribution calculation. -/
theorem resonant_delta_annihilated (Delta L : ℝ → ℂ)
    (hDelta : Delta.HasTemperateGrowth) (hL : L.HasTemperateGrowth)
    (r : ℝ) (hzero : Delta r = 0) (hres : L r = deriv Delta r) :
    mulTD Delta (derivTD (TemperedDistribution.delta r)) +
      mulTD L (TemperedDistribution.delta r) = 0 := by
  rw [mul_deriv_delta Delta hDelta r, mul_delta L hL r, hzero, hres]
  module

/-- The exact correction repairs the second equation's boundary source.
The hypothesis records the derivative of the uncorrected zero extension. -/
theorem correction_repairs_second_equation
    (B : ℝ → ℂ) (hB : B.HasTemperateGrowth) (r : ℝ) (hBr : B r ≠ 0)
    (v₀ z₀ : TD) (zH : ℂ)
    (hz : derivTD z₀ = mulTD B v₀ + zH • TemperedDistribution.delta r) :
    derivTD z₀ = mulTD B (v₀ + (zH / B r) • TemperedDistribution.delta r) := by
  rw [map_add, map_smul, mul_delta B hB r, smul_smul]
  rw [div_mul_cancel₀ zH hBr]
  exact hz

/-- Since the resonance operator annihilates the added delta, adding the correction
leaves the first radial equation unchanged. -/
theorem correction_preserves_first_equation
    (Delta L A : ℝ → ℂ)
    (hDelta : Delta.HasTemperateGrowth) (hL : L.HasTemperateGrowth)
    (r : ℝ) (hzero : Delta r = 0) (hres : L r = deriv Delta r)
    (v₀ z₀ : TD) (c : ℂ)
    (hfirst : mulTD Delta (derivTD v₀) + mulTD L v₀ = mulTD A z₀) :
    mulTD Delta (derivTD (v₀ + c • TemperedDistribution.delta r)) +
      mulTD L (v₀ + c • TemperedDistribution.delta r) = mulTD A z₀ := by
  simp only [map_add, map_smul]
  have h := resonant_delta_annihilated Delta L hDelta hL r hzero hres
  calc
    _ = (mulTD Delta (derivTD v₀) + mulTD L v₀) +
      c • (mulTD Delta (derivTD (TemperedDistribution.delta r)) +
        mulTD L (TemperedDistribution.delta r)) := by module
    _ = mulTD A z₀ := by rw [hfirst, h]; module

end KN.ChargedRadial
