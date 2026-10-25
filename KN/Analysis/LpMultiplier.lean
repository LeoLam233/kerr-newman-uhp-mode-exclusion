import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Basic.Complex.Basic

noncomputable section
open MeasureTheory
namespace KN.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (μ : Measure ℝ) (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ)
  (hbound : ∀ x : ℝ, ‖f x‖ ≤ C)

include hf hbound in
lemma memLp_bounded_smul (u : Lp E 2 μ) : MemLp (fun x => f x • u x) 2 μ := by
  apply (Lp.memLp u).of_le_mul (hf.aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  filter_upwards [] with x
  change ‖f x • u x‖ ≤ C*‖u x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

def scalarMulLp (u : Lp E 2 μ) : Lp E 2 μ :=
  (memLp_bounded_smul μ f hf C hbound u).toLp (fun x => f x • u x)

theorem scalarMulLp_ae (u : Lp E 2 μ) :
    scalarMulLp μ f hf C hbound u =ᵐ[μ] fun x => f x • u x :=
  (memLp_bounded_smul μ f hf C hbound u).coeFn_toLp

theorem scalarMulLp_add (u v : Lp E 2 μ) :
    scalarMulLp μ f hf C hbound (u+v) =
      scalarMulLp μ f hf C hbound u + scalarMulLp μ f hf C hbound v := by
  apply Lp.ext
  filter_upwards [scalarMulLp_ae μ f hf C hbound (u+v),
    scalarMulLp_ae μ f hf C hbound u, scalarMulLp_ae μ f hf C hbound v,
    Lp.coeFn_add u v,
    Lp.coeFn_add (scalarMulLp μ f hf C hbound u) (scalarMulLp μ f hf C hbound v)] with x ha hb hc hd he
  simp only [Pi.add_apply] at hd he
  rw [ha,he,hb,hc,hd]
  exact smul_add _ _ _

theorem scalarMulLp_smul (a : ℂ) (u : Lp E 2 μ) :
    scalarMulLp μ f hf C hbound (a • u) = a • scalarMulLp μ f hf C hbound u := by
  apply Lp.ext
  filter_upwards [scalarMulLp_ae μ f hf C hbound (a • u),
    scalarMulLp_ae μ f hf C hbound u, Lp.coeFn_smul a u,
    Lp.coeFn_smul a (scalarMulLp μ f hf C hbound u)] with x ha hb hc hd
  simp only [Pi.smul_apply] at hc hd
  rw [ha,hd,hb,hc]
  exact smul_comm _ _ _

def scalarMulLinearMap : Lp E 2 μ →ₗ[ℂ] Lp E 2 μ where
  toFun := scalarMulLp μ f hf C hbound
  map_add' := scalarMulLp_add μ f hf C hbound
  map_smul' := scalarMulLp_smul μ f hf C hbound

theorem scalarMulLp_norm_le (u : Lp E 2 μ) :
    ‖scalarMulLp μ f hf C hbound u‖ ≤ C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarMulLp_ae μ f hf C hbound u] with x hx
  rw [hx,norm_smul]
  exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)

/-- Actual bounded scalar multiplication on L², with no quotient representative choice in its API. -/
def boundedScalarMultiplier : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  (scalarMulLinearMap μ f hf C hbound).mkContinuous C (scalarMulLp_norm_le μ f hf C hbound)

theorem boundedScalarMultiplier_ae (u : Lp E 2 μ) :
    boundedScalarMultiplier μ f hf C hbound u =ᵐ[μ] fun x => f x • u x :=
  scalarMulLp_ae μ f hf C hbound u

theorem boundedScalarMultiplier_norm_le (hC : 0 ≤ C) :
    ‖boundedScalarMultiplier (E := E) μ f hf C hbound‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  exact scalarMulLp_norm_le μ f hf C hbound

end KN.Analysis
