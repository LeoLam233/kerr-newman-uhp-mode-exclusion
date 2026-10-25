import KN.Analysis.LpMultiplier
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open scoped BoundedContinuousFunction
open MeasureTheory
namespace KN.Physics
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Actual angular L² multiplication, linear and continuous in its bounded
continuous coefficient. This supplies the uniform topology needed for radial derivatives. -/
def coefficientMultiplier (μ : Measure ℝ) (f : ℝ →ᵇ ℂ) : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  KN.Analysis.boundedScalarMultiplier μ f f.continuous ‖f‖ f.norm_coe_le_norm

lemma coefficientMultiplier_ae (μ : Measure ℝ) (f : ℝ →ᵇ ℂ) (u : Lp E 2 μ) :
    coefficientMultiplier μ f u =ᵐ[μ] fun t => f t • u t :=
  KN.Analysis.boundedScalarMultiplier_ae μ f f.continuous ‖f‖ f.norm_coe_le_norm u

lemma coefficientMultiplier_add (μ : Measure ℝ) (f g : ℝ →ᵇ ℂ) :
    coefficientMultiplier (E:=E) μ (f+g)=coefficientMultiplier μ f+coefficientMultiplier μ g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [coefficientMultiplier_ae μ (f+g) u,
    coefficientMultiplier_ae μ f u, coefficientMultiplier_ae μ g u,
    Lp.coeFn_add (coefficientMultiplier μ f u) (coefficientMultiplier μ g u)] with t ha hb hc hd
  change (coefficientMultiplier μ (f+g) u) t = (coefficientMultiplier μ f u+coefficientMultiplier μ g u) t
  rw [ha,hd]
  simp only [Pi.add_apply]
  rw [hb,hc]
  exact add_smul _ _ _

lemma coefficientMultiplier_smul (μ : Measure ℝ) (c : ℂ) (f : ℝ →ᵇ ℂ) :
    coefficientMultiplier (E:=E) μ (c • f)=c • coefficientMultiplier μ f := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [coefficientMultiplier_ae μ (c • f) u,
    coefficientMultiplier_ae μ f u,
    Lp.coeFn_smul c (coefficientMultiplier μ f u)] with t ha hb hc
  change (coefficientMultiplier μ (c • f) u) t = (c • coefficientMultiplier μ f u) t
  rw [ha,hc]
  simp only [Pi.smul_apply]
  rw [hb]
  exact mul_smul c (f t) (u t)

def coefficientMultiplierLinear (μ : Measure ℝ) :
    (ℝ →ᵇ ℂ) →ₗ[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) where
  toFun := coefficientMultiplier μ
  map_add' := coefficientMultiplier_add μ
  map_smul' := coefficientMultiplier_smul μ

def coefficientMultiplierCLM (μ : Measure ℝ) :
    (ℝ →ᵇ ℂ) →L[ℂ] (Lp E 2 μ →L[ℂ] Lp E 2 μ) :=
  (coefficientMultiplierLinear μ).mkContinuous 1 (fun f => by
    change ‖KN.Analysis.boundedScalarMultiplier (E:=E) μ f f.continuous ‖f‖ f.norm_coe_le_norm‖ ≤ 1*‖f‖
    simpa only [one_mul] using KN.Analysis.boundedScalarMultiplier_norm_le
      (E:=E) μ f f.continuous ‖f‖ f.norm_coe_le_norm (norm_nonneg f))

theorem coefficient_action_smooth {s : Set ℝ} (μ : Measure ℝ)
    (f : ℝ → (ℝ →ᵇ ℂ)) (u : ℝ → Lp E 2 μ)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f s)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) u s) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r => coefficientMultiplier μ (f r) (u r)) s := by
  have hh := (((coefficientMultiplierCLM (E:=E) μ).restrictScalars ℝ).contDiff.comp_contDiffOn hf)
  have hr := (ContinuousLinearMap.restrictScalarsL ℂ (Lp E 2 μ) (Lp E 2 μ) ℝ ℝ).contDiff.comp_contDiffOn hh
  exact hr.clm_apply hu

end KN.Physics
