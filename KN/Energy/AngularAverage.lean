import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open MeasureTheory
namespace KN.Energy

/-- The normalized sin² expectation on the actual angular interval. -/
noncomputable def sineAverage (ρ : ℝ → ℝ) : ℝ :=
  ∫ θ in Set.Ioo 0 Real.pi, Real.sin θ ^ 2 * ρ θ

/-- No pointwise lower bound on the angular density is assumed. Normalization
and nonnegativity alone prove the exact bound needed for (46). -/
theorem sineAverage_bounds (ρ : ℝ → ℝ)
    (hρ : IntegrableOn ρ (Set.Ioo 0 Real.pi))
    (hn : 0 ≤ᵐ[volume.restrict (Set.Ioo 0 Real.pi)] ρ)
    (hunit : ∫ θ in Set.Ioo 0 Real.pi, ρ θ = 1) :
    0 ≤ sineAverage ρ ∧ sineAverage ρ ≤ 1 := by
  have hs : ∀ θ : ℝ, 0 ≤ Real.sin θ ^ 2 ∧ Real.sin θ ^ 2 ≤ 1 := by
    intro θ
    constructor
    · positivity
    · nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  have hmeas : AEStronglyMeasurable (fun θ => Real.sin θ ^ 2 * ρ θ)
      (volume.restrict (Set.Ioo 0 Real.pi)) :=
    (Real.continuous_sin.pow 2).aestronglyMeasurable.mul hρ.aestronglyMeasurable
  have hle : ∀ᵐ θ ∂volume.restrict (Set.Ioo 0 Real.pi), Real.sin θ ^ 2 * ρ θ ≤ ρ θ := by
    filter_upwards [hn] with θ hθ
    exact mul_le_of_le_one_left hθ (hs θ).2
  have hpos : ∀ᵐ θ ∂volume.restrict (Set.Ioo 0 Real.pi), 0 ≤ Real.sin θ ^ 2 * ρ θ := by
    filter_upwards [hn] with θ hθ
    exact mul_nonneg (hs θ).1 hθ
  have hi : IntegrableOn (fun θ => Real.sin θ ^ 2 * ρ θ) (Set.Ioo 0 Real.pi) := by
    apply hρ.mono' hmeas
    filter_upwards [hle, hpos] with θ hθ hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp] using hθ
  refine ⟨integral_nonneg_of_ae hpos, ?_⟩
  dsimp [sineAverage]
  rw [← hunit]
  exact integral_mono_ae hi hρ hle
end KN.Energy
