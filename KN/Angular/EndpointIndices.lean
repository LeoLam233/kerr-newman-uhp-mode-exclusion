import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace KN.Angular

/-- Critical half-integer endpoints are included: equality at 1/2 is allowed. -/
theorem half_integer_gap (m : ℤ) : (1/2 : ℝ) ≤ |(m : ℝ)+3/2| := by
  by_cases hm : -1 ≤ m
  · have hmR : (-1 : ℝ) ≤ m := by exact_mod_cast hm
    rw [abs_of_nonneg (by linarith : 0 ≤ (m : ℝ)+3/2)]
    linarith
  · have hmZ : m ≤ -2 := by omega
    have hmR : (m : ℝ) ≤ -2 := by exact_mod_cast hmZ
    rw [abs_of_nonpos (by linarith : (m : ℝ)+3/2 ≤ 0)]
    linarith

theorem endpoint_indicial_gap (m : ℤ) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) :
    (1/2 : ℝ) ≤ |3/2+σ*(m : ℝ)| ∧ (1/2 : ℝ) ≤ |-3/2+σ*(m : ℝ)| := by
  have hp := half_integer_gap m
  have hm := half_integer_gap (-m)
  push_cast at hm
  rcases hσ with rfl | rfl <;> constructor
  · simpa [add_comm] using hp
  · have he : -3/2+1*(m : ℝ) = -(-(m : ℝ)+3/2) := by ring
    rw [he, abs_neg]
    exact hm
  · simpa [sub_eq_add_neg, add_comm] using hm
  · have he : -3/2+(-1)*(m : ℝ) = -((m : ℝ)+3/2) := by ring
    rw [he, abs_neg]
    exact hp

end KN.Angular
