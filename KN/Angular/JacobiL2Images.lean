import KN.Angular.JacobiFirstOrder
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

namespace KN.Angular.Jacobi
noncomputable section
open MeasureTheory

theorem upper_memLp (k : ℝ) (n : ℕ) :
    MemLp (fun θ => (upper k n θ : ℂ)) 2 intervalMeasure :=
  regular_memLp _ _ (abs_nonneg _) (abs_nonneg _) n

theorem lower_memLp (k : ℝ) (n : ℕ) :
    MemLp (fun θ => (lower k n θ : ℂ)) 2 intervalMeasure :=
  regular_memLp _ _ (abs_nonneg _) (abs_nonneg _) n

/-- All upper first-order images belong to L², including every critical
endpoint sector. No square-domain implication is used. -/
theorem upper_lowering_memLp (k : ℤ) (n : ℕ) :
    MemLp (fun θ => (lowering (k : ℝ) (upper (k : ℝ) n) θ : ℂ)) 2 intervalMeasure := by
  have hae : ∀ᵐ θ ∂intervalMeasure, θ ∈ Set.Ioo 0 Real.pi :=
    ae_restrict_mem measurableSet_Ioo
  by_cases hk : 2 ≤ k
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    apply MemLp.ae_eq (hf_Lp := ((lower_memLp (k : ℝ) n).const_mul (-((n : ℝ)+(k : ℝ)-1) : ℂ)))
    filter_upwards [hae] with θ hθ
    rw [upper_right_image _ _ _ hkR hθ]
    push_cast
    rfl
  · by_cases hk' : k ≤ -2
    · have hkR : (k : ℝ) ≤ -2 := by exact_mod_cast hk'
      apply MemLp.ae_eq (hf_Lp := ((lower_memLp (k : ℝ) n).const_mul (((n : ℝ)-(k : ℝ)-1) : ℂ)))
      filter_upwards [hae] with θ hθ
      rw [upper_left_image _ _ _ hkR hθ]
      push_cast
      rfl
    · have hkZ : |k| ≤ 1 := by rw [abs_le]; omega
      have hkR : |(k : ℝ)| ≤ 1 := by exact_mod_cast hkZ
      cases n with
      | zero =>
        apply MemLp.ae_eq (hf_Lp := (MemLp.zero : MemLp (0 : ℝ → ℂ) 2 intervalMeasure))
        filter_upwards [hae] with θ hθ
        simp [upper_ground_kernel _ _ hkR hθ]
      | succ n =>
        apply MemLp.ae_eq (hf_Lp := ((lower_memLp (k : ℝ) n).const_mul (-((n : ℝ)+4) : ℂ)))
        filter_upwards [hae] with θ hθ
        rw [upper_central_image _ _ _ hkR hθ]
        push_cast
        rfl

end
end KN.Angular.Jacobi
