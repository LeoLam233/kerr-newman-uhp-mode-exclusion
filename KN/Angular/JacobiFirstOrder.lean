import KN.Angular.JacobiDerivative

namespace KN.Angular.Jacobi
noncomputable section

def upper (k : ℝ) (n : ℕ) := regularFunction |k+1| |k-1| n
def lower (k : ℝ) (n : ℕ) := regularFunction |k+2| |k-2| n

def lowering (k : ℝ) (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  deriv f θ-((3/2)*Real.cos θ+k)/Real.sin θ*f θ

/-- Actual unpaired off-diagonal zero mode, not merely a square eigenfunction. -/
theorem upper_ground_kernel (k θ : ℝ) (hk : |k| ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) : lowering k (upper k 0) θ=0 := by
  have hk' := abs_le.mp hk
  unfold lowering upper
  apply regular_ground_lowering_zero _ _ _ _ hθ
  · rw [abs_of_nonneg (by linarith : 0 ≤ k+1),abs_of_nonpos (by linarith : k-1 ≤ 0)]
    ring
  · rw [abs_of_nonneg (by linarith : 0 ≤ k+1),abs_of_nonpos (by linarith : k-1 ≤ 0)]
    ring

theorem upper_central_image (k θ : ℝ) (n : ℕ) (hk : |k| ≤ 1)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    lowering k (upper k (n+1)) θ = -((n : ℝ)+4)*lower k n θ := by
  have hk' := abs_le.mp hk
  have hA : |k+2|=|k+1|+1 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ k+2),abs_of_nonneg (by linarith : 0 ≤ k+1)]
    ring
  have hB : |k-2|=|k-1|+1 := by
    rw [abs_of_nonpos (by linarith : k-2 ≤ 0),abs_of_nonpos (by linarith : k-1 ≤ 0)]
    ring
  unfold lowering upper lower
  rw [hA,hB]
  apply regular_central_lowering _ _ _ _ _ hθ
  · rw [abs_of_nonneg (by linarith : 0 ≤ k+1),abs_of_nonpos (by linarith : k-1 ≤ 0)]
    ring
  · rw [abs_of_nonneg (by linarith : 0 ≤ k+1),abs_of_nonpos (by linarith : k-1 ≤ 0)]
    ring

theorem upper_right_image (k θ : ℝ) (n : ℕ) (hk : 2 ≤ k)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    lowering k (upper k n) θ = -((n : ℝ)+k-1)*lower k n θ := by
  unfold lowering upper lower
  rw [abs_of_nonneg (by linarith : 0 ≤ k+1),abs_of_nonneg (by linarith : 0 ≤ k-1),
    abs_of_nonneg (by linarith : 0 ≤ k+2),abs_of_nonneg (by linarith : 0 ≤ k-2)]
  convert regular_right_lowering (k-1) θ n hθ using 1 <;> congr 1 <;> ring

theorem upper_left_image (k θ : ℝ) (n : ℕ) (hk : k ≤ -2)
    (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    lowering k (upper k n) θ = ((n : ℝ)-k-1)*lower k n θ := by
  unfold lowering upper lower
  rw [abs_of_nonpos (by linarith : k+1 ≤ 0),abs_of_nonpos (by linarith : k-1 ≤ 0),
    abs_of_nonpos (by linarith : k+2 ≤ 0),abs_of_nonpos (by linarith : k-2 ≤ 0)]
  convert regular_left_lowering (-k-1) θ n hθ using 1 <;> congr 1 <;> ring

end
end KN.Angular.Jacobi
