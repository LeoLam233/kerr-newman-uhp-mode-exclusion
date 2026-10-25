import KN.Angular.ExternalJacobi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! General published Jacobi identities, DLMF 18.9.3, 18.9.4,
18.9.5 and 18.9.15 (https://dlmf.nist.gov/18.9).
The parameter-shifting ladder relation below is PROVED from these general
identities; none of the interfaces asserts a Dirac spectrum or domain. -/
namespace KN.Angular.Jacobi
noncomputable section

axiom dlmf_18_9_3 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  polynomial α (β-1) (n+1) x - polynomial (α-1) β (n+1) x = polynomial α β n x

axiom dlmf_18_9_4 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  (1-x)*polynomial (α+1) β n x + (1+x)*polynomial α (β+1) n x =
    2*polynomial α β n x

axiom dlmf_18_9_5 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  (2*((n+1 : ℕ) : ℝ)+α+β+1)*polynomial α β (n+1) x =
    (((n+1 : ℕ) : ℝ)+α+β+1)*polynomial α (β+1) (n+1) x +
    (((n+1 : ℕ) : ℝ)+α)*polynomial α (β+1) n x

/-- The symmetric companion stated immediately after DLMF 18.9.6. -/
axiom dlmf_18_9_5_symmetric (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  (2*((n+1 : ℕ) : ℝ)+α+β+1)*polynomial α β (n+1) x =
    (((n+1 : ℕ) : ℝ)+α+β+1)*polynomial (α+1) β (n+1) x -
    (((n+1 : ℕ) : ℝ)+β)*polynomial (α+1) β n x

axiom dlmf_18_9_15 (α β x : ℝ) (n : ℕ) (hx : x ∈ Set.Ioo (-1) 1) :
  HasDerivAt (polynomial α β (n+1))
    ((1/2)*(((n+1 : ℕ) : ℝ)+α+β+1)*polynomial (α+1) (β+1) n x) x

theorem polynomial_zero (α β x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    polynomial α β 0 x = 1 := by
  have hm : 0 < 1-x := by linarith [hx.2]
  have hp : 0 < 1+x := by linarith [hx.1]
  simp only [polynomial, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one,
    one_div, inv_one, one_mul, iteratedDeriv_zero, Nat.cast_zero, zero_add]
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_neg hm.le, Real.rpow_neg hp.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hm α), ne_of_gt (Real.rpow_pos_of_pos hp β)]

theorem polynomial_zero_hasDerivAt (α β x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    HasDerivAt (polynomial α β 0) 0 x := by
  apply (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact polynomial_zero α β y hy

/-- Exact degree-preserving parameter ladder, derived rather than assumed. -/
theorem derivative_shift_right_succ (α β x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Ioo (-1) 1) :
    (1+x)*deriv (polynomial α β (n+1)) x + β*polynomial α β (n+1) x =
      (((n+1 : ℕ) : ℝ)+β)*polynomial (α+1) (β-1) (n+1) x := by
  rw [(dlmf_18_9_15 α β x n hx).deriv]
  have h3 := dlmf_18_9_3 (α+1) (β+1) x n hx
  have h4 := dlmf_18_9_4 α β x (n+1) hx
  have h5 := dlmf_18_9_5 (α+1) (β-1) x n hx
  have h3' := dlmf_18_9_3 (α+1) β x n hx
  simp only [add_sub_cancel_right, sub_add_cancel] at h3 h5 h3'
  have hid : (1+x)*polynomial (α+1) (β+1) n x =
      2*(polynomial (α+1) β (n+1) x-polynomial α β (n+1) x) := by
    rw [← h3]
    nlinarith [h4]
  have hid2 : (((n+1 : ℕ) : ℝ)+β)*polynomial (α+1) (β-1) (n+1) x =
      (((n+1 : ℕ) : ℝ)+α+β+1)*polynomial (α+1) β (n+1) x -
      (((n+1 : ℕ) : ℝ)+α+1)*polynomial α β (n+1) x := by
    rw [← h3'] at h5
    nlinarith [h5]
  rw [hid2]
  calc
    _ = (1/2)*(((n+1 : ℕ) : ℝ)+α+β+1)*
        ((1+x)*polynomial (α+1) (β+1) n x)+β*polynomial α β (n+1) x := by ring
    _ = _ := by rw [hid]; ring

theorem derivative_shift_left_succ (α β x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Ioo (-1) 1) :
    (1-x)*deriv (polynomial α β (n+1)) x - α*polynomial α β (n+1) x =
      -(((n+1 : ℕ) : ℝ)+α)*polynomial (α-1) (β+1) (n+1) x := by
  rw [(dlmf_18_9_15 α β x n hx).deriv]
  have h3 := dlmf_18_9_3 (α+1) (β+1) x n hx
  have h4 := dlmf_18_9_4 α β x (n+1) hx
  have h5 := dlmf_18_9_5_symmetric (α-1) (β+1) x n hx
  have h3' := dlmf_18_9_3 α (β+1) x n hx
  simp only [add_sub_cancel_right, sub_add_cancel] at h3 h5 h3'
  have hid : (1-x)*polynomial (α+1) (β+1) n x =
      2*(polynomial α β (n+1) x-polynomial α (β+1) (n+1) x) := by
    rw [← h3]
    nlinarith [h4]
  have hid2 : (((n+1 : ℕ) : ℝ)+α)*polynomial (α-1) (β+1) (n+1) x =
      (((n+1 : ℕ) : ℝ)+α+β+1)*polynomial α (β+1) (n+1) x -
      (((n+1 : ℕ) : ℝ)+β+1)*polynomial α β (n+1) x := by
    rw [← h3'] at h5
    nlinarith [h5]
  calc
    _ = (1/2)*(((n+1 : ℕ) : ℝ)+α+β+1)*
        ((1-x)*polynomial (α+1) (β+1) n x)-α*polynomial α β (n+1) x := by ring
    _ = -((((n+1 : ℕ) : ℝ)+α)*polynomial (α-1) (β+1) (n+1) x) := by
      rw [hid,hid2]; ring
    _ = _ := by ring

theorem derivative_shift_right (α β x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Ioo (-1) 1) :
    (1+x)*deriv (polynomial α β n) x + β*polynomial α β n x =
      ((n : ℝ)+β)*polynomial (α+1) (β-1) n x := by
  cases n with
  | zero => rw [(polynomial_zero_hasDerivAt α β x hx).deriv,
      polynomial_zero α β x hx,polynomial_zero (α+1) (β-1) x hx]; simp
  | succ n => exact derivative_shift_right_succ α β x n hx

theorem derivative_shift_left (α β x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Ioo (-1) 1) :
    (1-x)*deriv (polynomial α β n) x - α*polynomial α β n x =
      -((n : ℝ)+α)*polynomial (α-1) (β+1) n x := by
  cases n with
  | zero => rw [(polynomial_zero_hasDerivAt α β x hx).deriv,
      polynomial_zero α β x hx,polynomial_zero (α-1) (β+1) x hx]; simp
  | succ n => exact derivative_shift_left_succ α β x n hx

theorem polynomial_hasDerivAt (α β x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Ioo (-1) 1) :
    HasDerivAt (polynomial α β n) (deriv (polynomial α β n) x) x := by
  cases n with
  | zero => exact (polynomial_zero_hasDerivAt α β x hx).differentiableAt.hasDerivAt
  | succ n => exact (dlmf_18_9_15 α β x n hx).differentiableAt.hasDerivAt

end
end KN.Angular.Jacobi
