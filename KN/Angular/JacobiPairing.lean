import KN.Angular.FirstOrderReverse
import KN.Angular.JacobiL2Images

namespace KN.Angular.Jacobi
noncomputable section
open scoped ContDiff

def pairedIndex (k : ℤ) (n : ℕ) : ℕ := if |k| ≤ 1 then n+1 else n

def ladderConstant (k : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ k then -((n : ℝ)+(k : ℝ)-1)
  else if k ≤ -2 then (n : ℝ)-(k : ℝ)-1 else -((n : ℝ)+4)

def pairedEigenvalueSq (k : ℤ) (n : ℕ) : ℝ :=
  (((pairedIndex k n : ℕ) : ℝ)+max |(k : ℝ)| 1)*
    (((pairedIndex k n : ℕ) : ℝ)+max |(k : ℝ)| 1+1)-2

theorem ladderConstant_ne_zero (k : ℤ) (n : ℕ) : ladderConstant k n ≠ 0 := by
  unfold ladderConstant
  split_ifs with h h'
  · have hk : (2 : ℝ) ≤ k := by exact_mod_cast h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · have hk : (k : ℝ) ≤ -2 := by exact_mod_cast h'
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem paired_lowering (k : ℤ) (n : ℕ) :
    Set.EqOn (lowering (k : ℝ) (upper (k : ℝ) (pairedIndex k n)))
      (fun θ => ladderConstant k n*lower (k : ℝ) n θ) (Set.Ioo 0 Real.pi) := by
  intro θ hθ
  by_cases hk : 2 ≤ k
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hnot : ¬ |k| ≤ 1 := by rw [abs_le]; omega
    simp only [pairedIndex,ite_eq_right hnot,ladderConstant,ite_eq_left hk]
    exact upper_right_image _ _ _ hkR hθ
  · by_cases hk' : k ≤ -2
    · have hkR : (k : ℝ) ≤ -2 := by exact_mod_cast hk'
      have hnot : ¬ |k| ≤ 1 := by rw [abs_le]; omega
      simp only [pairedIndex,ite_eq_right hnot,ladderConstant,ite_eq_right hk,ite_eq_left hk']
      exact upper_left_image _ _ _ hkR hθ
    · have hcentral : |k| ≤ 1 := by rw [abs_le]; omega
      have hkR : |(k : ℝ)| ≤ 1 := by exact_mod_cast hcentral
      simp only [pairedIndex,ite_eq_left hcentral,ladderConstant,ite_eq_right hk,ite_eq_right hk']
      exact upper_central_image _ _ _ hkR hθ

theorem paired_gap (k : ℤ) (n : ℕ) : 4 ≤ pairedEigenvalueSq k n := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hell : (2 : ℝ) ≤ (pairedIndex k n : ℝ)+max |(k : ℝ)| 1 := by
    unfold pairedIndex
    split_ifs with hk
    · push_cast
      have := le_max_right |(k : ℝ)| 1
      linarith
    · have hkZ : (2 : ℤ) ≤ |k| := by omega
      have hkR : (2 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkZ
      have := le_max_left |(k : ℝ)| 1
      linarith
  unfold pairedEigenvalueSq
  nlinarith

/-- Reverse ladder is derived from the scalar equation and the proved
forward image, not postulated as a specialized angular spectral fact. -/
theorem paired_raising (k : ℤ) (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    deriv (lower (k : ℝ) n) θ + coefficient (k : ℝ) θ*lower (k : ℝ) n θ =
      -(pairedEigenvalueSq k n/ladderConstant k n)*upper (k : ℝ) (pairedIndex k n) θ := by
  have hrev := upper_reverse (k : ℝ) θ (pairedIndex k n) hθ
  have hd := (paired_lowering k n).deriv isOpen_Ioo hθ
  have hsm : ContDiffOn ℝ ∞ (lower (k : ℝ) n) (Set.Ioo 0 Real.pi) :=
    regular_smooth _ _ (abs_nonneg _) (abs_nonneg _) n
  have hdiff := (hsm.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by simp)
  rw [deriv_const_mul _ hdiff] at hd
  rw [hd,paired_lowering k n hθ] at hrev
  change ladderConstant k n*deriv (lower (k : ℝ) n) θ + _ =
    -pairedEigenvalueSq k n*upper (k : ℝ) (pairedIndex k n) θ at hrev
  have hc := ladderConstant_ne_zero k n
  field_simp
  nlinarith [hrev]

end
end KN.Angular.Jacobi
