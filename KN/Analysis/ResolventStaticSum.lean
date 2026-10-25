import KN.Analysis.ResolventEigenbasis
import KN.Angular.StaticEigenFamily
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

namespace KN.Analysis
noncomputable section
open KN.Angular.Jacobi

theorem pairedEigenvalueSq_growth (k : ℤ) (n : ℕ) :
    ((n:ℝ)+1)^2 ≤ pairedEigenvalueSq k n := by
  have hn : 0≤(n:ℝ) := Nat.cast_nonneg n
  have hell : (n:ℝ)+2 ≤ (pairedIndex k n:ℝ)+max |(k:ℝ)| 1 := by
    unfold pairedIndex
    split_ifs with hk
    · push_cast
      linarith [le_max_right |(k:ℝ)| 1]
    · have hkZ : (2:ℤ)≤|k| := by omega
      have hkR : (2:ℝ)≤|(k:ℝ)| := by exact_mod_cast hkZ
      linarith [le_max_left |(k:ℝ)| 1]
  unfold pairedEigenvalueSq
  nlinarith

theorem real_sub_I_norm_sq (x : ℝ) : ‖(x:ℂ)-Complex.I‖^2=x^2+1 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply,pow_two]

/-- Both paired signs and the optional correctly signed ground branch have
summable squared resolvent eigenvalues at i. -/
theorem staticEigenvalue_resolvent_sum (k : ℤ) (β : ℝ) :
    Summable (fun i : StaticLabel k => (‖(staticEigenvalue k β i:ℂ)-Complex.I‖^2)⁻¹) := by
  have hp : Summable (fun n : ℕ => ((positiveRoot k β n)^2+1)⁻¹) := by
    have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
      have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
      simpa only [Real.rpow_two,sq_abs] using h
    apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
    intro n
    rw [← one_div]
    apply one_div_le_one_div_of_le (by positivity)
    have h := pairedEigenvalueSq_growth k n
    rw [positiveRoot_sq]
    nlinarith [sq_nonneg β]
  apply Summable.sum
  · apply (summable_prod_of_nonneg (fun _ => inv_nonneg.mpr (sq_nonneg _))).mpr
    refine ⟨?_,Summable.of_finite⟩
    intro sign
    cases sign <;> simpa only [Function.comp_apply,staticEigenvalue,real_sub_I_norm_sq,neg_sq] using hp
  · exact Summable.of_finite

/-- Chiral doubling preserves the proved Hilbert--Schmidt spectral sum. -/
theorem doubled_staticEigenvalue_resolvent_sum (k : ℤ) (β : ℝ) :
    Summable (fun i : Bool × StaticLabel k => (‖(staticEigenvalue k β i.2:ℂ)-Complex.I‖^2)⁻¹) := by
  apply (summable_prod_of_nonneg (fun _ => inv_nonneg.mpr (sq_nonneg _))).mpr
  exact ⟨fun _ => staticEigenvalue_resolvent_sum k β,Summable.of_finite⟩

end
end KN.Analysis
