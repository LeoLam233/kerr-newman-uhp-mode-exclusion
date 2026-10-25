import KN.Analysis.ResolventCompleteness
import Mathlib.Analysis.PSeries

namespace KN.Analysis
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Actual inverse action on an eigenvector of an unbounded operator. -/
theorem resolvent_eigenvector_norm (T : E →ₗ.[ℂ] E) (z : ℂ) (R : ResolventAt T z)
    (v : E) (hv : v ∈ T.domain) (lam : ℂ) (heig : T ⟨v,hv⟩=lam • v) :
    ‖lam-z‖*‖R.inverse v‖=‖v‖ := by
  have h := R.left_inverse ⟨v,hv⟩
  rw [heig,← sub_smul,map_smul] at h
  simpa only [norm_smul] using congrArg norm h

/-- Linear growth of the actual eigenvalue distance implies a Hilbert--Schmidt
resolvent. No summability, compactness or perturbed eigenbasis is assumed. -/
theorem resolvent_hilbertSchmidt_of_eigenvalue_growth
    (T : E →ₗ.[ℂ] E) (z : ℂ) (R : ResolventAt T z)
    (basis : HilbertBasis ℕ ℂ E) (lam : ℕ → ℂ)
    (hmem : ∀ n, basis n ∈ T.domain)
    (heig : ∀ n, T ⟨basis n,hmem n⟩=lam n • basis n)
    (c : ℝ) (hc : 0<c) (hgrowth : ∀ n : ℕ, c*((n:ℝ)+1)≤‖lam n-z‖) :
    Summable (fun n : ℕ => ‖R.inverse (basis n)‖^2) := by
  have hs : Summable (fun n : ℕ => 1/((n:ℝ)+1)^2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    simpa only [Real.rpow_two,sq_abs] using h
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hs.mul_left (c⁻¹^2))
  intro n
  have h := resolvent_eigenvector_norm T z R (basis n) (hmem n) (lam n) (heig n)
  rw [basis.orthonormal.norm_eq_one n] at h
  have hn : 0<(n:ℝ)+1 := by positivity
  have hbound : ‖R.inverse (basis n)‖ ≤ c⁻¹/((n:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_right (hgrowth n) (norm_nonneg (R.inverse (basis n)))
    rw [h] at hh
    apply (le_div_iff₀ hn).mpr
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith
  calc
    _ ≤ (c⁻¹/((n:ℝ)+1))^2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = _ := by rw [div_pow]; ring

/-- Exact Hilbert--Schmidt criterion for a genuine static eigenbasis of any
index type, including paired and unpaired spectral blocks. -/
theorem resolvent_hilbertSchmidt_iff_eigenvalue_sum {ι : Type*}
    (T : E →ₗ.[ℂ] E) (z : ℂ) (R : ResolventAt T z)
    (basis : HilbertBasis ι ℂ E) (lam : ι → ℂ)
    (hmem : ∀ n, basis n ∈ T.domain)
    (heig : ∀ n, T ⟨basis n,hmem n⟩=lam n • basis n) :
    Summable (fun n => ‖R.inverse (basis n)‖^2) ↔
      Summable (fun n => (‖lam n-z‖^2)⁻¹) := by
  have he : (fun n => ‖R.inverse (basis n)‖^2) = fun n => (‖lam n-z‖^2)⁻¹ := by
    funext n
    have h := resolvent_eigenvector_norm T z R (basis n) (hmem n) (lam n) (heig n)
    rw [basis.orthonormal.norm_eq_one n] at h
    have hn : ‖lam n-z‖≠0 := by intro hz; rw [hz,zero_mul] at h; norm_num at h
    have hv : ‖R.inverse (basis n)‖=‖lam n-z‖⁻¹ := by
      rw [inv_eq_one_div]
      apply (eq_div_iff hn).mpr
      nlinarith [h]
    rw [hv,inv_pow]
  rw [he]

end
end KN.Analysis
