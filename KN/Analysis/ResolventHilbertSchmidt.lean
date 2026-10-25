import KN.Analysis.ResolventPerturbation

namespace KN.Analysis
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The resolvent identity with a bounded left factor. This orientation makes
Hilbert--Schmidt transport a direct norm estimate on every basis vector. -/
theorem perturbed_resolvent_factor (T : E →ₗ.[ℂ] E) (z : ℂ) (B : E →L[ℂ] E)
    (R : ResolventAt T z) (Q : ResolventAt (boundedPerturbation T B) z) :
    Q.inverse = (1-Q.inverse*B)*R.inverse := by
  ext u
  have h := Q.left_inverse ⟨R.inverse u,R.mem_domain u⟩
  change Q.inverse (T ⟨R.inverse u,R.mem_domain u⟩+B (R.inverse u)-z • R.inverse u)=R.inverse u at h
  have he : T ⟨R.inverse u,R.mem_domain u⟩+B (R.inverse u)-z • R.inverse u =
      (T ⟨R.inverse u,R.mem_domain u⟩-z • R.inverse u)+B (R.inverse u) := by abel
  rw [he,R.right_inverse,map_add] at h
  change Q.inverse u = R.inverse u-Q.inverse (B (R.inverse u))
  exact eq_sub_of_add_eq h

/-- Bounded operators preserve the basis-sum definition of Hilbert--Schmidt
operators under left composition. -/
theorem hilbertSchmidt_left_comp {ι : Type*} (basis : ι → E) (R A : E →L[ℂ] E)
    (hR : Summable (fun n => ‖R (basis n)‖^2)) :
    Summable (fun n => ‖(A*R) (basis n)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hR.mul_left (‖A‖^2))
  intro n
  change ‖A (R (basis n))‖^2 ≤ ‖A‖^2*‖R (basis n)‖^2
  calc
    _ ≤ (‖A‖*‖R (basis n)‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    _ = _ := mul_pow _ _ _

/-- Hilbert--Schmidt resolvents persist under bounded perturbations whenever
the two genuine resolvents exist. No eigenbasis of the perturbed operator is used. -/
theorem perturbed_resolvent_hilbertSchmidt {ι : Type*} (basis : ι → E)
    (T : E →ₗ.[ℂ] E) (z : ℂ) (B : E →L[ℂ] E)
    (R : ResolventAt T z) (Q : ResolventAt (boundedPerturbation T B) z)
    (hR : Summable (fun n => ‖R.inverse (basis n)‖^2)) :
    Summable (fun n => ‖Q.inverse (basis n)‖^2) := by
  rw [perturbed_resolvent_factor T z B R Q]
  exact hilbertSchmidt_left_comp basis R.inverse (1-Q.inverse*B) hR

/-- Resolvent identity across two spectral parameters, in left-factor form. -/
theorem resolvent_spectral_factor (T : E →ₗ.[ℂ] E) (z w : ℂ)
    (R : ResolventAt T z) (Q : ResolventAt T w) :
    Q.inverse=(1+(w-z) • Q.inverse)*R.inverse := by
  ext u
  have h := Q.left_inverse ⟨R.inverse u,R.mem_domain u⟩
  have hr := R.right_inverse u
  have he : T ⟨R.inverse u,R.mem_domain u⟩-w • R.inverse u = u+(z-w) • R.inverse u := by
    calc
      _ = (T ⟨R.inverse u,R.mem_domain u⟩-z • R.inverse u)+(z-w) • R.inverse u := by module
      _ = _ := by rw [hr]
  rw [he,map_add,map_smul] at h
  change Q.inverse u = R.inverse u+(w-z) • Q.inverse (R.inverse u)
  rw [show w-z=-(z-w) by ring,neg_smul]
  simpa only [sub_eq_add_neg] using eq_sub_of_add_eq h

theorem resolvent_hilbertSchmidt_change_parameter {ι : Type*} (basis : ι → E)
    (T : E →ₗ.[ℂ] E) (z w : ℂ) (R : ResolventAt T z) (Q : ResolventAt T w)
    (hR : Summable (fun n => ‖R.inverse (basis n)‖^2)) :
    Summable (fun n => ‖Q.inverse (basis n)‖^2) := by
  rw [resolvent_spectral_factor T z w R Q]
  exact hilbertSchmidt_left_comp basis R.inverse (1+(w-z) • Q.inverse) hR

end
end KN.Analysis
