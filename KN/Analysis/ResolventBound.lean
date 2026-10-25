import KN.Analysis.ResolventPerturbation

namespace KN.Analysis
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Sharp elementary perturbation estimate for actual two-sided resolvents. -/
theorem perturbed_resolvent_norm (T : E →ₗ.[ℂ] E) (z : ℂ) (B : E →L[ℂ] E)
    (R : ResolventAt T z) (Q : ResolventAt (boundedPerturbation T B) z)
    (a : ℝ) (ha : ‖B‖ < a) (hR : ‖R.inverse‖ ≤ 1/a) :
    ‖Q.inverse‖ ≤ 1/(a-‖B‖) := by
  have ha0 : 0<a := lt_of_le_of_lt (norm_nonneg B) ha
  have had : 0<a-‖B‖ := sub_pos.mpr ha
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have hright := Q.right_inverse u
  have hleft := R.left_inverse ⟨Q.inverse u,Q.mem_domain u⟩
  change T ⟨Q.inverse u,Q.mem_domain u⟩+B (Q.inverse u)-z • Q.inverse u=u at hright
  have he : T ⟨Q.inverse u,Q.mem_domain u⟩-z • Q.inverse u=u-B (Q.inverse u) := by
    apply eq_sub_of_add_eq
    calc
      _ = T ⟨Q.inverse u,Q.mem_domain u⟩+B (Q.inverse u)-z • Q.inverse u := by abel
      _ = u := hright
  rw [he] at hleft
  have hbound : ‖Q.inverse u‖ ≤ (1/a)*(‖u‖+‖B‖*‖Q.inverse u‖) := by
    calc
      _ = ‖R.inverse (u-B (Q.inverse u))‖ := congrArg norm hleft.symm
      _ ≤ ‖R.inverse‖*‖u-B (Q.inverse u)‖ := R.inverse.le_opNorm _
      _ ≤ (1/a)*‖u-B (Q.inverse u)‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ ≤ (1/a)*(‖u‖+‖B‖*‖Q.inverse u‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (norm_sub_le _ _).trans (add_le_add le_rfl (B.le_opNorm _))
  have hmul : a*‖Q.inverse u‖ ≤ ‖u‖+‖B‖*‖Q.inverse u‖ := by
    have hh := mul_le_mul_of_nonneg_left hbound (le_of_lt ha0)
    field_simp at hh
    nlinarith
  have hx : (a-‖B‖)*‖Q.inverse u‖ ≤ ‖u‖ := by nlinarith
  rw [one_div, ← div_eq_inv_mul]
  exact (le_div_iff₀ had).mpr (by nlinarith)

variable [CompleteSpace E]

/-- Bounded perturbations have resolvents throughout the strip complement.
The parameter a is |Im z| when the base operator is self-adjoint. -/
theorem exists_perturbed_resolvent (T : E →ₗ.[ℂ] E) (z : ℂ) (B : E →L[ℂ] E)
    (R : ResolventAt T z) (a : ℝ) (ha : ‖B‖<a) (hR : ‖R.inverse‖≤1/a) :
    ∃ Q : ResolventAt (boundedPerturbation T B) z, ‖Q.inverse‖≤1/(a-‖B‖) := by
  have ha0 : 0<a := lt_of_le_of_lt (norm_nonneg B) ha
  have hsmall : ‖B*R.inverse‖<1 := by
    calc
      _ ≤ ‖B‖*‖R.inverse‖ := norm_mul_le _ _
      _ ≤ ‖B‖*(1/a) := mul_le_mul_of_nonneg_left hR (norm_nonneg _)
      _ < 1 := by rw [← div_eq_mul_one_div]; exact (div_lt_one ha0).mpr ha
  let Q := neumannResolvent T z R B hsmall
  exact ⟨Q,perturbed_resolvent_norm T z B R Q a ha hR⟩

end
end KN.Analysis
