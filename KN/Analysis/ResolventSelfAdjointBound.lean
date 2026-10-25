import KN.Analysis.ResolventBound
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace KN.Analysis
noncomputable section
open KN.Angular.External
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Symmetry yields the usual nonreal spectral lower bound on the actual domain. -/
theorem selfAdjoint_shift_lower (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (z : ℂ) (u : T.domain) : |z.im| *‖(u:E)‖ ≤ ‖T u-z • (u:E)‖ := by
  have hs := T.adjoint_isFormalAdjoint hT.dense_domain
  rw [show T.adjoint=T from hT] at hs
  have hre : (⟪(u:E),T u⟫).im=0 := by
    have hstar : (starRingEnd ℂ) ⟪(u:E),T u⟫ = ⟪(u:E),T u⟫ := by
      rw [inner_conj_symm]
      exact hs u u
    have h := congrArg Complex.im hstar
    change -(⟪(u:E),T u⟫).im = (⟪(u:E),T u⟫).im at h
    linarith
  have him : (⟪(u:E),T u-z • (u:E)⟫).im = -z.im*‖(u:E)‖^2 := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    change (⟪(u:E),T u⟫ - z*(‖(u:E)‖:ℂ)^2).im = _
    rw [← Complex.ofReal_pow]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hre]
    ring
  have hb := (Complex.abs_im_le_norm (⟪(u:E),T u-z • (u:E)⟫)).trans
    (norm_inner_le_norm (u:E) (T u-z • (u:E)))
  rw [him,abs_mul,abs_neg] at hb
  rw [abs_of_nonneg (sq_nonneg ‖(u:E)‖)] at hb
  by_cases hu : ‖(u:E)‖=0
  · rw [hu,mul_zero]; exact norm_nonneg _
  · have hup : 0<‖(u:E)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
    nlinarith

/-- Every existing self-adjoint nonreal resolvent has the sharp norm bound. -/
theorem selfAdjoint_resolvent_norm (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) (R : ResolventAt T z) : ‖R.inverse‖≤1/|z.im| := by
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  have h := selfAdjoint_shift_lower T hT z ⟨R.inverse u,R.mem_domain u⟩
  rw [R.right_inverse] at h
  rw [one_div, ← div_eq_inv_mul]
  exact (le_div_iff₀ hzpos).mpr (by nlinarith)

end
end KN.Analysis
