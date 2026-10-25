import KN.Analysis.ResolventSelfAdjointBound

namespace KN.Analysis
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

namespace External
/-- Precisely general classical input: surjectivity of nonreal shifts of a
self-adjoint operator. Source: Reed--Simon, Methods of Modern Mathematical
Physics I (1980), Theorem VIII.3, pp. 256--257, followed by a real affine
rescaling of T. The source proof establishes range surjectivity at ±i.
Verified text: https://djvu.online/file/UBTVnOK64NlqI (VIII.2).
This assumes no compactness, eigenbasis, angular realization or completeness.
Boundedness and the sharp resolvent norm are proved separately in Lean. -/
axiom selfAdjoint_nonreal_surjective (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) :
    Function.Surjective (fun u : T.domain => T u-z • (u:E))
end External

def shiftedDomainMap (T : E →ₗ.[ℂ] E) (z : ℂ) : T.domain →ₗ[ℂ] E :=
  T.toFun-z • T.domain.subtype

theorem selfAdjoint_shift_injective (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) : Function.Injective (shiftedDomainMap T z) := by
  intro u v huv
  have hzero : shiftedDomainMap T z (u-v)=0 := by rw [map_sub,huv,sub_self]
  have h := selfAdjoint_shift_lower T hT z (u-v)
  change |z.im| * ‖((u-v : T.domain):E)‖ ≤ ‖shiftedDomainMap T z (u-v)‖ at h
  rw [hzero,norm_zero] at h
  have hn : ‖((u-v : T.domain):E)‖=0 := by nlinarith [abs_pos.mpr hz,norm_nonneg (((u-v : T.domain):E))]
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Actual bounded two-sided inverse constructed from classical surjectivity
and the Lean-proved spectral lower bound. -/
def selfAdjointResolvent (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) : ResolventAt T z := by
  let e := LinearEquiv.ofBijective (shiftedDomainMap T z)
    ⟨selfAdjoint_shift_injective T hT z hz,External.selfAdjoint_nonreal_surjective T hT z hz⟩
  let L : E →ₗ[ℂ] E := T.domain.subtype.comp e.symm.toLinearMap
  have hbound : ∀ u, ‖L u‖≤(1/|z.im|)*‖u‖ := by
    intro u
    have h := selfAdjoint_shift_lower T hT z (e.symm u)
    have he : T (e.symm u)-z • ((e.symm u):E)=u := e.apply_symm_apply u
    rw [he] at h
    change ‖((e.symm u):E)‖ ≤ _
    rw [one_div,← div_eq_inv_mul]
    exact (le_div_iff₀ (abs_pos.mpr hz)).mpr (by nlinarith)
  refine ⟨L.mkContinuous (1/|z.im|) hbound,?_,?_,?_⟩
  · intro u
    exact (e.symm u).property
  · intro u
    exact e.apply_symm_apply u
  · intro u
    exact congrArg Subtype.val (e.symm_apply_apply u)

/-- Full self-adjoint resolvent estimate with actual domain-valued inverses. -/
theorem selfAdjoint_exists_resolvent (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (z : ℂ) (hz : z.im ≠ 0) :
    ∃ R : ResolventAt T z, ‖R.inverse‖≤1/|z.im| :=
  ⟨selfAdjointResolvent T hT z hz,
    selfAdjoint_resolvent_norm T hT z hz (selfAdjointResolvent T hT z hz)⟩

end
end KN.Analysis
