import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace KN.Analysis
noncomputable section
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Domain-aware anticommutation passes to the actual unbounded adjoint.
Only bounded self-adjointness is needed; involutivity is unnecessary. -/
theorem adjoint_anticommutes (T : E →ₗ.[ℂ] E) (hd : Dense (T.domain : Set E))
    (U : E →L[ℂ] E) (hU : IsSelfAdjoint U)
    (hanti : ∀ x : T.domain, ∃ hx : U x ∈ T.domain,
      T ⟨U x,hx⟩ = -U (T x))
    (v : T.adjoint.domain) :
    ∃ hv : U v ∈ T.adjoint.domain,
      T.adjoint ⟨U v,hv⟩ = -U (T.adjoint v) := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hU
  have hs' : ∀ x y : E, ⟪U x,y⟫=⟪x,U y⟫ := hs
  have hw : ∀ x : T.domain, ⟪-U (T.adjoint v),(x:E)⟫=⟪U v,T x⟫ := by
    intro x
    obtain ⟨hx,he⟩ := hanti x
    have ha := T.adjoint_isFormalAdjoint hd v ⟨U x,hx⟩
    change ⟪T.adjoint v,U x⟫=⟪(v:E),T ⟨U x,hx⟩⟫ at ha
    rw [he,inner_neg_right] at ha
    rw [inner_neg_left,hs',ha,neg_neg,hs']
  have hv := T.mem_adjoint_domain_of_exists (U v) ⟨-U (T.adjoint v),hw⟩
  exact ⟨hv,T.adjoint_apply_eq hd ⟨U v,hv⟩ hw⟩

omit [CompleteSpace E] in
/-- The chiral projector formed from two anticommuting symmetries preserves the
actual operator domain and commutes with its action. -/
theorem chiralProjection_commutes (T : E →ₗ.[ℂ] E) (I J : E →L[ℂ] E)
    (hI : ∀ x : T.domain, ∃ hx : I x ∈ T.domain, T ⟨I x,hx⟩= -I (T x))
    (hJ : ∀ x : T.domain, ∃ hx : J x ∈ T.domain, T ⟨J x,hx⟩= -J (T x))
    (x : T.domain) :
    ∃ hp : (1/2:ℂ) • ((x:E)-Complex.I • I (J x)) ∈ T.domain,
      T ⟨(1/2:ℂ) • ((x:E)-Complex.I • I (J x)),hp⟩ =
        (1/2:ℂ) • (T x-Complex.I • I (J (T x))) := by
  obtain ⟨hj,hej⟩ := hJ x
  obtain ⟨hi,hei⟩ := hI ⟨J x,hj⟩
  have he : T ⟨I (J x),hi⟩=I (J (T x)) := by
    rw [hei,hej,map_neg,neg_neg]
  let y : T.domain := (1/2:ℂ) • (x-Complex.I • ⟨I (J x),hi⟩)
  refine ⟨y.property,?_⟩
  change T y=_
  dsimp only [y]
  change T.toFun ((1/2:ℂ) • (x-Complex.I • ⟨I (J x),hi⟩)) = _
  rw [map_smul,map_sub,map_smul]
  change T.toFun ⟨I (J x),hi⟩=I (J (T x)) at he
  rw [he]
  rfl

end
end KN.Analysis
