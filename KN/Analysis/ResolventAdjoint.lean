import KN.Analysis.ResolventCompleteness
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace KN.Analysis
noncomputable section
open KN.Angular.External
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Exact adjoint domain and action for bounded perturbations of a self-adjoint
unbounded operator. This supplies adjoint generalized-root completeness too. -/
theorem boundedPerturbation_adjoint (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (B : E →L[ℂ] E) :
    (boundedPerturbation T B).adjoint = boundedPerturbation T B.adjoint := by
  let P := boundedPerturbation T B
  have hd : Dense (P.domain : Set E) := hT.dense_domain
  have hs := T.adjoint_isFormalAdjoint hT.dense_domain
  rw [show T.adjoint=T from hT] at hs
  have hp := P.adjoint_isFormalAdjoint hd
  have hdom : P.adjoint.domain=T.domain := by
    ext u
    constructor
    · intro hu
      have hmem : u ∈ T.adjoint.domain := by
        apply T.mem_adjoint_domain_of_exists
        refine ⟨P.adjoint ⟨u,hu⟩-B.adjoint u,?_⟩
        intro x
        rw [inner_sub_left,B.adjoint_inner_left]
        have hh := hp ⟨u,hu⟩ x
        change ⟪P.adjoint ⟨u,hu⟩,(x:E)⟫=⟪u,T x+B x⟫ at hh
        rw [hh,inner_add_right]
        abel
      rwa [show T.adjoint=T from hT] at hmem
    · intro hu
      apply P.mem_adjoint_domain_of_exists
      refine ⟨T ⟨u,hu⟩+B.adjoint u,?_⟩
      intro x
      change ⟪T ⟨u,hu⟩+B.adjoint u,(x:E)⟫=⟪u,T x+B x⟫
      rw [inner_add_left,inner_add_right,hs ⟨u,hu⟩ x,B.adjoint_inner_left]
  apply LinearPMap.ext (f := P.adjoint) (g := boundedPerturbation T B.adjoint) hdom
  intro u hu hv
  change P.adjoint ⟨u,hu⟩=T ⟨u,hv⟩+B.adjoint u
  apply P.adjoint_apply_eq hd
  intro x
  change ⟪T ⟨u,hv⟩+B.adjoint u,(x:E)⟫=⟪u,T x+B x⟫
  rw [inner_add_left,inner_add_right,hs ⟨u,hv⟩ x,B.adjoint_inner_left]

/-- Both right and adjoint root spaces are complete; the latter is needed for
pointwise detection of angular slices without orthogonality at complex frequency. -/
theorem boundedPerturbation_dense_adjoint_roots
    (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T) (B : E →L[ℂ] E)
    (basis : HilbertBasis ℕ ℂ E) (z₀ : ℂ) (R₀ : ResolventAt T z₀)
    (hHS : Summable (fun n : ℕ => ‖R₀.inverse (basis n)‖^2)) :
    Dense (Submodule.span ℂ {u : E | IsGeneralizedRoot (boundedPerturbation T B).adjoint u} : Set E) := by
  rw [boundedPerturbation_adjoint T hT B]
  exact boundedPerturbation_dense_generalized_roots T hT B.adjoint basis z₀ R₀ hHS

end
end KN.Analysis
