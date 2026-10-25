import KN.Analysis.ResolventAdjoint
import Mathlib.Basic.Denumerable

namespace KN.Analysis
set_option backward.isDefEq.respectTransparency false
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Reindex an actual complete orthonormal basis without changing its vectors. -/
def reindexHilbertBasis {ι κ : Type*} (b : HilbertBasis ι ℂ E) (e : κ ≃ ι) :
    HilbertBasis κ ℂ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have he : Set.range (fun k => b (e k))=Set.range b := by
      ext x
      constructor
      · rintro ⟨k,rfl⟩; exact ⟨e k,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨e.symm i,by simp⟩
    simp only [Function.comp_def,he,b.dense_span,le_refl])

@[simp] theorem reindexHilbertBasis_apply {ι κ : Type*} (b : HilbertBasis ι ℂ E)
    (e : κ ≃ ι) (k : κ) : reindexHilbertBasis b e k=b (e k) := by
  simp [reindexHilbertBasis]

/-- The generic completeness theorem is independent of the countable infinite
labeling chosen for the concrete spherical or paired static basis. -/
theorem boundedPerturbation_dense_adjoint_roots_indexed {ι : Type*}
    [Countable ι] [Infinite ι] (T : E →ₗ.[ℂ] E) (hT : IsSelfAdjoint T)
    (B : E →L[ℂ] E) (basis : HilbertBasis ι ℂ E) (z₀ : ℂ)
    (R₀ : ResolventAt T z₀) (hHS : Summable (fun i => ‖R₀.inverse (basis i)‖^2)) :
    Dense (Submodule.span ℂ {u : E | IsGeneralizedRoot (boundedPerturbation T B).adjoint u} : Set E) := by
  let e : ℕ ≃ ι := Classical.choice inferInstance
  apply boundedPerturbation_dense_adjoint_roots T hT B (reindexHilbertBasis basis e) z₀ R₀
  have hs := hHS.comp_injective e.injective
  convert hs using 1
  ext n
  rw [reindexHilbertBasis_apply]
  rfl

end
end KN.Analysis
