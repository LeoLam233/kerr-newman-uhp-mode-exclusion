import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Max

namespace KN.Angular
open scoped ComplexInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Completeness of adjoint root spaces detects a full vector. The hypothesis
is density of their linear span, not a basis or eigenvector expansion. -/
theorem zero_of_dense_adjoint_roots {ι : Type*} (roots : ι → E)
    (hd : Dense (Submodule.span ℂ (Set.range roots) : Set E)) (z : E)
    (hz : ∀ i, ⟪roots i,z⟫ = 0) : z = 0 := by
  apply hd.eq_zero_of_inner_right ℂ
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hz i
  | zero => simp
  | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
  | smul a x hx ih => simp [inner_smul_left, ih]

/-- A Riesz projector family detects arbitrary vectors once its adjoint ranges
contain a complete family of generalized root vectors. -/
theorem zero_of_riesz_projections {ι : Type*} (roots : ι → E)
    (hd : Dense (Submodule.span ℂ (Set.range roots) : Set E))
    (P : ι → E →L[ℂ] E)
    (hpair : ∀ i z, ⟪roots i,P i z⟫ = ⟪roots i,z⟫)
    (z : E) (hz : ∀ i, P i z = 0) : z = 0 := by
  apply zero_of_dense_adjoint_roots roots hd z
  intro i
  rw [← hpair i z, hz i]
  simp

/-- Finite Jordan-chain top selection is global in the radial variable: the
higher coefficients vanish identically, not merely at a selected radius. -/
theorem exists_top_coefficient {R F : Type*} [Zero F] (n : ℕ)
    (f : ℕ → R → F) (hfinite : ∀ j, n ≤ j → f j = 0)
    (hne : ∃ j, f j ≠ 0) :
    ∃ j, j < n ∧ f j ≠ 0 ∧ ∀ k, j < k → f k = 0 := by
  classical
  let S := (Finset.range n).filter (fun j => f j ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨j,hj⟩ := hne
    refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hj⟩⟩
    by_contra h
    exact hj (hfinite j (Nat.le_of_not_gt h))
  let j := S.max' hS
  have hj := Finset.mem_filter.mp (Finset.max'_mem S hS)
  refine ⟨j, Finset.mem_range.mp hj.1, hj.2, ?_⟩
  intro k hk
  by_contra hkn
  have hknlt : k < n := by
    by_contra h
    exact hkn (hfinite k (Nat.le_of_not_gt h))
  have hmem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hknlt,hkn⟩
  exact (Nat.not_le_of_gt hk) (Finset.le_max' S k hmem)

end KN.Angular
