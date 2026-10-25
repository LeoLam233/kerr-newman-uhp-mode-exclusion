import KN.Angular.ExternalHintz

namespace KN.Angular
noncomputable section
open scoped ComplexInnerProductSpace

/-- The actual maximal first-order graph is single-valued, using the exact
published full-space self-adjoint realization and proved chiral graph equivalence. -/
theorem staticGraph_single_valued (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (u x y : AngularHilbert)
    (hx : StaticGraph σ b.beta m u x) (hy : StaticGraph σ b.beta m u y) : x=y := by
  obtain ⟨T,hgraph,_⟩ := External.hintz_2026_v1_lemma1_zero_frequency b hQ σ hσ m
  obtain ⟨hu,hx'⟩ := (hgraph _ _).mpr ((fullStaticGraph_chiral_iff σ b.beta m u x).mpr hx)
  obtain ⟨hu',hy'⟩ := (hgraph _ _).mpr ((fullStaticGraph_chiral_iff σ b.beta m u y).mpr hy)
  apply chiralLpIsometry.injective
  change chiralLpMap x = chiralLpMap y
  exact hx'.symm.trans hy'

/-- Symmetry of the actual first-order maximal angular graph at zero frequency. -/
theorem staticGraph_symmetric (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (u v x y : AngularHilbert)
    (hx : StaticGraph σ b.beta m u x) (hy : StaticGraph σ b.beta m v y) :
    ⟪x,v⟫ = ⟪u,y⟫ := by
  obtain ⟨T,hgraph,hself,_⟩ := External.hintz_2026_v1_lemma1_zero_frequency b hQ σ hσ m
  obtain ⟨hu,hx'⟩ := (hgraph _ _).mpr ((fullStaticGraph_chiral_iff σ b.beta m u x).mpr hx)
  obtain ⟨hv,hy'⟩ := (hgraph _ _).mpr ((fullStaticGraph_chiral_iff σ b.beta m v y).mpr hy)
  have hf := T.adjoint_isFormalAdjoint hself.dense_domain
  rw [show T.adjoint=T from hself] at hf
  have heq := hf ⟨chiralLpMap u,hu⟩ ⟨chiralLpMap v,hv⟩
  change ⟪T ⟨chiralLpMap u,hu⟩,chiralLpMap v⟫ =
    ⟪chiralLpMap u,T ⟨chiralLpMap v,hv⟩⟫ at heq
  rw [hx',hy'] at heq
  change ⟪chiralLpIsometry x,chiralLpIsometry v⟫ =
    ⟪chiralLpIsometry u,chiralLpIsometry y⟫ at heq
  simpa only [LinearIsometry.inner_map_map] using heq

theorem static_expectation_real (b : KN.Background) (hQ : b.Q ≠ 0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (u x : AngularHilbert)
    (hx : StaticGraph σ b.beta m u x) :
    (starRingEnd ℂ) ⟪u,x⟫ = ⟪u,x⟫ := by
  rw [inner_conj_symm]
  exact staticGraph_symmetric b hQ σ hσ m u u x x hx hx

end
end KN.Angular
