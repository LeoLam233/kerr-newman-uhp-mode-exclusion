import KN.Angular.FullOperator
import KN.Angular.StaticHilbertBasis
import KN.Analysis.ChiralDecomposition

namespace KN.Angular
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace

def fullIFiber : EuclideanSpace ℂ (Fin 4) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 4) :=
  KN.Physics.I4.toEuclideanLin.isometryOfInner (by
    intro x y
    rw [← LinearMap.adjoint_inner_right,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x,(KN.Physics.I4.conjTranspose.toEuclideanLin.comp
      KN.Physics.I4.toEuclideanLin) y⟫=⟪x,y⟫
    rw [← Matrix.toLpLin_mul 2 2 2,KN.Analysis.I4_conjTranspose,KN.Physics.I4_sq,
      Matrix.toLpLin_one]
    rfl)

theorem fullI_ae (u : FullAngularHilbert) :
    fullI u =ᵐ[angularMeasure] fun θ => fullIFiber (u θ) :=
  KN.Physics.I4.toEuclideanLin.toContinuousLinearMap.coeFn_compLpL u

theorem fullI_norm (u : FullAngularHilbert) : ‖fullI u‖=‖u‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [fullI_ae u] with θ hθ
  rw [hθ,fullIFiber.norm_map]

def fullIIsometry : FullAngularHilbert →ₗᵢ[ℂ] FullAngularHilbert :=
  { fullI.toLinearMap with norm_map' := fullI_norm }

def partnerChiralIsometry : AngularHilbert →ₗᵢ[ℂ] FullAngularHilbert :=
  fullIIsometry.comp chiralLpIsometry

def chiralProjection : FullAngularHilbert →L[ℂ] AngularHilbert :=
  chiralEmbedding.conjTranspose.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure

theorem chiralProjection_ae (u : FullAngularHilbert) :
    chiralProjection u =ᵐ[angularMeasure] fun θ => chiralEmbedding.conjTranspose.toEuclideanLin (u θ) :=
  chiralEmbedding.conjTranspose.toEuclideanLin.toContinuousLinearMap.coeFn_compLpL u

theorem chiral_fiber_orthogonal (u v : AngularFiber) :
    ⟪chiralIsometry u,fullIFiber (chiralIsometry v)⟫=0 := by
  change ⟪chiralEmbedding.toEuclideanLin u,KN.Physics.I4.toEuclideanLin
    (chiralEmbedding.toEuclideanLin v)⟫=0
  rw [← LinearMap.adjoint_inner_right,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change ⟪u,((chiralEmbedding.conjTranspose.toEuclideanLin.comp KN.Physics.I4.toEuclideanLin).comp
    chiralEmbedding.toEuclideanLin) v⟫=0
  rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2,KN.Analysis.chiral_orthogonal_partner]
  simp

theorem chiralLp_orthogonal (u v : AngularHilbert) :
    ⟪chiralLpIsometry u,partnerChiralIsometry v⟫=0 := by
  rw [L2.inner_def]
  have ha := fullI_ae (chiralLpMap v)
  apply integral_eq_zero_of_ae
  filter_upwards [chiralLpMap_ae u,chiralLpMap_ae v,ha] with θ h1 h2 h3
  change ⟪chiralLpMap u θ,fullI (chiralLpMap v) θ⟫=0
  rw [h1,h3,h2]
  exact chiral_fiber_orthogonal _ _

theorem full_chiral_reconstruction (u : FullAngularHilbert) :
    chiralLpMap (chiralProjection u)+fullI (chiralLpMap (chiralProjection (fullI u)))=u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (chiralLpMap (chiralProjection u))
      (fullI (chiralLpMap (chiralProjection (fullI u)))),
    chiralLpMap_ae (chiralProjection u), chiralProjection_ae u,
    fullI_ae (chiralLpMap (chiralProjection (fullI u))),
    chiralLpMap_ae (chiralProjection (fullI u)),chiralProjection_ae (fullI u),
    fullI_ae u] with θ h0 h1 h2 h3 h4 h5 h6
  rw [h0]
  change chiralLpMap (chiralProjection u) θ+fullI (chiralLpMap (chiralProjection (fullI u))) θ=_
  rw [h1,h2,h3,h4,h5,h6]
  change chiralEmbedding.toEuclideanLin (chiralEmbedding.conjTranspose.toEuclideanLin (u θ))+
    KN.Physics.I4.toEuclideanLin (chiralEmbedding.toEuclideanLin
      (chiralEmbedding.conjTranspose.toEuclideanLin (KN.Physics.I4.toEuclideanLin (u θ))))=u θ
  apply WithLp.ofLp_injective 2
  simpa only [Matrix.toLpLin_apply,WithLp.ofLp_toLp,WithLp.ofLp_add] using
    KN.Analysis.full_fiber_chiral_reconstruction (u θ).ofLp

private theorem closed_submodule_contains_basis_map
    {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (basis : HilbertBasis ι ℂ E) (L : E →L[ℂ] F) (S : Submodule ℂ F)
    (hS : IsClosed (S : Set F)) (hmem : ∀ i, L (basis i) ∈ S) (u : E) : L u ∈ S := by
  let T : Submodule ℂ E := S.comap L.toLinearMap
  have hT : IsClosed (T : Set E) := hS.preimage L.continuous
  have hspan : Submodule.span ℂ (Set.range basis) ≤ T := by
    apply Submodule.span_le.2
    rintro _ ⟨i,rfl⟩
    exact hmem i
  have hcl := (Submodule.span ℂ (Set.range basis)).topologicalClosure_minimal hspan hT
  rw [basis.dense_span] at hcl
  exact hcl (Submodule.mem_top : u ∈ (⊤ : Submodule ℂ E))

def fullBasisVector (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ)
    (i : Bool × Jacobi.StaticLabel k) : FullAngularHilbert :=
  if i.1 then partnerChiralIsometry (Jacobi.staticHilbertBasis b hQ k i.2)
  else chiralLpIsometry (Jacobi.staticHilbertBasis b hQ k i.2)

theorem fullBasisVector_orthonormal (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ) :
    Orthonormal ℂ (fullBasisVector b hQ k) := by
  constructor
  · rintro ⟨s,i⟩
    cases s <;> simp [fullBasisVector,(Jacobi.staticHilbertBasis b hQ k).orthonormal.norm_eq_one]
  · rintro ⟨s,i⟩ ⟨t,j⟩ hne
    cases s <;> cases t
    · have hij : i ≠ j := by intro h; apply hne; cases h; rfl
      change ⟪chiralLpIsometry _,chiralLpIsometry _⟫=0
      rw [LinearIsometry.inner_map_map]
      exact (Jacobi.staticHilbertBasis b hQ k).orthonormal.2 hij
    · exact chiralLp_orthogonal _ _
    · rw [← inner_conj_symm]
      change (starRingEnd ℂ) ⟪chiralLpIsometry _,partnerChiralIsometry _⟫=0
      rw [chiralLp_orthogonal,map_zero]
    · have hij : i ≠ j := by intro h; apply hne; cases h; rfl
      change ⟪partnerChiralIsometry _,partnerChiralIsometry _⟫=0
      rw [LinearIsometry.inner_map_map]
      exact (Jacobi.staticHilbertBasis b hQ k).orthonormal.2 hij

theorem fullBasisVector_dense (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ) :
    Dense (Submodule.span ℂ (Set.range (fullBasisVector b hQ k)) : Set FullAngularHilbert) := by
  let S := (Submodule.span ℂ (Set.range (fullBasisVector b hQ k))).topologicalClosure
  have hp (i : Jacobi.StaticLabel k) :
      chiralLpIsometry (Jacobi.staticHilbertBasis b hQ k i) ∈ S := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨(false,i),rfl⟩
  have hm (i : Jacobi.StaticLabel k) :
      partnerChiralIsometry (Jacobi.staticHilbertBasis b hQ k i) ∈ S := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ⟨(true,i),rfl⟩
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro u _
  rw [← full_chiral_reconstruction u]
  apply S.add_mem
  · exact closed_submodule_contains_basis_map (Jacobi.staticHilbertBasis b hQ k)
      chiralLpIsometry.toContinuousLinearMap S (Submodule.isClosed_topologicalClosure _) hp _
  · exact closed_submodule_contains_basis_map (Jacobi.staticHilbertBasis b hQ k)
      partnerChiralIsometry.toContinuousLinearMap S (Submodule.isClosed_topologicalClosure _) hm _

def fullStaticHilbertBasis (b : KN.Background) (hQ : b.Q ≠ 0) (k : ℤ) :
    HilbertBasis (Bool × Jacobi.StaticLabel k) ℂ FullAngularHilbert :=
  HilbertBasis.mk (fullBasisVector_orthonormal b hQ k) (by
    rw [Submodule.dense_iff_topologicalClosure_eq_top.mp (fullBasisVector_dense b hQ k)])

end
end KN.Angular
