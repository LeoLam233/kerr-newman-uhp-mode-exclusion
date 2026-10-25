import KN.Angular.FullChiralBasis

namespace KN.Angular
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace

theorem chiralProjection_inner (u : AngularHilbert) (v : FullAngularHilbert) :
    ⟪chiralLpMap u,v⟫=⟪u,chiralProjection v⟫ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [chiralLpMap_ae u,chiralProjection_ae v] with θ hu hv
  rw [hu,hv]
  change ⟪chiralEmbedding.toEuclideanLin (u θ),v θ⟫=⟪u θ,chiralEmbedding.conjTranspose.toEuclideanLin (v θ)⟫
  rw [← LinearMap.adjoint_inner_right,← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem chiralProjection_leftInverse (u : AngularHilbert) :
    chiralProjection (chiralLpMap u)=u := by
  apply Lp.ext
  filter_upwards [chiralProjection_ae (chiralLpMap u),chiralLpMap_ae u] with θ hp he
  rw [hp,he]
  change (chiralEmbedding.conjTranspose.toEuclideanLin.comp chiralEmbedding.toEuclideanLin) (u θ)=u θ
  rw [← Matrix.toLpLin_mul 2 2 2,chiral_isometry,Matrix.toLpLin_one]
  rfl

theorem fullChiralProjection_symmetric (u v : FullAngularHilbert) :
    ⟪chiralLpMap (chiralProjection u),v⟫=⟪u,chiralLpMap (chiralProjection v)⟫ := by
  rw [chiralProjection_inner,← inner_conj_symm u, chiralProjection_inner,inner_conj_symm]

theorem fullI_involution (u : FullAngularHilbert) : fullI (fullI u)=u := by
  apply Lp.ext
  filter_upwards [fullI_ae (fullI u),fullI_ae u] with θ h1 h2
  rw [h1,h2]
  change (KN.Physics.I4.toEuclideanLin.comp KN.Physics.I4.toEuclideanLin) (u θ)=u θ
  rw [← Matrix.toLpLin_mul 2 2 2,KN.Physics.I4_sq,Matrix.toLpLin_one]
  rfl

def ChiralVector (u : FullAngularHilbert) : Prop := ∃ a : AngularHilbert, u=chiralLpMap a

end
end KN.Angular
