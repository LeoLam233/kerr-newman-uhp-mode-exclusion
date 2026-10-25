import KN.Angular.FullChiralBasis

noncomputable section
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
namespace KN.Analysis
open Matrix KN.Angular KN.Physics
open scoped ComplexInnerProductSpace

theorem J4_conjTranspose : J4.conjTranspose=J4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [J4,Matrix.conjTranspose_apply]

theorem chiral_J_embedding : J4 * chiralEmbedding = Complex.I • (I4 * chiralEmbedding) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralEmbedding,I4,J4,Matrix.mul_apply,Fin.sum_univ_succ,Complex.I_sq] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem chiral_projection_matrix :
    chiralEmbedding * chiralEmbedding.conjTranspose =
      (1/2:ℂ) • (1-Complex.I • (I4 * J4)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralEmbedding,I4,J4,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.conjTranspose_apply,Complex.conj_I,Complex.I_sq,map_ofNat] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem fullJ_ae (u : FullAngularHilbert) :
    fullJ u =ᵐ[angularMeasure] fun θ => J4.toEuclideanLin (u θ) :=
  J4.toEuclideanLin.toContinuousLinearMap.coeFn_compLpL u

theorem fullJ_involution (u : FullAngularHilbert) : fullJ (fullJ u)=u := by
  apply MeasureTheory.Lp.ext
  filter_upwards [fullJ_ae (fullJ u),fullJ_ae u] with θ h1 h2
  rw [h1,h2]
  change (J4.toEuclideanLin.comp J4.toEuclideanLin) (u θ)=u θ
  rw [← Matrix.toLpLin_mul 2 2 2,J4_sq,Matrix.toLpLin_one]
  rfl

theorem fullJ_symmetric (u v : FullAngularHilbert) :
    ⟪fullJ u,v⟫=⟪u,fullJ v⟫ := by
  rw [MeasureTheory.L2.inner_def,MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [fullJ_ae u,fullJ_ae v] with θ h1 h2
  rw [h1,h2,← LinearMap.adjoint_inner_right,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,J4_conjTranspose]

theorem fullJ_chiral (u : AngularHilbert) :
    fullJ (chiralLpMap u)=Complex.I • fullI (chiralLpMap u) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [fullJ_ae (chiralLpMap u),fullI_ae (chiralLpMap u),
    chiralLpMap_ae u,MeasureTheory.Lp.coeFn_smul Complex.I (fullI (chiralLpMap u))]
    with θ h1 h2 h3 h4
  rw [h4,h1]
  simp only [Pi.smul_apply]
  rw [h2,h3]
  change (J4.toEuclideanLin.comp chiralEmbedding.toEuclideanLin) (u θ)=
    Complex.I • (I4.toEuclideanLin.comp chiralEmbedding.toEuclideanLin) (u θ)
  rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2,chiral_J_embedding]
  simp only [map_smul,LinearMap.smul_apply]

theorem full_chiral_projection (u : FullAngularHilbert) :
    chiralLpMap (chiralProjection u)=(1/2:ℂ) • (u-Complex.I • fullI (fullJ u)) := by
  apply MeasureTheory.Lp.ext
  filter_upwards [chiralLpMap_ae (chiralProjection u),chiralProjection_ae u,
    fullI_ae (fullJ u),fullJ_ae u,
    MeasureTheory.Lp.coeFn_smul (1/2:ℂ) (u-Complex.I • fullI (fullJ u)),
    MeasureTheory.Lp.coeFn_sub u (Complex.I • fullI (fullJ u)),
    MeasureTheory.Lp.coeFn_smul Complex.I (fullI (fullJ u))]
    with θ h1 h2 h3 h4 h5 h6 h7
  rw [h1,h2,h5]
  simp only [Pi.smul_apply]
  rw [h6]
  simp only [Pi.sub_apply]
  rw [h7]
  simp only [Pi.smul_apply]
  rw [h3,h4]
  change (chiralEmbedding.toEuclideanLin.comp chiralEmbedding.conjTranspose.toEuclideanLin) (u θ)=
    (1/2:ℂ) • (u θ-Complex.I • (I4.toEuclideanLin.comp J4.toEuclideanLin) (u θ))
  rw [← Matrix.toLpLin_mul 2 2 2,← Matrix.toLpLin_mul 2 2 2,chiral_projection_matrix]
  simp only [map_smul,map_sub,map_one,LinearMap.smul_apply,LinearMap.sub_apply,LinearMap.id_apply,Matrix.toLpLin_one]

end KN.Analysis
