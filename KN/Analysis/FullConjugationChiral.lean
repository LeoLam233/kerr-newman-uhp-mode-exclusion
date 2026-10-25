import KN.Analysis.FullConjugation

noncomputable section
namespace KN.Analysis
open KN.Angular KN.Physics MeasureTheory Matrix
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def chiralRealSign : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

def chiralRealMap : AngularHilbert →L[ℝ] AngularHilbert :=
  ((chiralRealSign.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure).restrictScalars ℝ).comp
    ((conjugateFiber 2).toContinuousLinearMap.compLpL 2 angularMeasure)

theorem chiral_real_fiber (u : AngularFiber) :
    fullIFiber (conjugateFiber 4 (chiralIsometry u))=
      chiralIsometry (chiralRealSign.toEuclideanLin (conjugateFiber 2 u)) := by
  ext i
  fin_cases i <;> simp [fullIFiber,conjugateFiber_apply,chiralIsometry,
    Matrix.toLpLin_apply,chiralRealSign,chiralEmbedding,I4,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ,map_ofNat] <;> ring

theorem chiralRealMap_ae (u : AngularHilbert) :
    chiralRealMap u =ᵐ[angularMeasure] fun θ =>
      chiralRealSign.toEuclideanLin (conjugateFiber 2 (u θ)) := by
  let L := (conjugateFiber 2).toContinuousLinearMap.compLpL 2 angularMeasure
  filter_upwards [chiralRealSign.toEuclideanLin.toContinuousLinearMap.coeFn_compLpL (L u),
    (conjugateFiber 2).toContinuousLinearMap.coeFn_compLpL u] with θ h1 h2
  change ((chiralRealSign.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure) (L u)) θ = _
  rw [h1]
  change chiralRealSign.toEuclideanLin (L u θ)=_
  rw [h2]
  rfl

theorem fullRealStructure_chiral (u : AngularHilbert) :
    fullRealStructure (chiralLpMap u)=chiralLpMap (chiralRealMap u) := by
  apply Lp.ext
  filter_upwards [fullI_ae (fullConjugate (chiralLpMap u)),
    fullConjugate_ae (chiralLpMap u),chiralLpMap_ae u,
    chiralLpMap_ae (chiralRealMap u),chiralRealMap_ae u] with θ h1 h2 h3 h4 h5
  change fullI (fullConjugate (chiralLpMap u)) θ=chiralLpMap (chiralRealMap u) θ
  rw [h1,h2,h3,h4,h5]
  exact chiral_real_fiber (u θ)

end KN.Analysis
