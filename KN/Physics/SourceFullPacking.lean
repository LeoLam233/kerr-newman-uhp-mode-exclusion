import KN.Angular.FullChiralBasis
import KN.Analysis.ResolventBoundaryMap

noncomputable section
namespace KN.Physics
open KN.Angular Matrix MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

def sourceUpperMatrix : Matrix (Fin 4) (Fin 2) ℂ := !![1,0;0,1;0,0;0,0]
def sourceLowerMatrix : Matrix (Fin 4) (Fin 2) ℂ := !![0,0;0,0;1,0;0,1]
def sourceUpperL : AngularHilbert →L[ℂ] FullAngularHilbert :=
  sourceUpperMatrix.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure
def sourceLowerL : AngularHilbert →L[ℂ] FullAngularHilbert :=
  sourceLowerMatrix.toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure

def sourcePack (p q : AngularHilbert) : FullAngularHilbert := sourceUpperL p+sourceLowerL q

def sourcePlusLift : AngularHilbert →L[ℂ] FullAngularHilbert := (1/2:ℂ) • (sourceUpperL+sourceLowerL)
def sourceMinusLift : AngularHilbert →L[ℂ] FullAngularHilbert := (1/2:ℂ) • (sourceUpperL-sourceLowerL)

theorem sourceUpper_ae (u : AngularHilbert) : sourceUpperL u =ᵐ[angularMeasure]
    fun θ => sourceUpperMatrix.toEuclideanLin (u θ) :=
  sourceUpperMatrix.toEuclideanLin.toContinuousLinearMap.coeFn_compLpL u
theorem sourceLower_ae (u : AngularHilbert) : sourceLowerL u =ᵐ[angularMeasure]
    fun θ => sourceLowerMatrix.toEuclideanLin (u θ) :=
  sourceLowerMatrix.toEuclideanLin.toContinuousLinearMap.coeFn_compLpL u

theorem sourceUpper_I (u : AngularHilbert) : fullI (sourceUpperL u)=sourceLowerL u := by
  apply Lp.ext
  filter_upwards [fullI_ae (sourceUpperL u),sourceUpper_ae u,sourceLower_ae u] with θ h1 h2 h3
  rw [h1,h2,h3]
  change (I4.toEuclideanLin.comp sourceUpperMatrix.toEuclideanLin) (u θ)=_
  rw [← Matrix.toLpLin_mul 2 2 2]
  have he : I4*sourceUpperMatrix=sourceLowerMatrix := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [I4,sourceUpperMatrix,sourceLowerMatrix,Matrix.mul_apply,Fin.sum_univ_succ]
  rw [he]

theorem sourceLower_I (u : AngularHilbert) : fullI (sourceLowerL u)=sourceUpperL u := by
  apply Lp.ext
  filter_upwards [fullI_ae (sourceLowerL u),sourceLower_ae u,sourceUpper_ae u] with θ h1 h2 h3
  rw [h1,h2,h3]
  change (I4.toEuclideanLin.comp sourceLowerMatrix.toEuclideanLin) (u θ)=_
  rw [← Matrix.toLpLin_mul 2 2 2]
  have he : I4*sourceLowerMatrix=sourceUpperMatrix := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [I4,sourceUpperMatrix,sourceLowerMatrix,Matrix.mul_apply,Fin.sum_univ_succ]
  rw [he]

theorem sourcePack_piPlus (p q : AngularHilbert) :
    fullPiPlus (sourcePack p q)=sourcePlusLift (p+q) := by
  simp only [fullPiPlus,sourcePack,sourcePlusLift,_root_.smul_apply,
    _root_.add_apply,one_apply_eq_self,map_add,sourceUpper_I,sourceLower_I]
  module

theorem sourcePack_piMinus (p q : AngularHilbert) :
    fullPiMinus (sourcePack p q)=sourceMinusLift (p-q) := by
  simp only [fullPiMinus,sourcePack,sourceMinusLift,_root_.smul_apply,
    _root_.sub_apply,one_apply_eq_self,map_add,map_sub,sourceUpper_I,sourceLower_I]
  module

theorem sourcePack_ae (p q : AngularHilbert) : sourcePack p q =ᵐ[angularMeasure]
    fun θ => WithLp.toLp 2 ![p θ 0,p θ 1,q θ 0,q θ 1] := by
  filter_upwards [Lp.coeFn_add (sourceUpperL p) (sourceLowerL q),sourceUpper_ae p,sourceLower_ae q]
    with θ h1 h2 h3
  change (sourceUpperL p+sourceLowerL q) θ=_
  rw [h1]
  simp only [Pi.add_apply]
  rw [h2,h3]
  ext i
  fin_cases i <;> simp [sourceUpperMatrix,sourceLowerMatrix,Matrix.toLpLin_apply,
    Matrix.mulVec,dotProduct,Fin.sum_univ_succ]

theorem sourcePack_horizons (b : KN.Background) (m : ℤ) (omega : ℂ)
    (p q : ℝ → AngularHilbert) (a d : ℝ)
    (hp : KN.Boundary.HorizonRegular b m omega a (fun r => p r+q r))
    (hm : KN.Boundary.HorizonRegular b m omega d (fun r => p r-q r)) :
    KN.Boundary.HorizonRegular b m omega a (fun r => fullPiPlus (sourcePack (p r) (q r))) ∧
    KN.Boundary.HorizonRegular b m omega d (fun r => fullPiMinus (sourcePack (p r) (q r))) := by
  constructor
  · simpa only [sourcePack_piPlus] using hp.map sourcePlusLift
  · simpa only [sourcePack_piMinus] using hm.map sourceMinusLift

theorem sourcePack_eq_zero_iff (p q : AngularHilbert) :
    sourcePack p q=0 ↔ p=0 ∧ q=0 := by
  constructor
  · intro h
    have he := sourcePack_ae p q
    rw [h] at he
    constructor
    · apply Lp.ext
      filter_upwards [he,Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 4)) (p := 2) (μ := angularMeasure),
        Lp.coeFn_zero (E := AngularFiber) (p := 2) (μ := angularMeasure)] with θ h1 h2 h3
      rw [h2] at h1
      rw [h3]
      ext i
      fin_cases i
      · exact (congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 0) h1).symm
      · exact (congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 1) h1).symm
    · apply Lp.ext
      filter_upwards [he,Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 4)) (p := 2) (μ := angularMeasure),
        Lp.coeFn_zero (E := AngularFiber) (p := 2) (μ := angularMeasure)] with θ h1 h2 h3
      rw [h2] at h1
      rw [h3]
      ext i
      fin_cases i
      · exact (congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 2) h1).symm
      · exact (congrArg (fun v : EuclideanSpace ℂ (Fin 4) => v 3) h1).symm
  · rintro ⟨rfl,rfl⟩
    simp [sourcePack]

end KN.Physics
