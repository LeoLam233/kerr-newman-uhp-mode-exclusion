import KN.Physics.SourceHilbertBoundaryTransform

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix MeasureTheory Set
namespace KN.Physics
open KN.Angular

lemma sourceAdj_physical (b : KN.Background) (r t : ℝ) :
    sourceAdj b.M b.Q b.a r (Real.sqrt (b.Delta r)) (Real.sin t) (Real.cos t)=
      (physicalSourceMatrix b r t).adjugate := by
  simp only [physicalSourceMatrix,sourceMatrix,Matrix.adjugate_fin_two_of,sourceAdj]
  congr 1; ring

lemma sourceStar_physical (b : KN.Background) (r t : ℝ) :
    sourceStar b.M b.Q b.a r (Real.sqrt (b.Delta r)) (Real.sin t) (Real.cos t)=
      (physicalSourceMatrix b r t).conjTranspose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceStar,physicalSourceMatrix,sourceMatrix,Matrix.conjTranspose_apply,
      ← Complex.sin_conj,← Complex.cos_conj,Complex.conj_ofReal,Complex.conj_I] <;> ring

lemma sourceAdjL_ae (b : KN.Background) {r : ℝ} (hr : b.rPlus≤r) (u : AngularHilbert) :
    sourceAdjL b r u =ᵐ[angularMeasure] fun t => WithLp.toLp 2
      ((physicalSourceMatrix b r t).adjugate *ᵥ (u t : Fin 2 → ℂ)) := by
  let E := horizonEvenL b r u
  let O := horizonOddL b r u
  let c : ℂ := Real.sqrt (b.Delta r)
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (c • E+O),Lp.coeFn_add (c • E) O,
    Lp.coeFn_smul c E,horizonEvenL_ae b hr u,horizonOddL_ae b hr u] with t h0 h1 h2 hE hO
  change ((1/2:ℂ) • (c • E+O)) t=_
  rw [h0]
  change (1/2:ℂ) • (c • E+O) t=_
  rw [h1]
  change (1/2:ℂ) • ((c • E) t+O t)=_
  rw [h2]
  change (1/2:ℂ) • (c • (horizonEvenL b r u) t+(horizonOddL b r u) t)=_
  rw [hE,hO,← sourceAdj_physical]
  ext j
  fin_cases j <;> simp [c,horizonEven,horizonOdd,sourceAdj,Matrix.mulVec] <;> ring

lemma sourceStarL_ae (b : KN.Background) {r : ℝ} (hr : b.rPlus≤r) (u : AngularHilbert) :
    sourceStarL b r u =ᵐ[angularMeasure] fun t => WithLp.toLp 2
      ((physicalSourceMatrix b r t).conjTranspose *ᵥ (u t : Fin 2 → ℂ)) := by
  let E := horizonEvenL b r u
  let O := horizonOddL b r u
  let c : ℂ := Real.sqrt (b.Delta r)
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (c • E-O),Lp.coeFn_sub (c • E) O,
    Lp.coeFn_smul c E,horizonEvenL_ae b hr u,horizonOddL_ae b hr u] with t h0 h1 h2 hE hO
  change ((1/2:ℂ) • (c • E-O)) t=_
  rw [h0]
  change (1/2:ℂ) • (c • E-O) t=_
  rw [h1]
  change (1/2:ℂ) • ((c • E) t-O t)=_
  rw [h2]
  change (1/2:ℂ) • (c • (horizonEvenL b r u) t-(horizonOddL b r u) t)=_
  rw [hE,hO,← sourceStar_physical]
  ext j
  fin_cases j <;> simp [c,horizonEven,horizonOdd,sourceStar,Matrix.mulVec] <;> ring

lemma sourceChargeEmbedding_ae (q : ℂ) (u : SourceAngularHilbert) :
    sourceChargeL q (sourceAngularEmbedding u) =ᵐ[angularMeasure] fun t =>
      (Real.sqrt (Real.sin t):ℂ) • WithLp.toLp 2 ![u t 0,-2*q*u t 1] := by
  let A := (Matrix.diagonal ![1,-2*q]).toEuclideanLin.toContinuousLinearMap
  filter_upwards [A.coeFn_compLpL (sourceAngularEmbedding u),sqrtSinLift_ae u] with t hA hu
  change (A.compLpL 2 angularMeasure (sourceAngularEmbedding u)) t=_
  rw [hA]
  change A (sqrtSinLift u t)=_
  rw [hu]
  ext j
  fin_cases j <;> simp [A,sqrtSinAction,Matrix.toLpLin_apply,Matrix.mulVec,Matrix.diagonal]

/-- Original high and low angular fibers packed in the manuscript source order. -/
def sourceFiberPack (high low : SourceAngularHilbert) (t : ℝ) : Fin 4 → ℂ :=
  ![high t 0,low t 0,high t 1,low t 1]

lemma sourceHilbertTransform_ae (positive : Bool) (b : KN.Background) {r : ℝ}
    (hr : b.rPlus<r) (high low : SourceAngularHilbert) :
    ∀ᵐ t ∂angularMeasure,
      ((sourceHilbertTransform positive b r high low).1 t : Fin 2 → ℂ)=
          (sourceTransform positive b r t (sourceFiberPack high low t)).1 ∧
      ((sourceHilbertTransform positive b r high low).2 t : Fin 2 → ℂ)=
          (sourceTransform positive b r t (sourceFiberPack high low t)).2 := by
  let U := sourceChargeL (transformCharge positive b) (sourceAngularEmbedding high)
  let V := sourceChargeL (transformCharge positive b) (sourceAngularEmbedding low)
  let scale : ℂ := Real.rpow (b.Delta r) (if positive then (5:ℝ)/4 else (-3:ℝ)/4)
  let mix := Complex.I*transformMix positive b r
  filter_upwards [Lp.coeFn_smul scale (sourceAdjL b r (U+mix • V)),
    Lp.coeFn_smul scale (sourceStarL b r (U-mix • V)),
    sourceAdjL_ae b hr.le (U+mix • V),sourceStarL_ae b hr.le (U-mix • V),
    Lp.coeFn_add U (mix • V),Lp.coeFn_sub U (mix • V),Lp.coeFn_smul mix V,
    sourceChargeEmbedding_ae (transformCharge positive b) high,
    sourceChargeEmbedding_ae (transformCharge positive b) low] with t hp hm hA hS ha hs hv hu hv0
  change ((scale • sourceAdjL b r (U+mix • V)) t : Fin 2 → ℂ)=_ ∧
    ((scale • sourceStarL b r (U-mix • V)) t : Fin 2 → ℂ)=_
  rw [hp,hm]
  change (scale • (sourceAdjL b r (U+mix • V)) t : Fin 2 → ℂ)=_ ∧
    (scale • (sourceStarL b r (U-mix • V)) t : Fin 2 → ℂ)=_
  rw [hA,hS]
  simp only [sourceTransform]
  constructor
  · change scale • ((physicalSourceMatrix b r t).adjugate *ᵥ ((U+mix • V) t : Fin 2 → ℂ))=_
    rw [← Matrix.mulVec_smul]
    congr 1
    rw [ha]
    change scale • ((U t+(mix • V) t) : Fin 2 → ℂ)=_
    rw [hv]
    change scale • ((U t+mix • V t) : Fin 2 → ℂ)=_
    dsimp only [U,V]
    rw [hu,hv0]
    ext j
    fin_cases j <;> cases positive <;> simp [sourceFiberPack,chiralInput,transformScale,scale,mix] <;> ring
  · change scale • ((physicalSourceMatrix b r t).conjTranspose *ᵥ ((U-mix • V) t : Fin 2 → ℂ))=_
    rw [← Matrix.mulVec_smul]
    congr 1
    rw [hs]
    change scale • ((U t-(mix • V) t) : Fin 2 → ℂ)=_
    rw [hv]
    change scale • ((U t-mix • V t) : Fin 2 → ℂ)=_
    dsimp only [U,V]
    rw [hu,hv0]
    ext j
    fin_cases j <;> cases positive <;> simp [sourceFiberPack,chiralInput,transformScale,scale,mix] <;> ring

end KN.Physics
