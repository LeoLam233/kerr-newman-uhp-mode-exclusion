import KN.Physics.SourceHilbertBoundaryEvenOdd
import KN.Physics.SourceHilbertBoundaryOriginal
import KN.Physics.PhysicalTransform

noncomputable section
open Matrix MeasureTheory
namespace KN.Physics
open KN.Angular

/-- Fixed electromagnetic normalization in the original two-component source. -/
def sourceChargeL (q : ℂ) : AngularHilbert →L[ℂ] AngularHilbert :=
  (Matrix.diagonal ![1,-2*q]).toEuclideanLin.toContinuousLinearMap.compLpL 2 angularMeasure

/-- Hilbert lifts of the literal adjugate and conjugate-transpose source matrices.
The half-sum formulas equal those matrices by source_sum_factor/source_difference. -/
def sourceAdjL (b : KN.Background) (r : ℝ) : AngularHilbert →L[ℂ] AngularHilbert :=
  (1/2:ℂ) • ((Real.sqrt (b.Delta r):ℂ) • horizonEvenL b r+horizonOddL b r)
def sourceStarL (b : KN.Background) (r : ℝ) : AngularHilbert →L[ℂ] AngularHilbert :=
  (1/2:ℂ) • ((Real.sqrt (b.Delta r):ℂ) • horizonEvenL b r-horizonOddL b r)

/-- The actual source transform of original spherical-measure high/low fields.
The fixed sqrt-sine embedding, charge normalization, radial power, chiral mixing,
and original source matrices are all present. No transformed boundary is built in. -/
def sourceHilbertTransform (positive : Bool) (b : KN.Background) (r : ℝ)
    (high low : SourceAngularHilbert) : AngularHilbert × AngularHilbert :=
  let U := sourceChargeL (transformCharge positive b) (sourceAngularEmbedding high)
  let V := sourceChargeL (transformCharge positive b) (sourceAngularEmbedding low)
  let scale : ℂ := (Real.rpow (b.Delta r) (if positive then (5:ℝ)/4 else (-3:ℝ)/4):ℂ)
  let mix := Complex.I*transformMix positive b r
  (scale • sourceAdjL b r (U+mix • V), scale • sourceStarL b r (U-mix • V))

lemma sourceAdjL_add_star (b : KN.Background) (r : ℝ) :
    sourceAdjL b r+sourceStarL b r=(Real.sqrt (b.Delta r):ℂ) • horizonEvenL b r := by
  unfold sourceAdjL sourceStarL
  module
lemma sourceAdjL_sub_star (b : KN.Background) (r : ℝ) :
    sourceAdjL b r-sourceStarL b r=horizonOddL b r := by
  unfold sourceAdjL sourceStarL
  module

end KN.Physics
