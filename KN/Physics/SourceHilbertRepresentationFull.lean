import KN.Physics.SourceHilbertRepresentation
import KN.Physics.SourceFullPacking
import KN.Physics.SourcePDEFour

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace KN.Physics
open KN.Angular

lemma sourceFullTransform_ae (positive : Bool) (b : KN.Background) {r : ℝ}
    (hr : b.rPlus<r) (high low : SourceAngularHilbert) :
    sourcePack (sourceHilbertTransform positive b r high low).1
      (sourceHilbertTransform positive b r high low).2 =ᵐ[angularMeasure]
    fun t => WithLp.toLp 2
      (joinSource (sourceTransform positive b r t (sourceFiberPack high low t)).1
        (sourceTransform positive b r t (sourceFiberPack high low t)).2) := by
  filter_upwards [sourcePack_ae (sourceHilbertTransform positive b r high low).1
    (sourceHilbertTransform positive b r high low).2,
    sourceHilbertTransform_ae positive b hr high low] with t hp ht
  rw [hp]
  ext j
  fin_cases j
  · exact congrFun ht.1 0
  · exact congrFun ht.1 1
  · exact congrFun ht.2 0
  · exact congrFun ht.2 1

/-- The complete source Hilbert field is represented by the literal pointwise
sourceFullVector used in the verified differential transformation. -/
theorem sourceFullTransform_represents (positive : Bool) (b : KN.Background) {r : ℝ}
    (hr : b.rPlus<r) (high low : SourceAngularHilbert) (u : ℝ → ℝ → Fin 4 → ℂ)
    (hhigh : (fun t => high t) =ᵐ[KN.Kerr.sphericalMeasure]
      fun t => WithLp.toLp 2 ![u r t 0,u r t 2])
    (hlow : (fun t => low t) =ᵐ[KN.Kerr.sphericalMeasure]
      fun t => WithLp.toLp 2 ![u r t 1,u r t 3]) :
    sourcePack (sourceHilbertTransform positive b r high low).1
      (sourceHilbertTransform positive b r high low).2 =ᵐ[angularMeasure]
      fun t => WithLp.toLp 2 (sourceFullVector positive b u r t) := by
  filter_upwards [sourceFullTransform_ae positive b hr high low,
    source_ae_to_angular hhigh,source_ae_to_angular hlow] with t ht hh hl
  rw [ht]
  have he : sourceFiberPack high low t=u r t := by
    ext j
    fin_cases j
    · exact congrArg (fun v : AngularFiber => v 0) hh
    · exact congrArg (fun v : AngularFiber => v 0) hl
    · exact congrArg (fun v : AngularFiber => v 1) hh
    · exact congrArg (fun v : AngularFiber => v 1) hl
  rw [he]
  rfl

end KN.Physics
