import KN.Physics.SourceHilbertRepresentation
import KN.Physics.SourceFullPacking
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace KN.Physics
open KN.Angular

/-- Actual source-transform injectivity in L², obtained from its pointwise
matrix representation and the fixed isometric original-measure embedding. -/
theorem sourceHilbertTransform_zero (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0)
    {r : ℝ} (hr : b.rPlus<r) (high low : SourceAngularHilbert)
    (hz : sourceHilbertTransform positive b r high low=0) : high=0 ∧ low=0 := by
  have hzero : (fun t => (0:AngularHilbert) t) =ᵐ[angularMeasure] (fun _ => (0:AngularFiber)) :=
    Lp.coeFn_zero AngularFiber 2 angularMeasure
  have hpack : ∀ᵐ t ∂angularMeasure, sourceFiberPack high low t=0 := by
    filter_upwards [sourceHilbertTransform_ae positive b hr high low,hzero,
      ae_restrict_mem measurableSet_Ioo] with t ht h0 hθ
    rw [hz] at ht
    have hp : (sourceTransform positive b r t (sourceFiberPack high low t)).1=0 := by
      rw [← ht.1]
      exact congrArg (fun v : AngularFiber => (v : Fin 2 → ℂ)) h0
    have hm : (sourceTransform positive b r t (sourceFiberPack high low t)).2=0 := by
      rw [← ht.2]
      exact congrArg (fun v : AngularFiber => (v : Fin 2 → ℂ)) h0
    exact sourceTransform_zero positive b hQ hr hθ.1 hθ.2 _ (Prod.ext hp hm)
  have hhigh : ∀ᵐ t ∂angularMeasure, high t=0 := by
    filter_upwards [hpack] with t ht
    ext j
    fin_cases j
    · simpa [sourceFiberPack] using congrFun ht 0
    · simpa [sourceFiberPack] using congrFun ht 2
  have hlow : ∀ᵐ t ∂angularMeasure, low t=0 := by
    filter_upwards [hpack] with t ht
    ext j
    fin_cases j
    · simpa [sourceFiberPack] using congrFun ht 1
    · simpa [sourceFiberPack] using congrFun ht 3
  have recover (u : SourceAngularHilbert) (hu : ∀ᵐ t ∂angularMeasure, u t=0) : u=0 := by
    apply sourceAngularEmbedding.injective
    rw [map_zero]
    apply Lp.ext
    filter_upwards [sqrtSinLift_ae u,hu,hzero] with t ht hu h0
    change sqrtSinLift u t=(0:AngularHilbert) t
    rw [ht,h0]
    simp only [sqrtSinAction,hu,smul_zero]
  exact ⟨recover high hhigh,recover low hlow⟩

/-- A continuous original angular representative which is zero in its genuine
spherical L² space vanishes pointwise throughout the open sphere chart. -/
theorem source_representative_zero (u : SourceAngularHilbert) (f : ℝ → AngularFiber)
    (hf : ContinuousOn f (Ioo 0 Real.pi))
    (he : (fun t => u t) =ᵐ[KN.Kerr.sphericalMeasure] f) (hu : u=0) :
    EqOn f 0 (Ioo 0 Real.pi) := by
  have hz : (fun t => (0:SourceAngularHilbert) t) =ᵐ[KN.Kerr.sphericalMeasure]
      (fun _ => (0:AngularFiber)) := Lp.coeFn_zero AngularFiber 2 KN.Kerr.sphericalMeasure
  have ha : f =ᵐ[KN.Kerr.sphericalMeasure] 0 := by
    rw [hu] at he
    exact he.symm.trans hz
  exact Measure.eqOn_open_of_ae_eq (source_ae_to_angular ha) isOpen_Ioo hf continuousOn_const

/-- Vanishing of the full four-component transformed Hilbert field recovers
both original source L² fields, with no assumed inverse map. -/
theorem sourceFullTransform_zero (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0)
    {r : ℝ} (hr : b.rPlus<r) (high low : SourceAngularHilbert)
    (hz : sourcePack (sourceHilbertTransform positive b r high low).1
      (sourceHilbertTransform positive b r high low).2=0) : high=0 ∧ low=0 := by
  have hp := (sourcePack_eq_zero_iff _ _).mp hz
  exact sourceHilbertTransform_zero positive b hQ hr high low (Prod.ext hp.1 hp.2)

/-- Pointwise recovery of all four original physical components in the open
angular chart, from the genuine original spherical-measure representatives. -/
theorem sourceFullTransform_original_pointwise_zero
    (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) {r : ℝ} (hr : b.rPlus<r)
    (high low : SourceAngularHilbert) (u : ℝ → Fin 4 → ℂ)
    (hu : ContinuousOn u (Ioo 0 Real.pi))
    (hhigh : (fun t => high t) =ᵐ[KN.Kerr.sphericalMeasure]
      fun t => WithLp.toLp 2 ![u t 0,u t 2])
    (hlow : (fun t => low t) =ᵐ[KN.Kerr.sphericalMeasure]
      fun t => WithLp.toLp 2 ![u t 1,u t 3])
    (hz : sourcePack (sourceHilbertTransform positive b r high low).1
      (sourceHilbertTransform positive b r high low).2=0) : EqOn u 0 (Ioo 0 Real.pi) := by
  have hh := sourceFullTransform_zero positive b hQ hr high low hz
  have hch : ContinuousOn (fun t => WithLp.toLp 2 ![u t 0,u t 2]) (Ioo 0 Real.pi) := by
    apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    apply continuousOn_pi.mpr
    intro j
    fin_cases j
    · change ContinuousOn (fun t => u t 0) (Ioo 0 Real.pi)
      exact (continuous_apply 0).comp_continuousOn hu
    · change ContinuousOn (fun t => u t 2) (Ioo 0 Real.pi)
      exact (continuous_apply 2).comp_continuousOn hu
  have hcl : ContinuousOn (fun t => WithLp.toLp 2 ![u t 1,u t 3]) (Ioo 0 Real.pi) := by
    apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    apply continuousOn_pi.mpr
    intro j
    fin_cases j
    · change ContinuousOn (fun t => u t 1) (Ioo 0 Real.pi)
      exact (continuous_apply 1).comp_continuousOn hu
    · change ContinuousOn (fun t => u t 3) (Ioo 0 Real.pi)
      exact (continuous_apply 3).comp_continuousOn hu
  have hh0 := source_representative_zero high _ hch hhigh hh.1
  have hl0 := source_representative_zero low _ hcl hlow hh.2
  intro t ht
  ext j
  fin_cases j
  · exact congrArg (fun v : AngularFiber => v 0) (hh0 ht)
  · exact congrArg (fun v : AngularFiber => v 0) (hl0 ht)
  · exact congrArg (fun v : AngularFiber => v 1) (hh0 ht)
  · exact congrArg (fun v : AngularFiber => v 1) (hl0 ht)

end KN.Physics
