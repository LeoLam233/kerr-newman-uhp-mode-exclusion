import KN.Energy.PhysicalInfinityEndpoint

noncomputable section
open Filter Set Asymptotics MeasureTheory
open scoped Topology
namespace KN.Energy

theorem physical_density_continuous (positive : Bool) (b : KN.Background)
    (ω : ℂ) (T L σ D : ℝ) (Y Yp : ℝ → ℂ)
    (hY : ContinuousOn Y (Iio (-b.h))) (hYp : ContinuousOn Yp (Iio (-b.h))) :
    ContinuousOn (density ω (systemP positive b) (systemW positive b) (angularK b T L σ)
      (fun x => radialR b x-D) (gaugedU b ω Y) (gaugedV b ω Y Yp)) (Iio (-b.h)) := by
  intro x hx
  have hxlt : x < -b.h := hx
  have hx0 : x ≠ 0 := by have := b.h_pos; linarith
  have hxe : x+b.eta ≠ 0 := by
    have hh : b.h=b.eta+2 := rfl
    linarith
  have hx2 : x*(x+b.eta)^2 ≠ 0 := mul_ne_zero hx0 (pow_ne_zero 2 hxe)
  have hx3 : x*(x+b.eta)^3 ≠ 0 := mul_ne_zero hx0 (pow_ne_zero 3 hxe)
  have hxh : x+b.h ≠ 0 := by linarith
  have ht : -b.h-x ≠ 0 := by linarith
  have hy := hY.continuousAt (Iio_mem_nhds hxlt)
  have hyp := hYp.continuousAt (Iio_mem_nhds hxlt)
  apply ContinuousAt.continuousWithinAt
  unfold density gaugedU gaugedV inverseGauge angularK radialR
  cases positive
  · simp only [systemP,systemW,Bool.false_eq_true,ite_false]
    unfold Pminus Wminus
    fun_prop (disch := assumption)
  · simp only [systemP,systemW,ite_true]
    unfold Pplus Wplus
    fun_prop (disch := assumption)

theorem physical_energy_integrable (positive : Bool) (b : KN.Background)
    (ω : ℂ) (hω : 0 < ω.im) (T L σ D : ℝ) (Y Yp : ℝ → ℂ)
    (hY : ContinuousOn Y (Iio (-b.h))) (hYp : ContinuousOn Yp (Iio (-b.h)))
    (hYb : ContinuousAt Y (-b.h)) (hYpb : ContinuousAt Yp (-b.h))
    (hYinf : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Y (-r)))
    (hYpinf : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Yp (-r))) :
    IntegrableOn
      (density ω (systemP positive b) (systemW positive b) (angularK b T L σ)
        (fun x => radialR b x-D) (gaugedU b ω Y) (gaugedV b ω Y Yp)) (Iio (-b.h)) := by
  exact integrable_energy_of_endpoint_bounds _ (-b.h) b.M ω.im b.delta
    b.mass_pos hω b.delta_pos
    (physical_density_continuous positive b ω T L σ D Y Yp hY hYp)
    (physical_finite_energy_order positive b ω T L σ D Y Yp hYb hYpb)
    (physical_infinity_energy_flux_bounds positive b ω hω T L σ D Y Yp hYinf hYpinf).1

end KN.Energy
