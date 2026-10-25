import KN.Energy.PhysicalIntegrability

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Filter Set Asymptotics
namespace KN.Energy

/-- The physical energy exclusion with every weight sign, integrability and
both endpoint flux limits derived rather than supplied as separate premises. -/
theorem physical_gauged_vanishes (positive : Bool) (b : KN.Background)
    (ω : ℂ) (hω : 0 < ω.im) (T L σ qAvg : ℝ) (hq : qAvg ≤ 1)
    (l : ℝ → ℝ) (Y Yp : ℝ → ℂ)
    (hY : ∀ x < -b.h, HasDerivAt Y (Yp x) x)
    (hYp : ContinuousOn Yp (Iio (-b.h)))
    (hYb : ContinuousAt Y (-b.h)) (hYpb : ContinuousAt Yp (-b.h))
    (hYinf : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Y (-r)))
    (hYpinf : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Yp (-r)))
    (hk : ∀ x < -b.h, 0 ≤ angularK b T L σ x)
    (hV : ∀ x < -b.h,
      HasDerivAt (fun y => (systemP positive b y:ℂ)*gaugedV b ω Y Yp y)
        ((systemW positive b x:ℂ)*
          ((angularK b T L σ x:ℂ)-ω*(l x:ℂ)-ω^2*((radialR b x-b.a^2*(b.c^2+qAvg):ℝ):ℂ))*
            gaugedU b ω Y x) x) :
    ∀ x < -b.h, Y x=0 := by
  have hYc : ContinuousOn Y (Iio (-b.h)) :=
    fun x hx => (hY x hx).continuousAt.continuousWithinAt
  have hP : ∀ x < -b.h, 0 ≤ systemP positive b x := by
    intro x hx
    have hh := physical_weights_positive b x hx
    cases positive
    · exact hh.2.2.1.le
    · exact hh.1.le
  have hW : ∀ x < -b.h, 0 < systemW positive b x := by
    intro x hx
    have hh := physical_weights_positive b x hx
    cases positive
    · exact hh.2.2.2
    · exact hh.2.1
  have hzero := divergence_ODE_vanishes ω hω (systemP positive b) (systemW positive b)
    (angularK b T L σ) l (fun x => radialR b x-b.a^2*(b.c^2+qAvg))
    (gaugedU b ω Y) (gaugedV b ω Y Yp) (-b.h)
    (fun x hx => gauged_hasDerivAt ω b.M (-b.h) x Y (Yp x) hx (hY x hx))
    hV hP hW hk (fun x hx => physical_B_positive b x qAvg hx hq)
    (physical_energy_integrable positive b ω hω T L σ (b.a^2*(b.c^2+qAvg))
      Y Yp hYc hYp hYb hYpb hYinf hYpinf)
    (physical_finite_flux_zero positive b ω hω Y Yp hYb hYpb)
    (physical_infinity_flux_zero positive b ω hω Y Yp hYinf hYpinf)
  intro x hx
  have hz := hzero x hx
  change inverseGauge ω b.M (-b.h) x*Y x=0 at hz
  exact (mul_eq_zero.mp hz).resolve_left (Complex.exp_ne_zero _)

end KN.Energy
