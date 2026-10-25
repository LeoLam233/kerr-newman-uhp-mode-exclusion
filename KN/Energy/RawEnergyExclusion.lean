import KN.Energy.PhysicalDivergence
import KN.Energy.PhysicalVanishing

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.Energy
open KN.ChargedRadial

/-- Exact scalar equation (38), with actual derivatives rather than an abstract jet. -/
def TransformedEquation (b : KN.Background) (p : RadialPolynomialData) (Y Yp : ℝ → ℂ) : Prop :=
  ∀ x < -b.h, transformA p x*deriv Yp x+
    (transformB p x+Complex.I*p.omega*transformC p x)*Yp x+
    (transformD0 p x+p.omega*transformD1 p x+p.omega^2*transformD2 p x+
      Complex.I*p.omega*transformE p x)*Y x=0

/-- Actual transformed-equation exclusion: the gauge cancellation, energy
integrability, and endpoint fluxes are all theorems applied internally. -/
theorem raw_transformed_field_zero (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0)
    (m : ℤ) (ω lam : ℂ) (hω : 0 < ω.im) (T L v C qAvg : ℝ) (hq : qAvg ≤ 1)
    (hlam : lam=(L:ℂ)+ω*v)
    (hlam2 : lam^2=(b.beta:ℂ)^2+T+ω*C+ω^2*((b.a^2*(b.c^2+qAvg):ℝ):ℂ))
    (Y Yp : ℝ → ℂ)
    (hY : ∀ x < -b.h, HasDerivAt Y (Yp x) x)
    (hYp : DifferentiableOn ℝ Yp (Iio (-b.h)))
    (hYb : ContinuousAt Y (-b.h)) (hYpb : ContinuousAt Yp (-b.h))
    (hYinf : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Y (-r)))
    (hYpinf : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Yp (-r)))
    (hk : ∀ x < -b.h, 0 ≤ angularK b T L (spinSign positive) x)
    (heq : TransformedEquation b (backgroundPolynomialData b m (spinSign positive) ω lam) Y Yp) :
    ∀ x < -b.h, Y x=0 := by
  apply physical_gauged_vanishes positive b ω hω T L (spinSign positive) qAvg hq
    (fun x => 2*(b.a*(m:ℝ))*x-C-b.c/x*v) Y Yp hY hYp.continuousOn
    hYb hYpb hYinf hYpinf hk
  intro x hx
  have hyy := (hYp.differentiableAt (Iio_mem_nhds hx)).hasDerivAt
  have hh := transformed_ODE_to_physical_divergence positive b m ω lam Y Yp x (deriv Yp x)
    hx (hY x hx) hyy (heq x hx)
  rw [angularBracket_energy_form b hQ m ω lam T L v C (b.a^2*(b.c^2+qAvg))
    (spinSign positive) x hlam hlam2] at hh
  convert hh using 1
  ring

end KN.Energy
