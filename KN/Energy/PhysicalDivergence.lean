import KN.Energy.InverseGaugeFlux
import KN.Energy.PhysicalGaugePotential

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set
open scoped Topology
namespace KN.Energy
open KN.ChargedRadial

theorem transformed_ODE_to_physical_divergence (positive : Bool) (b : KN.Background)
    (m : ℤ) (ω lam : ℂ) (Y Yp : ℝ → ℂ) (x : ℝ) (Ypp : ℂ)
    (hx : x < -b.h) (hY : HasDerivAt Y (Yp x) x) (hYp : HasDerivAt Yp Ypp x)
    (heq :
      transformA (backgroundPolynomialData b m (spinSign positive) ω lam) x*Ypp+
      (transformB (backgroundPolynomialData b m (spinSign positive) ω lam) x+
        Complex.I*ω*transformC (backgroundPolynomialData b m (spinSign positive) ω lam) x)*Yp x+
      (transformD0 (backgroundPolynomialData b m (spinSign positive) ω lam) x+
        ω*transformD1 (backgroundPolynomialData b m (spinSign positive) ω lam) x+
        ω^2*transformD2 (backgroundPolynomialData b m (spinSign positive) ω lam) x+
        Complex.I*ω*transformE (backgroundPolynomialData b m (spinSign positive) ω lam) x)*Y x=0) :
    HasDerivAt (fun y => (systemP positive b y:ℂ)*gaugedV b ω Y Yp y)
      (-(systemW positive b x:ℂ)*angularBracket b m ω lam (spinSign positive) x*
        gaugedU b ω Y x) x := by
  let p := backgroundPolynomialData b m (spinSign positive) ω lam
  let pp := systemMu positive b x*(x^2-b.eta*b.h-3*spinSign positive*x*(x+b.h))
  let qp := systemMu positive b x*(b.M*(x+b.eta)*(x-b.eta-3*spinSign positive*x))
  let d := (systemMu positive b x:ℂ)*(transformD0 p x+ω*transformD1 p x+ω^2*transformD2 p x)
  have hP : HasDerivAt (systemP positive b) pp x := systemP_hasDerivAt positive b hx
  have hQ : HasDerivAt (systemQ positive b) qp x := systemQ_hasDerivAt positive b hx
  have hs := phaseRate_hasDerivAt b hx
  have hqprod : qp=pp*phaseRate b x+systemP positive b x*(2*b.M/(-b.h-x)^2) := by
    have he : systemQ positive b =ᶠ[𝓝 x] (fun y => systemP positive b y*phaseRate b y) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact (system_weight_identities positive b hy).2.2.2
    exact hQ.unique ((hP.mul hs).congr_of_eventuallyEq he)
  have hA : (systemMu positive b x:ℂ)*transformA p x=(systemP positive b x:ℂ) := by
    have hh := (system_weight_identities positive b hx).1
    have hc := congrArg Complex.ofReal hh
    push_cast at hc
    simpa [p,backgroundPolynomialData,transformA,KN.Background.h,add_assoc] using hc
  have hB : (systemMu positive b x:ℂ)*transformB p x=(pp:ℂ) := by
    dsimp [pp,p,backgroundPolynomialData,transformB,KN.Background.h]
    push_cast
    ring
  have hC : (systemMu positive b x:ℂ)*transformC p x=2*(systemQ positive b x:ℂ) := by
    have hh := (system_weight_identities positive b hx).2.2.1
    have hc := congrArg Complex.ofReal hh
    push_cast at hc
    simpa [p,backgroundPolynomialData,transformC] using hc
  have hE : (systemMu positive b x:ℂ)*transformE p x=(qp:ℂ) := by
    dsimp [qp,p,backgroundPolynomialData,transformE]
    push_cast
    ring
  have hweighted : (systemP positive b x:ℂ)*Ypp+
      ((pp:ℂ)+2*Complex.I*ω*systemQ positive b x)*Yp x+
      (d+Complex.I*ω*qp)*Y x=0 := by
    have hh := congrArg (fun z : ℂ => (systemMu positive b x:ℂ)*z) heq
    change (systemMu positive b x:ℂ)*(transformA p x*Ypp+
      (transformB p x+Complex.I*ω*transformC p x)*Yp x+
      (transformD0 p x+ω*transformD1 p x+ω^2*transformD2 p x+
        Complex.I*ω*transformE p x)*Y x)=_ at hh
    dsimp [d]
    linear_combination hh - Ypp*hA - Yp x*hB -
      Complex.I*ω*Yp x*hC - Complex.I*ω*Y x*hE
  have hg : HasDerivAt (inverseGauge ω b.M (-b.h))
      (Complex.I*ω*(phaseRate b x:ℂ)*inverseGauge ω b.M (-b.h) x) x := by
    simpa only [phaseRate] using inverseGauge_hasDerivAt ω b.M (-b.h) x hx
  have hf := inverse_gauge_flux ω (inverseGauge ω b.M (-b.h)) Y Yp
    (systemP positive b) (phaseRate b) x pp (2*b.M/(-b.h-x)^2) (systemQ positive b x) qp
    Ypp d hg hY hYp hP hs (system_weight_identities positive b hx).2.2.2 hqprod hweighted
  have hpot := physical_weighted_potential positive b m ω lam hx
  change d+ω^2*(systemQ positive b x:ℂ)*(phaseRate b x:ℂ)=_ at hpot
  rw [hpot] at hf
  convert hf using 1
  · rfl
  · dsimp [gaugedU]
    ring

theorem angularBracket_energy_form (b : KN.Background) (hQ : b.Q ≠ 0)
    (m : ℤ) (ω lam : ℂ) (T L v C D σ x : ℝ)
    (hlam : lam=(L:ℂ)+ω*v)
    (hlam2 : lam^2=(b.beta:ℂ)^2+T+ω*C+ω^2*D) :
    angularBracket b m ω lam σ x =
      -(angularK b T L σ x:ℂ)+
        ω*((2*(b.a*(m:ℝ))*x-C-b.c/x*v:ℝ):ℂ)+ω^2*((radialR b x-D:ℝ):ℂ) := by
  have hh := angular_bracket_identity ω lam b.beta T L v C D b.c σ b.h x
    (b.a*(m:ℝ)) (radialR b x) hlam hlam2 (b.beta_mul_c hQ)
  dsimp [angularBracket,angularK]
  push_cast at *
  convert hh using 1
  ring

end KN.Energy
