import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

open Filter Set
open scoped Topology
namespace KN.Energy
noncomputable def gauge (ω : ℂ) (S : ℝ → ℝ) (x : ℝ) : ℂ :=
  Complex.exp (-Complex.I*ω*(S x : ℂ))
noncomputable def gaugeFirst (ω : ℂ) (S s : ℝ → ℝ) (U V : ℝ → ℂ) (x : ℝ) : ℂ :=
  gauge ω S x * (V x-Complex.I*ω*(s x : ℂ)*U x)
noncomputable def gaugeSecond (ω : ℂ) (S s : ℝ → ℝ)
    (U V : ℝ → ℂ) (sp : ℝ) (A : ℂ) (x : ℝ) : ℂ :=
  gauge ω S x*(A-2*Complex.I*ω*(s x : ℂ)*V x-
    Complex.I*ω*(sp:ℂ)*U x-ω^2*(s x : ℂ)^2*U x)

theorem gauge_ne_zero (ω : ℂ) (S : ℝ → ℝ) (x : ℝ) : gauge ω S x ≠ 0 :=
  Complex.exp_ne_zero _

theorem gauge_hasDerivAt (ω : ℂ) (S : ℝ → ℝ) (x s : ℝ)
    (hS : HasDerivAt S s x) :
    HasDerivAt (gauge ω S) (-Complex.I*ω*(s:ℂ)*gauge ω S x) x := by
  have h := (Complex.hasDerivAt_exp _).comp x (hS.ofReal_comp.const_mul (-Complex.I*ω))
  convert h using 1
  · rfl
  · dsimp [gauge]; ring

theorem gauge_product_hasDerivAt (ω : ℂ) (S s : ℝ → ℝ) (U V : ℝ → ℂ) (x : ℝ)
    (hS : HasDerivAt S (s x) x) (hU : HasDerivAt U (V x) x) :
    HasDerivAt (fun y => gauge ω S y*U y) (gaugeFirst ω S s U V x) x := by
  convert (gauge_hasDerivAt ω S x (s x) hS).mul hU using 1
  dsimp [gaugeFirst]; ring

theorem gauge_product_second_hasDerivAt (ω : ℂ) (S s : ℝ → ℝ) (U V : ℝ → ℂ)
    (x sp : ℝ) (A : ℂ) (hS : HasDerivAt S (s x) x) (hs : HasDerivAt s sp x)
    (hU : HasDerivAt U (V x) x) (hV : HasDerivAt V A x) :
    HasDerivAt (gaugeFirst ω S s U V) (gaugeSecond ω S s U V sp A x) x := by
  have hi := ((hs.ofReal_comp.const_mul (Complex.I*ω)).mul hU)
  convert (gauge_hasDerivAt ω S x (s x) hS).mul (hV.sub hi) using 1
  · rfl
  · dsimp [gaugeFirst, gaugeSecond]
    ring_nf
    simp [Complex.I_sq]
    ring

/-- Algebraic gauge conjugation after multiplication by μ. Every frequency
is genuinely complex. q=P s and q'=P' s+P s' are explicit derivative relations. -/
theorem gauge_residual_identity (ω g U V A : ℂ) (P Pp q qp s sp : ℝ) (d : ℂ)
    (hq : q=P*s) (hqp : qp=Pp*s+P*sp) :
    (P:ℂ)*(g*(A-2*Complex.I*ω*s*V-Complex.I*ω*sp*U-ω^2*(s:ℂ)^2*U))+
      ((Pp:ℂ)+2*Complex.I*ω*q)*(g*(V-Complex.I*ω*s*U))+
      (d+Complex.I*ω*qp)*(g*U) =
    g*((P:ℂ)*A+(Pp:ℂ)*V+(d+ω^2*q*s)*U) := by
  rw [hq, hqp]
  push_cast
  ring_nf
  simp [Complex.I_sq]
  ring

/-- Actual pointwise implication from the ungauged ODE to the divergence
ODE, with derivatives proved from the exponential gauge. -/
theorem gauge_ODE_to_divergence (ω : ℂ) (S s P : ℝ → ℝ) (U V : ℝ → ℂ)
    (b x sp Pp q qp : ℝ) (A d : ℂ) (hx : x < b)
    (hS : ∀ y < b, HasDerivAt S (s y) y) (hs : HasDerivAt s sp x)
    (hU : ∀ y < b, HasDerivAt U (V y) y) (hV : HasDerivAt V A x)
    (hP : HasDerivAt P Pp x) (hq : q=P x*s x) (hqp : qp=Pp*s x+P x*sp)
    (heq : (P x:ℂ)*deriv (deriv (fun y => gauge ω S y*U y)) x+
      ((Pp:ℂ)+2*Complex.I*ω*q)*deriv (fun y => gauge ω S y*U y) x+
      (d+Complex.I*ω*qp)*(gauge ω S x*U x) = 0) :
    HasDerivAt (fun y => (P y:ℂ)*V y) (-(d+ω^2*q*s x)*U x) x := by
  have hfirst : deriv (fun y => gauge ω S y*U y) =ᶠ[nhds x] gaugeFirst ω S s U V := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact (gauge_product_hasDerivAt ω S s U V y (hS y hy) (hU y hy)).deriv
  have hsecond : deriv (deriv (fun y => gauge ω S y*U y)) x =
      gaugeSecond ω S s U V sp A x := hfirst.deriv_eq.trans
    (gauge_product_second_hasDerivAt ω S s U V x sp A (hS x hx) hs (hU x hx) hV).deriv
  rw [hsecond, (gauge_product_hasDerivAt ω S s U V x (hS x hx) (hU x hx)).deriv] at heq
  have hres := gauge_residual_identity ω (gauge ω S x) (U x) (V x) A
    (P x) Pp q qp (s x) sp d hq hqp
  change (P x:ℂ)*gaugeSecond ω S s U V sp A x+
      ((Pp:ℂ)+2*Complex.I*ω*q)*gaugeFirst ω S s U V x+
      (d+Complex.I*ω*qp)*(gauge ω S x*U x) = _ at hres
  rw [heq] at hres
  have hz := (mul_eq_zero.mp hres.symm).resolve_left (gauge_ne_zero ω S x)
  convert hP.ofReal_comp.mul hV using 1
  linear_combination -hz

end KN.Energy
