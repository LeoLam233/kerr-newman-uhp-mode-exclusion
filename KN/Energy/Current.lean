import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

open ComplexConjugate
namespace KN.Energy

/-- The local energy current; its derivative is nonpositive in the UHP. -/
noncomputable def current (ω : ℂ) (P : ℝ → ℝ) (U V : ℝ → ℂ) (x : ℝ) : ℝ :=
  (conj ω * ((P x : ℂ) * V x * conj (U x))).im

theorem current_algebra (ω u v : ℂ) (P W k l B : ℝ) :
    (conj ω * (((W : ℂ) * (k - ω*l - ω^2*B) * u) * conj u +
      (P : ℂ)*v*conj v)).im =
    -ω.im * (P*Complex.normSq v + W*k*Complex.normSq u +
      Complex.normSq ω*W*B*Complex.normSq u) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]
  ring

/-- Actual derivative of the current for a solution of (43), not an assumed
integrated energy identity. V denotes U', and the second derivative hypothesis
is the divergence-form ODE itself. -/
theorem current_hasDerivAt (ω : ℂ) (P W k l B : ℝ → ℝ) (U V : ℝ → ℂ) (x : ℝ)
    (hU : HasDerivAt U (V x) x)
    (hV : HasDerivAt (fun y => (P y : ℂ)*V y)
      ((W x : ℂ)*(k x-ω*l x-ω^2*B x)*U x) x) :
    HasDerivAt (current ω P U V)
      (-ω.im * (P x*Complex.normSq (V x) + W x*k x*Complex.normSq (U x) +
        Complex.normSq ω*W x*B x*Complex.normSq (U x))) x := by
  have hc : HasDerivAt (fun y => conj (U y)) (conj (V x)) x :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hU
  have hp := (hV.mul hc).const_mul (conj ω)
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hp
  convert him using 1
  · rfl
  · exact (current_algebra ω (U x) (V x) (P x) (W x) (k x) (l x) (B x)).symm

end KN.Energy
