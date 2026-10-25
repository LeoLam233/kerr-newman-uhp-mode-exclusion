import KN.Kerr.Conjugation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace KN.Kerr

/-- Second product derivative with precisely exposed differentiability assumptions. -/
theorem deriv_two_product (f q : ℝ → ℂ) (hf : Differentiable ℝ f)
    (hq : Differentiable ℝ q) (x : ℝ)
    (hf' : DifferentiableAt ℝ (deriv f) x) (hq' : DifferentiableAt ℝ (deriv q) x) :
    deriv (deriv (fun t => q t * f t)) x =
    q x * deriv (deriv f) x + 2 * deriv q x * deriv f x +
      deriv (deriv q) x * f x := by
  have hfirst : deriv (fun t => q t * f t) =
      fun t => deriv q t * f t + q t * deriv f t := by
    funext t
    exact deriv_fun_mul (hq t) (hf t)
  rw [hfirst, deriv_fun_add (f := fun t => deriv q t * f t) (g := fun t => q t * deriv f t) (hq'.mul (hf x)) ((hq x).mul hf'),
    deriv_fun_mul hq' (hf x), deriv_fun_mul (hq x) hf']
  ring

/-- Conjugation of an actual differential expression, not a jet-only identity.
The specialized Kerr gauge supplies the two displayed logarithmic derivative laws. -/
theorem conjugation_actual_functions
    (f q : ℝ → ℂ) (hf : Differentiable ℝ f) (hq : Differentiable ℝ q)
    (r : ℝ) (hf' : DifferentiableAt ℝ (deriv f) r)
    (hq' : DifferentiableAt ℝ (deriv q) r)
    (Δ Δ' K s ω a m Λ : ℂ) (hΔ : Δ ≠ 0)
    (hfirst : deriv q r = logarithmicDerivative Δ Δ' K s * q r)
    (hsecond : deriv (deriv q) r =
      (logarithmicDerivativePrime Δ Δ' K s ω r +
        logarithmicDerivative Δ Δ' K s ^ 2) * q r) :
    Δ * deriv (deriv (fun t => q t * f t)) r +
    (s + 1) * Δ' * deriv (fun t => q t * f t) r +
    ((K ^ 2 - Complex.I * s * Δ' * K) / Δ +
      4 * Complex.I * s * ω * r + s - Λ - a ^ 2 * ω ^ 2 + 2 * a * m * ω) *
      (q r * f r) =
    q r * (Δ * deriv (deriv f) r + ((1 - s) * Δ' - 2 * Complex.I * K) * deriv f r +
      (2 * Complex.I * (2 * s - 1) * ω * r - s - Λ - a ^ 2 * ω ^ 2 +
        2 * a * m * ω) * f r) := by
  rw [deriv_two_product f q hf hq r hf' hq', deriv_fun_mul (hq r) (hf r), hfirst, hsecond]
  have hc1 := conjugation_first Δ Δ' K s hΔ
  have hc0 := conjugation_zeroth Δ Δ' K s ω r a m Λ hΔ
  linear_combination (q r * deriv f r) * hc1 + (q r * f r) * hc0

end KN.Kerr
