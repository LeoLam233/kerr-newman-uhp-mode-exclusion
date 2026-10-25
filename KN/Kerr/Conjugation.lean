import KN.Kerr.Intertwiner

namespace KN.Kerr

/-- Logarithmic derivative of the ingoing conjugating factor H Δ^(-s). -/
noncomputable def logarithmicDerivative (Δ Δ' K s : ℂ) : ℂ := -(Complex.I * K + s * Δ') / Δ

/-- Quotient-rule derivative, using Δ'' = 2 and K' = 2 ω r. -/
noncomputable def logarithmicDerivativePrime (Δ Δ' K s ω r : ℂ) : ℂ :=
  -(Complex.I * (2 * ω * r) + 2 * s) / Δ +
    (Complex.I * K + s * Δ') * Δ' / Δ ^ 2

/-- The first derivative coefficient in C002 (53). -/
theorem conjugation_first (Δ Δ' K s : ℂ) (hΔ : Δ ≠ 0) :
    2 * Δ * logarithmicDerivative Δ Δ' K s + (s + 1) * Δ' =
      (1 - s) * Δ' - 2 * Complex.I * K := by
  unfold logarithmicDerivative
  field_simp
  ring

/-- Complete cancellation of the apparent 1/Δ terms in C002 (53).
The Δ' = 2(r-M) identity is already incorporated into the original potential. -/
theorem conjugation_zeroth (Δ Δ' K s ω r a m Λ : ℂ) (hΔ : Δ ≠ 0) :
    Δ * (logarithmicDerivativePrime Δ Δ' K s ω r +
      logarithmicDerivative Δ Δ' K s ^ 2) +
    (s + 1) * Δ' * logarithmicDerivative Δ Δ' K s +
    (K ^ 2 - Complex.I * s * Δ' * K) / Δ +
    (4 * Complex.I * s * ω * r + s - Λ - a ^ 2 * ω ^ 2 + 2 * a * m * ω) =
    2 * Complex.I * (2 * s - 1) * ω * r - s - Λ - a ^ 2 * ω ^ 2 +
      2 * a * m * ω := by
  unfold logarithmicDerivativePrime logarithmicDerivative
  field_simp
  linear_combination (K ^ 2) * Complex.I_sq

/-- Negative-spin roots have strictly negative real part throughout the UHP. -/
theorem negative_spin_indicial_real (s γ κ : ℝ) (hs : s < 0) (hγ : 0 < γ)
    (hκ : 0 < κ) : s - γ / κ < 0 := by
  have h := div_pos hγ hκ
  linarith

/-- No resonance is removed from the UHP in the differential intertwiner:
its leading outgoing multiplier is nonzero at every UHP frequency. -/
theorem outgoing_multiplier_nonzero (ω : ℂ) (hω : 0 < ω.im) (n : ℕ) :
    (2 * Complex.I * ω) ^ n ≠ 0 := by
  apply pow_ne_zero
  apply mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  intro h
  simp [h] at hω

end KN.Kerr
