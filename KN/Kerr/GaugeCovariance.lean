import KN.Kerr.Intertwiner

namespace KN.Kerr
section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Covariant derivative associated to the logarithmic derivative p of a gauge. -/
noncomputable def covariantDerivative (D : Derivation ℂ A A) (p v : A) : A :=
  D v - p * v

/-- The one-step gauge identity is a genuine differentiation identity. -/
theorem gauge_covariance_one (D : Derivation ℂ A A) (p qInv : A)
    (hq : D qInv = -p * qInv) (v : A) :
    D (qInv * v) = qInv * covariantDerivative D p v := by
  simp only [Derivation.leibniz, smul_eq_mul, hq, covariantDerivative]
  ring

/-- Repeated differentiation after gauge conjugation. No inverse differential
operator, spectral coefficient, or asymptotic expansion is assumed. -/
theorem gauge_covariance_iterate (D : Derivation ℂ A A) (p qInv : A)
    (hq : D qInv = -p * qInv) (v : A) (n : ℕ) :
    (D^[n]) (qInv * v) = qInv * ((covariantDerivative D p)^[n]) v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, gauge_covariance_one D p qInv hq,
      Function.iterate_succ_apply']

/-- The exterior outgoing spin-reversal operator has rational-coefficient
covariant-derivative form, so conormal preservation reduces to closure properties. -/
theorem outgoing_gauge_covariance (D : Derivation ℂ A A) (p q qInv weight v : A)
    (hq : D qInv = -p * qInv) (hInv : q * qInv = 1) (n : ℕ) :
    q * weight * (D^[n]) (qInv * (weight * v)) =
      weight * ((covariantDerivative D p)^[n]) (weight * v) := by
  rw [gauge_covariance_iterate D p qInv hq]
  calc
    q * weight * (qInv * ((covariantDerivative D p)^[n]) (weight * v)) =
        (q * qInv) * (weight * ((covariantDerivative D p)^[n]) (weight * v)) := by ring
    _ = _ := by rw [hInv, one_mul]

end DifferentialAlgebra
end KN.Kerr
