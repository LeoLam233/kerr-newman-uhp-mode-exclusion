import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

set_option linter.unusedSimpArgs false
/-! The genuine differential-ring identity underlying C002 (56).
It is valid in every commutative complex differential algebra, not just on
polynomials, and requires no equation, horizon coefficient, or spectral condition. -/
namespace KN.Kerr

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Derivation ℂ A A) (r : A)
variable (M a m ω Λ : ℂ)

noncomputable def delta : A := r ^ 2 - 2 * algebraMap ℂ A M * r + algebraMap ℂ A a ^ 2
noncomputable def deltaPrime : A := 2 * (r - algebraMap ℂ A M)
noncomputable def kStd : A := (r ^ 2 + algebraMap ℂ A a ^ 2) * algebraMap ℂ A ω -
  algebraMap ℂ A a * algebraMap ℂ A m
noncomputable def pCoeff (s : ℂ) : A :=
  (1 - algebraMap ℂ A s) * deltaPrime r M -
    2 * algebraMap ℂ A Complex.I * kStd r a m ω
noncomputable def cCoeff (s : ℂ) : A :=
  2 * algebraMap ℂ A Complex.I * (2 * algebraMap ℂ A s - 1) * algebraMap ℂ A ω * r -
  algebraMap ℂ A s - algebraMap ℂ A Λ - algebraMap ℂ A a ^ 2 * algebraMap ℂ A ω ^ 2 +
  2 * algebraMap ℂ A a * algebraMap ℂ A m * algebraMap ℂ A ω

noncomputable def radialOperator (s : ℂ) (f : A) : A :=
  delta r M a * D (D f) + pCoeff r M a m ω s * D f + cCoeff r a m ω Λ s * f

/-- C002 (56), spin 1, as an actual operator identity. -/
theorem intertwiner_spin_one (hr : D r = 1) (f : A) :
    D (D (radialOperator D r M a m ω Λ 1 f)) =
      radialOperator D r M a m ω Λ (-1) (D (D f)) := by
  have htwo : D (2 : A) = 0 := D.map_natCast 2
  simp [htwo, map_ofNat, radialOperator, delta, deltaPrime, pCoeff, cCoeff, kStd,
    Derivation.leibniz, hr, pow_two]
  ring

/-- C002 (56), spin 2, as an actual operator identity. -/
theorem intertwiner_spin_two (hr : D r = 1) (f : A) :
    D (D (D (D (radialOperator D r M a m ω Λ 2 f)))) =
      radialOperator D r M a m ω Λ (-2) (D (D (D (D f)))) := by
  have htwo : D (2 : A) = 0 := D.map_natCast 2
  simp [htwo, map_ofNat, radialOperator, delta, deltaPrime, pCoeff, cCoeff, kStd,
    Derivation.leibniz, hr, pow_two]
  ring

end DifferentialAlgebra
end KN.Kerr
