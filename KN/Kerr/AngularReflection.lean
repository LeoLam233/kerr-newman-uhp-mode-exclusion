import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace KN.Kerr

noncomputable def angularPotential (a s m ω : ℂ) (θ : ℝ) : ℂ :=
  (m + s * (Real.cos θ : ℂ)) ^ 2 / (Real.sin θ : ℂ) ^ 2 -
  a ^ 2 * ω ^ 2 * (Real.cos θ : ℂ) ^ 2 +
  2 * a * s * ω * (Real.cos θ : ℂ)

/-- Expanded divergence-form operator (50) in the open angular interval. -/
noncomputable def angularOperator (a s m ω : ℂ) (u : ℝ → ℂ) (θ : ℝ) : ℂ :=
  -deriv (deriv u) θ - (Real.cos θ : ℂ) / (Real.sin θ : ℂ) * deriv u θ +
    angularPotential a s m ω θ * u θ

noncomputable def angularReflect (u : ℝ → ℂ) : ℝ → ℂ := fun θ => u (Real.pi - θ)

/-- Reflection is involutive, so it preserves nonzero functions. -/
theorem angularReflect_involutive (u : ℝ → ℂ) : angularReflect (angularReflect u) = u := by
  funext θ
  simp [angularReflect]

theorem angularReflect_ne_zero {u : ℝ → ℂ} (hu : u ≠ 0) : angularReflect u ≠ 0 := by
  intro h
  have := congrArg angularReflect h
  apply hu
  simpa only [angularReflect_involutive, show angularReflect (0 : ℝ → ℂ) = 0 from rfl] using this

/-- C002 (50) potential intertwining; no conjugation of ω or m. -/
theorem angularPotential_reflection (a s m ω : ℂ) (θ : ℝ) :
    angularPotential a (-s) m ω θ = angularPotential a s m ω (Real.pi - θ) := by
  simp [angularPotential, Real.cos_pi_sub, Real.sin_pi_sub]

@[simp] theorem deriv_angularReflect (u : ℝ → ℂ) (θ : ℝ) :
    deriv (angularReflect u) θ = -deriv u (Real.pi - θ) :=
  deriv_comp_const_sub u Real.pi θ

/-- Exact differential reflection identity, independently of domain realization. -/
theorem angularOperator_reflection (a s m ω : ℂ) (u : ℝ → ℂ) (θ : ℝ) :
    angularOperator a (-s) m ω (angularReflect u) θ =
      angularOperator a s m ω u (Real.pi - θ) := by
  have hd : deriv (angularReflect u) = fun x => -deriv u (Real.pi - x) :=
    funext (deriv_angularReflect u)
  have hdd : deriv (deriv (angularReflect u)) θ = deriv (deriv u) (Real.pi - θ) := by
    rw [hd, deriv.fun_neg, deriv_comp_const_sub, neg_neg]
  simp only [angularOperator, hdd, deriv_angularReflect, angularPotential_reflection,
    Real.cos_pi_sub, Real.sin_pi_sub, Complex.ofReal_neg, angularReflect]
  ring

/-- The two canonical regular pole orders exchange under spin reversal. -/
theorem pole_orders_exchange (m s : ℤ) :
    (|m + -s|, |m - -s|) = (|m - s|, |m + s|) := by
  simp [sub_eq_add_neg]

end KN.Kerr
