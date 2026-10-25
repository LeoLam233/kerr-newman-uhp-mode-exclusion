import KN.Boundary.Radial
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.TangentCone.Real

namespace KN.Kerr
open Set
open scoped Topology ContDiff

/-- Every finite radial derivative of a smooth closed-half-line coefficient
has a smooth closed-half-line extension. This includes resonant Frobenius data. -/
theorem horizon_coefficient_derivatives {f : ℝ → ℂ} {rp : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici rp)) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDerivWithin n f (Ici rp)) (Ici rp) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDerivWithin_succ]
    exact ih.derivWithin (uniqueDiffOn_Ici rp) (by simp)

/-- The closed-half-line derivatives are the ordinary radial derivatives
at every exterior point. -/
theorem horizon_coefficient_derivatives_exterior {f : ℝ → ℂ} {rp r : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici rp)) (n : ℕ) (hr : rp < r) :
    iteratedDerivWithin n f (Ici rp) r = iteratedDeriv n f r := by
  apply iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici rp)
  · exact ((hf r (le_of_lt hr)).contDiffAt (Ici_mem_nhds hr)).of_le (by simp)
  · exact le_of_lt hr

/-- Formula (55), expressed using a chosen smooth horizon coefficient.
The within derivative only defines its boundary value; it agrees with the ordinary
2s-th derivative everywhere in the physical exterior. -/
noncomputable def reversedRadial (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) (n : ℕ) (f : ℝ → ℂ) (r : ℝ) : ℂ :=
  KN.Boundary.gauge b m omega r * (Real.rpow (b.Delta r) s : ℂ) *
    iteratedDerivWithin n f (Ici b.rPlus) r

/-- The future-horizon part of Lemma 8.2, for every frequency and every order.
No nonzero leading coefficient or nonresonance hypothesis occurs. -/
theorem reversedRadial_horizon_regular (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) (n : ℕ) (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus)) :
    KN.Boundary.HorizonRegular b m omega s (reversedRadial b m omega s n f) := by
  refine ⟨iteratedDerivWithin n f (Ici b.rPlus), horizon_coefficient_derivatives hf n, ?_⟩
  intro r _
  rfl

end KN.Kerr
