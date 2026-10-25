import KN.Kerr.ExteriorDerivation
import KN.Kerr.NegativeHorizon
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

namespace KN.Kerr
open Set
open scoped ContDiff

/-- Ordinary radial derivatives preserve smoothness on the open exterior. -/
theorem exterior_iteratedDeriv_smooth {rp : ℝ} {f : ℝ → ℂ}
    (hf : ContDiffOn ℝ ∞ f (Ioi rp)) (n : ℕ) :
    ContDiffOn ℝ ∞ (iteratedDeriv n f) (Ioi rp) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen isOpen_Ioi (by simp)

/-- Equality in the smooth algebra, not just evaluation at one point. -/
theorem exteriorDerivation_pullback_eq (rp : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi rp)) :
    exteriorDerivation (exteriorPullback rp f hf) =
    exteriorPullback rp (deriv f) (hf.deriv_of_isOpen isOpen_Ioi (by simp)) := by
  apply Subtype.ext
  funext t
  exact exteriorDerivation_pullback rp f hf t

theorem exteriorDerivation_iterate_pullback (rp : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi rp)) (n : ℕ) :
    (exteriorDerivation^[n]) (exteriorPullback rp f hf) =
      exteriorPullback rp (iteratedDeriv n f) (exterior_iteratedDeriv_smooth hf n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, exteriorDerivation_pullback_eq]
    apply Subtype.ext
    funext t
    change deriv (iteratedDeriv n f) (exteriorChart rp t) = iteratedDeriv (n + 1) f (exteriorChart rp t)
    rw [iteratedDeriv_succ]

/-- Every coefficient and derivative in the chart operator is the physical
coefficient and derivative in (53), with Q=0 explicitly required. -/
theorem chart_radialOperator_value (b : KN.Background) (hQ : b.Q = 0)
    (m : ℤ) (omega Λ : ℂ) (s : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi b.rPlus)) (t : ℝ) :
    (radialOperator exteriorDerivation (exteriorCoordinate b.rPlus) b.M b.a m omega Λ s
      (exteriorPullback b.rPlus f hf)).val t =
    (b.Delta (exteriorChart b.rPlus t) : ℂ) * deriv (deriv f) (exteriorChart b.rPlus t) +
      radialP b m omega s (exteriorChart b.rPlus t) * deriv f (exteriorChart b.rPlus t) +
      radialC b m omega Λ s (exteriorChart b.rPlus t) * f (exteriorChart b.rPlus t) := by
  have hd1 := exteriorDerivation_pullback_eq b.rPlus f hf
  have hd2 := exteriorDerivation_pullback_eq b.rPlus (deriv f)
    (hf.deriv_of_isOpen isOpen_Ioi (by simp))
  unfold radialOperator
  rw [hd1, hd2]
  change ((exteriorChart b.rPlus t : ℂ)^2 - 2 * b.M * exteriorChart b.rPlus t + (b.a : ℂ)^2) *
    deriv (deriv f) (exteriorChart b.rPlus t) +
    ((1 - (s : ℂ)) * (2 * ((exteriorChart b.rPlus t : ℂ) - b.M)) -
      2 * Complex.I * (((exteriorChart b.rPlus t : ℂ)^2 + (b.a : ℂ)^2) * omega - b.a * m)) *
        deriv f (exteriorChart b.rPlus t) +
    (2 * Complex.I * (2 * (s : ℂ) - 1) * omega * exteriorChart b.rPlus t - s - Λ -
      (b.a : ℂ)^2 * omega^2 + 2 * b.a * m * omega) * f (exteriorChart b.rPlus t) = _
  simp only [Background.Delta, hQ, radialP, radialC, Background.frequencyK]
  push_cast
  ring

theorem conjugated_iff_chart_operator (b : KN.Background) (hQ : b.Q = 0)
    (m : ℤ) (omega Λ : ℂ) (s : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi b.rPlus)) :
    ConjugatedEquation b m omega Λ s f ↔
      radialOperator exteriorDerivation (exteriorCoordinate b.rPlus) b.M b.a m omega Λ s
        (exteriorPullback b.rPlus f hf) = 0 := by
  constructor
  · intro heq
    apply Subtype.ext
    funext t
    rw [chart_radialOperator_value b hQ m omega Λ s f hf t]
    exact heq _ (exteriorChart_mem b.rPlus t)
  · intro heq r hr
    have hval := congrArg (fun u : SmoothRadial => u.val (Real.log (r - b.rPlus))) heq
    rw [chart_radialOperator_value b hQ m omega Λ s f hf,
      exteriorChart_surjective b.rPlus r hr] at hval
    exact hval

/-- C002 (56) for spin 1, on arbitrary C∞ exterior solutions. -/
theorem spin_one_solution_reversal (b : KN.Background) (hQ : b.Q = 0)
    (m : ℤ) (omega Λ : ℂ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi b.rPlus))
    (heq : ConjugatedEquation b m omega Λ 1 f) :
    ConjugatedEquation b m omega Λ (-1) (iteratedDeriv 2 f) := by
  apply (conjugated_iff_chart_operator b hQ m omega Λ (-1) (iteratedDeriv 2 f)
    (exterior_iteratedDeriv_smooth hf 2)).mpr
  have hz := (conjugated_iff_chart_operator b hQ m omega Λ 1 f hf).mp heq
  have hi := exterior_intertwiner_one b.rPlus b.M b.a m omega Λ (exteriorPullback b.rPlus f hf)
  have hiter := exteriorDerivation_iterate_pullback b.rPlus f hf 2
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at hiter
  norm_num only [Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg] at hz ⊢
  rw [hz, map_zero, map_zero, hiter] at hi
  exact hi.symm

/-- C002 (56) for spin 2, with no excluded exceptional frequencies. -/
theorem spin_two_solution_reversal (b : KN.Background) (hQ : b.Q = 0)
    (m : ℤ) (omega Λ : ℂ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi b.rPlus))
    (heq : ConjugatedEquation b m omega Λ 2 f) :
    ConjugatedEquation b m omega Λ (-2) (iteratedDeriv 4 f) := by
  apply (conjugated_iff_chart_operator b hQ m omega Λ (-2) (iteratedDeriv 4 f)
    (exterior_iteratedDeriv_smooth hf 4)).mpr
  have hz := (conjugated_iff_chart_operator b hQ m omega Λ 2 f hf).mp heq
  have hi := exterior_intertwiner_two b.rPlus b.M b.a m omega Λ (exteriorPullback b.rPlus f hf)
  have hiter := exteriorDerivation_iterate_pullback b.rPlus f hf 4
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at hiter
  norm_num only [Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_neg] at hz ⊢
  rw [hz, map_zero, map_zero, map_zero, map_zero, hiter] at hi
  exact hi.symm

end KN.Kerr
