import KN.Kerr.ExteriorIntertwiner
import KN.Kerr.PhysicalConjugation
import KN.Kerr.HorizonPreservation

namespace KN.Kerr
open Set Filter
open scoped Topology ContDiff

/-- The equation depends only on the actual exterior restriction of the coefficient. -/
theorem ConjugatedEquation.congr {b : KN.Background} {m : ℤ} {omega Λ : ℂ}
    {s : ℝ} {f g : ℝ → ℂ} (hf : ConjugatedEquation b m omega Λ s f)
    (hfg : EqOn f g (Ioi b.rPlus)) : ConjugatedEquation b m omega Λ s g := by
  intro r hr
  have hlocal : f =ᶠ[𝓝 r] g := by
    filter_upwards [Ioi_mem_nhds (show b.rPlus < r from hr)] with x hx
    exact hfg hx
  rw [← hlocal.deriv.deriv_eq, ← hlocal.deriv_eq, ← hfg hr]
  exact hf r hr

/-- Core of C002 Lemma 8.2: the exact reflected angular eigenfunction,
physical negative-spin radial equation, and horizon class are all proved.
Outgoing preservation and image injectivity are separate remaining analytic steps. -/
theorem spin_reversal_core
    (b : KN.Background) (hQ : b.Q = 0) (m s : ℤ) (omega Λ : ℂ)
    (hs : s = 1 ∨ s = 2) (u R f : ℝ → ℂ)
    (hu : RegularAngularEigenfunction b m s omega Λ u)
    (hphysical : PhysicalRadialEquation b m omega Λ s R)
    (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r) :
    RegularAngularEigenfunction b m (-s) omega Λ (angularReflect u) ∧
    PhysicalRadialEquation b m omega Λ (-s)
      (reversedRadial b m omega s (2 * s.natAbs) f) ∧
    KN.Boundary.HorizonRegular b m omega s
      (reversedRadial b m omega s (2 * s.natAbs) f) := by
  have hconj := physical_to_conjugated b m s omega Λ R f hf hrep hphysical
  have hrev : ConjugatedEquation b m omega Λ (-(s : ℝ))
      (iteratedDeriv (2 * s.natAbs) f) := by
    rcases hs with rfl | rfl
    · norm_num only [Int.cast_one] at hconj
      simpa using spin_one_solution_reversal b hQ m omega Λ f (hf.mono Ioi_subset_Ici_self) hconj
    · norm_num only [Int.cast_ofNat] at hconj
      simpa using spin_two_solution_reversal b hQ m omega Λ f (hf.mono Ioi_subset_Ici_self) hconj
  have hrevWithin : ConjugatedEquation b m omega Λ (-(s : ℝ))
      (iteratedDerivWithin (2 * s.natAbs) f (Ici b.rPlus)) := by
    apply hrev.congr
    intro r hr
    exact (horizon_coefficient_derivatives_exterior hf (2 * s.natAbs) hr).symm
  refine ⟨hu.reflect, ?_, reversedRadial_horizon_regular b m omega s (2 * s.natAbs) f hf⟩
  apply conjugated_to_physical b m (-s) omega Λ
    (reversedRadial b m omega s (2 * s.natAbs) f)
    (iteratedDerivWithin (2 * s.natAbs) f (Ici b.rPlus))
    (horizon_coefficient_derivatives hf (2 * s.natAbs))
  · intro r _
    simp [reversedRadial, ingoingFactor]
  · simpa only [Int.cast_neg] using hrevWithin

end KN.Kerr
