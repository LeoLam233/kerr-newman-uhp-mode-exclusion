import KN.Kerr.GaugeConjugation
import KN.Kerr.NegativeHorizon
import KN.Kerr.WhitingInterface

namespace KN.Kerr
open Set Filter
open scoped Topology ContDiff

/-- The actual radial equation (52) implies the actual conjugated equation (53),
using the manuscript's integral gauge and only C∞ regularity on the half-line. -/
theorem physical_to_conjugated
    (b : KN.Background) (m s : ℤ) (omega Λ : ℂ) (R f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r)
    (heq : PhysicalRadialEquation b m omega Λ s R) :
    ConjugatedEquation b m omega Λ s f := by
  have hfopen : ContDiffOn ℝ ∞ f (Ioi b.rPlus) := hf.mono Ioi_subset_Ici_self
  have hfd (x : ℝ) (hx : b.rPlus < x) : DifferentiableAt ℝ f x :=
    ((hfopen x hx).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)
  have hfd' (x : ℝ) (hx : b.rPlus < x) : DifferentiableAt ℝ (deriv f) x :=
    (((hfopen.deriv_of_isOpen isOpen_Ioi (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)) x hx).contDiffAt
      (Ioi_mem_nhds hx)).differentiableAt (by simp)
  have hfirst (x : ℝ) (hx : b.rPlus < x) :
      deriv R x = ingoingFactor b m omega s x *
        (deriv f x + psiFunction b m omega s x * f x) := by
    have hlocal : R =ᶠ[𝓝 x] fun y => ingoingFactor b m omega s y * f y := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hrep y hy
    rw [hlocal.deriv_eq, deriv_fun_mul (ingoingFactor_hasDerivAt b m omega s hx).differentiableAt
      (hfd x hx), (ingoingFactor_hasDerivAt b m omega s hx).deriv]
    unfold psiFunction
    push_cast
    ring
  intro r hr
  have hfirstlocal : deriv R =ᶠ[𝓝 r] fun x => ingoingFactor b m omega s x *
      (deriv f x + psiFunction b m omega s x * f x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact hfirst x hx
  have hsecond : deriv (deriv R) r =
      ingoingFactor b m omega s r *
        (deriv (deriv f) r + 2 * psiFunction b m omega s r * deriv f r +
          (logarithmicDerivativePrime (b.Delta r) (2 * ((r : ℂ) - b.M))
            (-b.frequencyK m omega r) s omega r + psiFunction b m omega s r ^ 2) * f r) := by
    rw [hfirstlocal.deriv_eq]
    rw [deriv_fun_mul (d := fun x => deriv f x + psiFunction b m omega s x * f x) (ingoingFactor_hasDerivAt b m omega s hr).differentiableAt
      ((hfd' r hr).add ((psiFunction_hasDerivAt b m omega s hr).differentiableAt.mul (hfd r hr)))]
    rw [deriv_fun_add (g := fun x => psiFunction b m omega s x * f x) (hfd' r hr) ((psiFunction_hasDerivAt b m omega s hr).differentiableAt.mul (hfd r hr))]
    rw [deriv_fun_mul (psiFunction_hasDerivAt b m omega s hr).differentiableAt (hfd r hr)]
    rw [(ingoingFactor_hasDerivAt b m omega s hr).deriv,
      (psiFunction_hasDerivAt b m omega s hr).deriv]
    unfold psiFunction
    push_cast
    ring
  have hΔ : (b.Delta r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (b.Delta_pos hr)
  have hc1 := conjugation_first (b.Delta r) (2 * ((r : ℂ) - b.M))
    (-b.frequencyK m omega r) s hΔ
  have hc0 := conjugation_zeroth (b.Delta r) (2 * ((r : ℂ) - b.M))
    (-b.frequencyK m omega r) s omega r b.a m Λ hΔ
  have hp := heq r hr
  rw [hsecond, hfirst r hr, hrep r hr] at hp
  have hproduct : ingoingFactor b m omega s r *
      ((b.Delta r : ℂ) * deriv (deriv f) r + radialP b m omega s r * deriv f r +
        radialC b m omega Λ s r * f r) = 0 := by
    unfold radialP radialC psiFunction at *
    push_cast at *
    linear_combination hp - (ingoingFactor b m omega s r * deriv f r) * hc1 -
      (ingoingFactor b m omega s r * f r) * hc0
  exact (mul_eq_zero.mp hproduct).resolve_left (ingoingFactor_nonzero b m omega s hr)

/-- Converse direction of the exact physical conjugation, used for the reversed mode. -/
theorem conjugated_to_physical
    (b : KN.Background) (m s : ℤ) (omega Λ : ℂ) (R f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega s r * f r)
    (heq : ConjugatedEquation b m omega Λ s f) :
    PhysicalRadialEquation b m omega Λ s R := by
  have hfopen : ContDiffOn ℝ ∞ f (Ioi b.rPlus) := hf.mono Ioi_subset_Ici_self
  have hfd (x : ℝ) (hx : b.rPlus < x) : DifferentiableAt ℝ f x :=
    ((hfopen x hx).contDiffAt (Ioi_mem_nhds hx)).differentiableAt (by simp)
  have hfd' (x : ℝ) (hx : b.rPlus < x) : DifferentiableAt ℝ (deriv f) x :=
    (((hfopen.deriv_of_isOpen isOpen_Ioi (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)) x hx).contDiffAt
      (Ioi_mem_nhds hx)).differentiableAt (by simp)
  have hfirst (x : ℝ) (hx : b.rPlus < x) :
      deriv R x = ingoingFactor b m omega s x *
        (deriv f x + psiFunction b m omega s x * f x) := by
    have hlocal : R =ᶠ[𝓝 x] fun y => ingoingFactor b m omega s y * f y := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact hrep y hy
    rw [hlocal.deriv_eq, deriv_fun_mul (ingoingFactor_hasDerivAt b m omega s hx).differentiableAt
      (hfd x hx), (ingoingFactor_hasDerivAt b m omega s hx).deriv]
    unfold psiFunction
    push_cast
    ring
  intro r hr
  have hfirstlocal : deriv R =ᶠ[𝓝 r] fun x => ingoingFactor b m omega s x *
      (deriv f x + psiFunction b m omega s x * f x) := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact hfirst x hx
  have hsecond : deriv (deriv R) r =
      ingoingFactor b m omega s r *
        (deriv (deriv f) r + 2 * psiFunction b m omega s r * deriv f r +
          (logarithmicDerivativePrime (b.Delta r) (2 * ((r : ℂ) - b.M))
            (-b.frequencyK m omega r) s omega r + psiFunction b m omega s r ^ 2) * f r) := by
    rw [hfirstlocal.deriv_eq]
    rw [deriv_fun_mul (d := fun x => deriv f x + psiFunction b m omega s x * f x) (ingoingFactor_hasDerivAt b m omega s hr).differentiableAt
      ((hfd' r hr).add ((psiFunction_hasDerivAt b m omega s hr).differentiableAt.mul (hfd r hr)))]
    rw [deriv_fun_add (g := fun x => psiFunction b m omega s x * f x) (hfd' r hr) ((psiFunction_hasDerivAt b m omega s hr).differentiableAt.mul (hfd r hr))]
    rw [deriv_fun_mul (psiFunction_hasDerivAt b m omega s hr).differentiableAt (hfd r hr)]
    rw [(ingoingFactor_hasDerivAt b m omega s hr).deriv,
      (psiFunction_hasDerivAt b m omega s hr).deriv]
    unfold psiFunction
    push_cast
    ring
  have hΔ : (b.Delta r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (b.Delta_pos hr)
  have hc1 := conjugation_first (b.Delta r) (2 * ((r : ℂ) - b.M))
    (-b.frequencyK m omega r) s hΔ
  have hc0 := conjugation_zeroth (b.Delta r) (2 * ((r : ℂ) - b.M))
    (-b.frequencyK m omega r) s omega r b.a m Λ hΔ
  have hp := heq r hr
  rw [hsecond, hfirst r hr, hrep r hr]
  unfold radialP radialC psiFunction at *
  push_cast at *
  linear_combination (ingoingFactor b m omega s r) * hp +
    (ingoingFactor b m omega s r * deriv f r) * hc1 +
    (ingoingFactor b m omega s r * f r) * hc0

end KN.Kerr
