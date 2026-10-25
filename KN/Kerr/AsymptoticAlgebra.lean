import KN.Kerr.Conjugation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Instances.Complex

namespace KN.Kerr
open Filter
open scoped Topology

/-- The indicial root in C002 Lemma 8.1 with physical real Ω and κ. -/
noncomputable def secondIndicialRoot (s m Ω κ : ℝ) (ω : ℂ) : ℂ :=
  (s : ℂ) + Complex.I * (ω - (m : ℂ) * (Ω : ℂ)) / (κ : ℂ)

theorem secondIndicialRoot_re (s m Ω κ : ℝ) (ω : ℂ) :
    (secondIndicialRoot s m Ω κ ω).re = s - ω.im / κ := by
  simp [secondIndicialRoot, Complex.div_re, Complex.normSq_apply]
  by_cases hκ : κ = 0
  · simp [hκ]
  · field_simp
    ring

theorem negative_spin_second_root (s m Ω κ : ℝ) (ω : ℂ)
    (hs : s < 0) (hκ : 0 < κ) (hω : 0 < ω.im) :
    (secondIndicialRoot s m Ω κ ω).re < 0 := by
  rw [secondIndicialRoot_re]
  exact negative_spin_indicial_real s ω.im κ hs hω hκ

/-- A normalized nonzero leading asymptotic coefficient detects a nonzero function. -/
theorem nonzero_of_normalized_limit {f scale : ℝ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hlim : Tendsto (fun r => f r / scale r) atTop (𝓝 c)) : f ≠ 0 := by
  intro hf
  have hz : Tendsto (fun r => f r / scale r) atTop (𝓝 0) := by
    simp [hf]
  exact hc (tendsto_nhds_unique hlim hz)

/-- The injectivity step of (58): once the differentiated outgoing expansion
is available, no upper-half-plane frequency can make the image zero.
This theorem does not assume a nonzero horizon leading coefficient. -/
theorem outgoing_derivative_ne_zero {f scale : ℝ → ℂ} {ω c₀ : ℂ} {n : ℕ}
    (hω : 0 < ω.im) (hc : c₀ ≠ 0)
    (hlim : Tendsto (fun r => iteratedDeriv n f r / scale r) atTop
      (𝓝 ((2 * Complex.I * ω) ^ n * c₀))) : iteratedDeriv n f ≠ 0 :=
  nonzero_of_normalized_limit
    (mul_ne_zero (outgoing_multiplier_nonzero ω hω n) hc) hlim

/-- Polynomial positivity used in the spin-weighted spherical spectrum (51). -/
theorem static_angular_eigenvalue_lower_bound (ell spin : ℝ)
    (hs : 0 ≤ spin) (hl : spin ≤ ell) :
    spin ≤ ell * (ell + 1) - spin ^ 2 := by
  have hsum : 0 ≤ ell + spin := by linarith
  have hprod := mul_nonneg (sub_nonneg.mpr hl) hsum
  nlinarith

/-- Imaginary part cancellation in (59), including a nonreal angular eigenvalue.
`linear` is real and cancels, rather than being assumed positive. -/
theorem angular_admissibility_identity (ω : ℂ) (static quad linear : ℝ) :
    (starRingEnd ℂ ω * ((static : ℂ) + ω * (linear : ℂ) - ω ^ 2 * (quad : ℂ))).im =
      -ω.im * (static + Complex.normSq ω * quad) := by
  simp [Complex.mul_im, Complex.mul_re, Complex.normSq_apply, pow_two]
  ring

end KN.Kerr
