import KN.Boundary.GaugeSmooth
import Mathlib.Analysis.Calculus.LogDeriv

noncomputable section
open Set MeasureTheory
namespace KN.Analysis

def expPrimitive (h : ℝ → ℂ) (base r : ℝ) : ℂ :=
  Complex.exp (∫ x in base..r, h x)

theorem intervalPrimitive_hasDerivAt (h : ℝ → ℂ) (lo base r : ℝ)
    (hh : ContinuousOn h (Ioi lo)) (hb : lo < base) (hr : lo < r) :
    HasDerivAt (fun r => ∫ x in base..r, h x) (h r) r := by
  have hs : uIcc base r ⊆ Ioi lo := by
    intro x hx
    exact lt_of_lt_of_le (lt_min hb hr) hx.1
  have hc := hh.continuousAt (Ioi_mem_nhds hr)
  apply intervalIntegral.integral_hasDerivAt_right (hh.mono hs).intervalIntegrable
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hh r hr
  · exact hc

theorem expPrimitive_hasDerivAt (h : ℝ → ℂ) (lo base r : ℝ)
    (hh : ContinuousOn h (Ioi lo)) (hb : lo < base) (hr : lo < r) :
    HasDerivAt (expPrimitive h base) (expPrimitive h base r*h r) r := by
  exact (intervalPrimitive_hasDerivAt h lo base r hh hb hr).cexp

theorem expPrimitive_contDiffOn (h : ℝ → ℂ) (lo base : ℝ)
    (hh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) h (Ioi lo)) (hb : lo < base) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (expPrimitive h base) (Ioi lo) := by
  have hd := fun r hr => intervalPrimitive_hasDerivAt h lo base r hh.continuousOn hb hr
  have hi : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r => ∫ x in base..r, h x) (Ioi lo) := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
    constructor
    · intro r hr; exact (hd r hr).differentiableAt.differentiableWithinAt
    · apply hh.congr; intro r hr; exact (hd r hr).deriv
  exact hi.cexp

theorem expPrimitive_ne_zero (h : ℝ → ℂ) (base r : ℝ) : expPrimitive h base r ≠ 0 :=
  Complex.exp_ne_zero _

end KN.Analysis
