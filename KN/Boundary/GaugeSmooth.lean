import KN.Boundary.GaugeGrowth
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Set MeasureTheory
namespace KN.Boundary

theorem gaugeIntegrand_contDiffOn (b : Background) (m : ℤ) (ω : ℂ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (gaugeIntegrand b m ω) (Ioi b.rPlus) := by
  have hcoe : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (x : ℂ)) :=
    Complex.ofRealCLM.contDiff
  unfold gaugeIntegrand
  simp only [div_eq_mul_inv]
  apply ContDiffOn.mul
  · unfold Background.frequencyK; fun_prop
  · apply ContDiffOn.inv
    · unfold Background.Delta; fun_prop
    · intro r hr
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (b.Delta_pos hr))

theorem gauge_contDiffOn (b : Background) (m : ℤ) (ω : ℂ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (gauge b m ω) (Ioi b.rPlus) := by
  let F : ℝ → ℂ := fun r => ∫ x in (2*b.rPlus)..r, gaugeIntegrand b m ω x
  have hF : ∀ r ∈ Ioi b.rPlus, HasDerivAt F (gaugeIntegrand b m ω r) r := by
    intro r hr
    apply intervalIntegral.integral_hasDerivAt_right
    · exact gaugeIntegrand_intervalIntegrable b m ω hr
    · have hm : Measurable (gaugeIntegrand b m ω) := by
        unfold gaugeIntegrand Background.frequencyK Background.Delta; fun_prop
      exact hm.stronglyMeasurable.stronglyMeasurableAtFilter
    · exact (gaugeIntegrand_continuousOn b m ω).continuousAt (Ioi_mem_nhds hr)
  have hFs : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F (Ioi b.rPlus) := by
    apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
    constructor
    · intro r hr; exact (hF r hr).differentiableAt.differentiableWithinAt
    · apply (gaugeIntegrand_contDiffOn b m ω).congr
      intro r hr
      exact (hF r hr).deriv
  have hex := ((contDiffOn_const (c := Complex.I)).mul hFs).cexp
  convert hex using 1
  rfl

end KN.Boundary
