import KN.Kerr.HorizonPreservation
import KN.Boundary.GaugeSmooth

namespace KN.Kerr
open Set
open scoped ContDiff

/-- The actual reversed field is smooth on the open exterior. -/
theorem reversedRadial_contDiffOn (b : KN.Background) (m : ℤ) (omega : ℂ)
    (k n : ℕ) (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus)) :
    ContDiffOn ℝ ∞ (reversedRadial b m omega (k : ℝ) n f) (Ioi b.rPlus) := by
  have hweight : ContDiffOn ℝ ∞ (fun r => (Real.rpow (b.Delta r) (k : ℝ) : ℂ)) (Ioi b.rPlus) := by
    change ContDiffOn ℝ ∞ (fun r => ((b.Delta r ^ (k : ℝ) : ℝ) : ℂ)) _
    simp only [Real.rpow_natCast]
    have hd : ContDiff ℝ ∞ (fun r => b.Delta r ^ k) := by
      unfold Background.Delta
      fun_prop
    exact (Complex.ofRealCLM.contDiff.comp hd).contDiffOn
  exact ((KN.Boundary.gauge_contDiffOn b m omega).mul hweight).mul
    ((horizon_coefficient_derivatives hf n).mono Ioi_subset_Ici_self)

end KN.Kerr
