import KN.Boundary.RegularSingularFactorPair
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial
open KN.Boundary

theorem shifted_power_smooth (r : ℝ) (alpha : ℂ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ((t-r:ℝ):ℂ)^alpha) (Ioi r) := by
  have hl : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.log (t-r)) (Ioi r) :=
    (contDiff_id.sub contDiff_const).contDiffOn.log (fun t ht => ne_of_gt (sub_pos.mpr ht))
  have he := ((Complex.ofRealCLM.contDiff.comp_contDiffOn hl).mul (contDiffOn_const (c := alpha))).cexp
  apply he.congr
  intro t ht
  exact (positivePower_eq_cpow r t alpha ht).symm

theorem factorized_exterior_smooth (r : ℝ) (alpha : ℂ) (f v : ℝ → ℂ)
    (hf : Smooth f) (he : ∀ t > r, v t=((t-r:ℝ):ℂ)^alpha*f t) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi r) := by
  apply ((shifted_power_smooth r alpha).mul hf.contDiffOn).congr
  intro t ht
  exact he t ht

/-- Exterior regularity of the multiplier-weighted component is inherited
from the original smooth horizon class and the proved factorization. -/
theorem multiplier_exterior_smooth (b : KN.Background) (m : ℤ) (omega : ℂ)
    (sigma : ℝ) (w v : ℝ → ℂ)
    (hw : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) w (Ici b.rPlus))
    (hv : ∀ r ∈ Ioi b.rPlus, v r=radialMultiplier b m omega (-(1+3*sigma)/2) r*w r) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi b.rPlus) := by
  obtain ⟨f,g,hf,_,he,_⟩ := radialMultiplier_pair_factors b m omega sigma w w hw hw
  exact factorized_exterior_smooth b.rPlus (horizonAlpha b m omega sigma) f v hf
    (fun r hr => (hv r hr).trans (he r hr))

end KN.ChargedRadial
