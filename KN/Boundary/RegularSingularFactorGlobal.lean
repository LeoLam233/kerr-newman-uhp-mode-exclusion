import KN.Boundary.RegularSingularFactorPhysical
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section
open Set
namespace KN.Boundary

/-- A globally smooth map into a half-line, equal to the identity above b. -/
def smoothExteriorRetraction (a b r : ℝ) : ℝ :=
  a + Real.smoothTransition ((r-a)/(b-a))*(r-a)

theorem smoothExteriorRetraction_smooth (a b : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (smoothExteriorRetraction a b) := by
  unfold smoothExteriorRetraction
  fun_prop

theorem smoothExteriorRetraction_lower (a b r : ℝ) (hab : a < b) :
    a ≤ smoothExteriorRetraction a b r := by
  unfold smoothExteriorRetraction
  by_cases hr : a ≤ r
  · exact le_add_of_nonneg_right (mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr hr))
  · rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_of_not_ge hr)) (sub_nonneg.mpr hab.le)),zero_mul,add_zero]

theorem smoothExteriorRetraction_eq (a b r : ℝ) (hab : a < b) (hr : b ≤ r) :
    smoothExteriorRetraction a b r = r := by
  unfold smoothExteriorRetraction
  rw [Real.smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hab)).mpr (by linarith))]
  ring


theorem extend_smooth_halfline (lo rp : ℝ) (hlo : lo < rp) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi lo))
    (hn : ∀ r, f r ≠ 0) :
    ∃ F : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      (∀ r ≥ rp, F r=f r) ∧ (∀ r, F r ≠ 0) := by
  let a := (lo+rp)/2
  have ha : lo < a := by dsimp [a]; linarith
  have hab : a < rp := by dsimp [a]; linarith
  let φ := smoothExteriorRetraction a rp
  have hm : MapsTo φ univ (Ioi lo) := by
    intro r _
    exact lt_of_lt_of_le ha (smoothExteriorRetraction_lower a rp r hab)
  refine ⟨fun r => f (φ r), ?_, ?_, fun r => hn (φ r)⟩
  · exact contDiffOn_univ.mp
      (hf.comp (smoothExteriorRetraction_smooth a rp).contDiffOn hm)
  · intro r hr
    change f (φ r) = f r
    rw [show φ r = r from smoothExteriorRetraction_eq a rp r hab hr]

theorem radialMultiplier_global_horizon_factor (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ) :
    ∃ f : ℝ → ℂ,
      ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ r, f r ≠ 0) ∧
      ∀ r ∈ Ioi b.rPlus,
        radialMultiplier b m ω (-(1+3*σ)/2) r =
          ((r-b.rPlus:ℝ):ℂ)^(horizonAlpha b m ω σ)*f r := by
  obtain ⟨f,hf,hn,he⟩ := radialMultiplier_horizon_factor b m ω σ
  obtain ⟨F,hF,hFe,hFn⟩ := extend_smooth_halfline b.rMinus b.rPlus
    (by linarith [b.horizon_gap,b.delta_pos]) f hf hn
  refine ⟨F,hF,hFn,?_⟩
  intro r hr
  rw [hFe r hr.le]
  exact he r hr

end KN.Boundary
