import KN.Boundary.RegularSingularFactorGlobal
import KN.ChargedRadial.CanonicalInterface

noncomputable section
open Set
namespace KN.Boundary

/-- The two physical multiplier-weighted components have the exact powers used
by the supported distribution construction. The sole external dependency here
is the separately declared general Seeley half-line extension theorem. -/
theorem radialMultiplier_pair_factors (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ)
    (w ws : ℝ → ℂ)
    (hw : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) w (Ici b.rPlus))
    (hs : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ws (Ici b.rPlus)) :
    ∃ f g : ℝ → ℂ, KN.ChargedRadial.Smooth f ∧ KN.ChargedRadial.Smooth g ∧
      (∀ r ∈ Ioi b.rPlus,
        radialMultiplier b m ω (-(1+3*σ)/2) r*w r =
          ((r-b.rPlus:ℝ):ℂ)^(horizonAlpha b m ω σ)*f r) ∧
      (∀ r ∈ Ioi b.rPlus,
        (b.Delta r:ℂ)*radialMultiplier b m ω (-(1+3*σ)/2) r*ws r =
          ((r-b.rPlus:ℝ):ℂ)^(horizonAlpha b m ω σ+1)*g r) := by
  obtain ⟨a,ha,_,he⟩ := radialMultiplier_global_horizon_factor b m ω σ
  obtain ⟨W,hW,hWe⟩ := KN.ChargedRadial.External.smooth_halfline_extension b.rPlus w hw
  obtain ⟨S,hS,hSe⟩ := KN.ChargedRadial.External.smooth_halfline_extension b.rPlus ws hs
  refine ⟨fun r => a r*W r, fun r => ((r-b.rMinus:ℝ):ℂ)*a r*S r,
    ha.mul hW, ?_, ?_, ?_⟩
  · exact ((Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)).mul ha).mul hS
  · intro r hr
    dsimp only
    rw [he r hr, hWe (show r ∈ Ici b.rPlus from le_of_lt (show b.rPlus < r from hr))]
    ring
  · intro r hr
    dsimp only
    rw [he r hr, hSe (show r ∈ Ici b.rPlus from le_of_lt (show b.rPlus < r from hr)),
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hr))),
      Complex.cpow_one, b.delta_factor]
    push_cast
    ring

end KN.Boundary
