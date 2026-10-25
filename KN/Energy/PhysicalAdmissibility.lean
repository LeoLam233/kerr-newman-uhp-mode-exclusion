import KN.Boundary.RegularSingularFactorPair
import KN.Energy.PhysicalFactorTail
import KN.ChargedRadial.LaplaceAdmissibility

noncomputable section
open Filter Set Asymptotics MeasureTheory
namespace KN.Energy
open KN.Boundary KN.ChargedRadial KN.Analysis

theorem multiplier_rescaled_damped_integrable (b : Background) (m : ℤ) (ω : ℂ)
    (q e : ℝ) (hq : q+e ≤ 1) (w z f : ℝ → ℂ) (α : ℂ) (hα : -2 < α.re)
    (hf : ContDiff ℝ 1 f)
    (hw : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m ω e r*z r)
    (he : ∀ r ∈ Ioi b.rPlus,
      radialMultiplier b m ω q r*w r=((r-b.rPlus:ℝ):ℂ)^α*f r)
    (hs : ExteriorSmooth b.rPlus (fun r => gauge b m ω r*z r))
    (hout : PolynomialConormal (fun r => gauge b m ω r*z r))
    (β : ℝ) (hb : β < -(b.eta*ω.im)) (j : ℕ) :
    Integrable (dampedPowerFunction b.rPlus β (α+1) (fun r => f r*(r:ℂ)^j)) ∧
    Integrable (dampedPowerFunction b.rPlus β (α+1) (fun r => deriv f r*(r:ℂ)^j)) := by
  have htail := multiplier_rescaled_damped_moments b m ω q e hq w z f α
    (hf.differentiable one_ne_zero) hw he hs hout β hb j
  have hk : 0 < -(β+b.eta*ω.im)/2 := by linarith
  have ha : -1 < (α+1).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  constructor
  · apply dampedPower_integrable_of_exp_bound b.rPlus β (-(β+b.eta*ω.im)/2) hk
      (α+1) ha _ (hf.continuous.mul (Complex.continuous_ofReal.pow j))
    convert htail.1 using 1
    · ext r; simp only [Pi.mul_apply, Pi.pow_apply]; push_cast; ring
    · ext r; congr 1; ring
  · apply dampedPower_integrable_of_exp_bound b.rPlus β (-(β+b.eta*ω.im)/2) hk
      (α+1) ha _ ((hf.continuous_deriv le_rfl).mul (Complex.continuous_ofReal.pow j))
    convert htail.2 using 1
    · ext r; simp only [Pi.mul_apply, Pi.pow_apply]; push_cast; ring
    · ext r; congr 1; ring

/-- Physical outgoing conormal control, not an assumed transform growth
condition, supplies exponential temperedness of the actual finite part. -/
theorem multiplier_rescaled_laplaceAdmissible (b : Background) (m : ℤ) (ω : ℂ)
    (q e : ℝ) (hq : q+e ≤ 1) (w z f : ℝ → ℂ) (α : ℂ) (hα : -2 < α.re)
    (hf : ContDiff ℝ 1 f)
    (hw : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m ω e r*z r)
    (he : ∀ r ∈ Ioi b.rPlus,
      radialMultiplier b m ω q r*w r=((r-b.rPlus:ℝ):ℂ)^α*f r)
    (hs : ExteriorSmooth b.rPlus (fun r => gauge b m ω r*z r))
    (hout : PolynomialConormal (fun r => gauge b m ω r*z r)) :
    LaplaceAdmissible b.rPlus (-(b.eta*ω.im)) (finitePartAt b.rPlus α f) := by
  apply finitePartAt_laplaceAdmissible b.rPlus (-(b.eta*ω.im)) α hα f hf
  intro β hb
  simpa only [pow_zero,mul_one] using
    multiplier_rescaled_damped_integrable b m ω q e hq w z f α hα hf hw he hs hout β hb 0

/-- Both physical chiral signs instantiate the actual finite-part admissibility
criterion directly from horizon smoothness and outgoing conormal control. -/
theorem physical_finitePart_exists_admissible (b : Background) (m : ℤ) (ω : ℂ)
    (hω : 0 < ω.im) (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (w z : ℝ → ℂ)
    (hwSmooth : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) w (Ici b.rPlus))
    (hw : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m ω (3*σ/4) r*z r)
    (hs : ExteriorSmooth b.rPlus (fun r => gauge b m ω r*z r))
    (hout : PolynomialConormal (fun r => gauge b m ω r*z r)) :
    ∃ f : ℝ → ℂ, Smooth f ∧
      (∀ r ∈ Ioi b.rPlus,
        radialMultiplier b m ω (-(1+3*σ)/2) r*w r =
          ((r-b.rPlus:ℝ):ℂ)^(horizonAlpha b m ω σ)*f r) ∧
      LaplaceAdmissible b.rPlus (-(b.eta*ω.im)) (finitePartAt b.rPlus (horizonAlpha b m ω σ) f) ∧
      ∀ β < -(b.eta*ω.im), ∀ j : ℕ,
        Integrable (dampedPowerFunction b.rPlus β (horizonAlpha b m ω σ+1)
          (fun r => f r*(r:ℂ)^j)) ∧
        Integrable (dampedPowerFunction b.rPlus β (horizonAlpha b m ω σ+1)
          (fun r => deriv f r*(r:ℂ)^j)) := by
  obtain ⟨f,_,hf,_,he,_⟩ := radialMultiplier_pair_factors b m ω σ w (fun _ => 0)
    hwSmooth contDiffOn_const
  have hq : -(1+3*σ)/2+3*σ/4 ≤ 1 := by rcases hσ with rfl|rfl <;> norm_num
  have hα : -2 < (horizonAlpha b m ω σ).re := by
    rcases hσ with rfl|rfl
    · exact horizonAlpha_positive_gt_neg_two b m ω hω
    · linarith [horizonAlpha_negative_gt_one b m ω hω]
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  refine ⟨f,hf,he,?_,?_⟩
  · exact multiplier_rescaled_laplaceAdmissible b m ω _ _ hq w z f _ hα hf1 hw he hs hout
  · intro β hb j
    exact multiplier_rescaled_damped_integrable b m ω _ _ hq w z f _ hα hf1 hw he hs hout β hb j

end KN.Energy
