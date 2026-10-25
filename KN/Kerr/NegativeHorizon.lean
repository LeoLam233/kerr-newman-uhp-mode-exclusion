import KN.Kerr.FuchsInterface
import KN.Background.Parameters
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic

namespace KN.Kerr
open Set Filter
open scoped Topology ContDiff

noncomputable def horizonA (b : KN.Background) (r : ℝ) : ℂ := (r - b.rMinus : ℝ)
noncomputable def radialP (b : KN.Background) (m : ℤ) (omega : ℂ) (s : ℝ) (r : ℝ) : ℂ :=
  (1 - (s : ℂ)) * (2 * ((r : ℂ) - b.M)) + 2 * Complex.I * b.frequencyK m omega r
noncomputable def radialC (b : KN.Background) (m : ℤ) (omega Λ : ℂ) (s : ℝ) (r : ℝ) : ℂ :=
  2 * Complex.I * (2 * (s : ℂ) - 1) * omega * r - s - Λ -
  (b.a : ℂ)^2 * omega^2 + 2 * b.a * m * omega

/-- The exact conjugated radial equation (53), on the full exterior. -/
def ConjugatedEquation (b : KN.Background) (m : ℤ) (omega Λ : ℂ) (s : ℝ)
    (f : ℝ → ℂ) : Prop :=
  ∀ r ∈ Ioi b.rPlus, (b.Delta r : ℂ) * deriv (deriv f) r +
    radialP b m omega s r * deriv f r + radialC b m omega Λ s r * f r = 0

theorem horizonA_nonzero (b : KN.Background) (r : ℝ) (hr : r ∈ Ici b.rPlus) :
    horizonA b r ≠ 0 := by
  have hp : 0 < r - b.rMinus := by
    have hg := b.horizon_gap
    have hd := b.delta_pos
    change b.rPlus ≤ r at hr
    linarith
  unfold horizonA
  exact_mod_cast ne_of_gt hp

/-- The Fuchs indicial quotient is verified from the actual Kerr coefficients. -/
theorem radialP_horizon_quotient (b : KN.Background) (m : ℤ) (omega : ℂ) (s : ℝ) :
    (radialP b m omega s b.rPlus / horizonA b b.rPlus).re =
      1 - s + (b.rPlus ^ 2 + b.a ^ 2) * omega.im / b.delta := by
  have hd : b.delta ≠ 0 := ne_of_gt b.delta_pos
  simp [radialP, horizonA, Background.frequencyK, Background.rPlus,
    Background.rMinus, Complex.div_re, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, pow_two]
  field_simp
  ring

/-- C002 Lemma 8.1's decisive boundary fact, instantiated from general Fuchs theory.
Unlike the classical interface, all specialized coefficient hypotheses are proved here. -/
theorem negative_horizon_analytic_nonzero
    (b : KN.Background) (m : ℤ) (omega Λ : ℂ) (s : ℝ)
    (hs : s < 0) (homega : 0 < omega.im)
    (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (heq : ConjugatedEquation b m omega Λ s f)
    (hne : ∃ r ∈ Ici b.rPlus, f r ≠ 0) :
    ∃ g : ℝ → ℂ, AnalyticAt ℝ g b.rPlus ∧ f =ᶠ[𝓝[≥] b.rPlus] g ∧ g b.rPlus ≠ 0 := by
  have hA : AnalyticOnNhd ℝ (horizonA b) (Ici b.rPlus) := by
    intro r _
    unfold horizonA
    exact Complex.ofRealCLM.analyticAt _ |>.comp (analyticAt_id.sub analyticAt_const)
  have hB : AnalyticOnNhd ℝ (radialP b m omega s) (Ici b.rPlus) := by
    intro r _
    have hc : AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) r := Complex.ofRealCLM.analyticAt r
    unfold radialP Background.frequencyK
    fun_prop
  have hC : AnalyticOnNhd ℝ (radialC b m omega Λ s) (Ici b.rPlus) := by
    intro r _
    have hc : AnalyticAt ℝ (fun x : ℝ => (x : ℂ)) r := Complex.ofRealCLM.analyticAt r
    unfold radialC
    fun_prop
  have hi : 1 < (radialP b m omega s b.rPlus / horizonA b b.rPlus).re := by
    rw [radialP_horizon_quotient]
    have hp : 0 < b.rPlus ^ 2 + b.a ^ 2 := by nlinarith [b.rPlus_pos, sq_nonneg b.a]
    have hterm := div_pos (mul_pos hp homega) b.delta_pos
    linarith
  have heq' : ∀ r ∈ Ioi b.rPlus,
      (r - b.rPlus : ℝ) * horizonA b r * deriv (deriv f) r +
      radialP b m omega s r * deriv f r + radialC b m omega Λ s r * f r = 0 := by
    intro r hr
    have hfactor : ((r - b.rPlus : ℝ) : ℂ) * horizonA b r = (b.Delta r : ℂ) := by
      rw [horizonA, ← Complex.ofReal_mul, b.delta_factor]
    rw [hfactor]
    exact heq r hr
  obtain ⟨⟨g, hg, hfg⟩, hzero⟩ := External.fuchs_smooth_halfline_classification
    b.rPlus (horizonA b) (radialP b m omega s) (radialC b m omega Λ s) f
    hA hB hC (horizonA_nonzero b) hi hf heq'
  refine ⟨g, hg, hfg, ?_⟩
  intro hgzero
  have hfg0 : f b.rPlus = g b.rPlus := mem_of_mem_nhdsWithin (a := b.rPlus) (s := Ici b.rPlus) self_mem_Ici hfg
  obtain ⟨r, hr, hnr⟩ := hne
  exact hnr (hzero (hfg0.trans hgzero) r hr)

end KN.Kerr
