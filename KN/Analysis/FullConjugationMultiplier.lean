import KN.Analysis.FullConjugation
import KN.Angular.FullMultiplier

noncomputable section
namespace KN.Analysis
open KN.Angular KN.Physics MeasureTheory
set_option backward.isDefEq.respectTransparency false

theorem fullConjugate_multiplier (b : KN.Background) (σ : ℝ) (u : FullAngularHilbert) :
    fullConjugate (fullFrequencyMultiplier b σ u)=
      -fullFrequencyMultiplier b σ (fullConjugate u) := by
  apply Lp.ext
  filter_upwards [fullConjugate_ae (fullFrequencyMultiplier b σ u),fullConjugate_ae u,
    fullFrequencyMultiplier_ae b σ u,fullFrequencyMultiplier_ae b σ (fullConjugate u),
    Lp.coeFn_neg (fullFrequencyMultiplier b σ (fullConjugate u))] with θ h1 h2 h3 h4 h5
  rw [h1,h3,h5]
  simp only [Pi.neg_apply]
  rw [h4,h2]
  have hh := conjugateFiber_potential (-σ*b.a*b.kappa*Real.sin θ) (σ*b.a*b.c*Real.cos θ) (u θ)
  simpa only [Complex.ofReal_mul,Complex.ofReal_neg] using hh

theorem fullRealStructure_multiplier (b : KN.Background) (σ : ℝ) (u : FullAngularHilbert) :
    fullRealStructure (fullFrequencyMultiplier b σ u)=
      fullFrequencyMultiplier b σ (fullRealStructure u) := by
  change fullI (fullConjugate (fullFrequencyMultiplier b σ u))=
    fullFrequencyMultiplier b σ (fullI (fullConjugate u))
  rw [fullConjugate_multiplier,map_neg,fullFrequencyMultiplier_I]

end KN.Analysis
