import KN.ChargedRadial.PhysicalSupportedPair
import KN.ChargedRadial.PhysicalExceptionalTransform
import KN.ChargedRadial.PhysicalInjectivity
import KN.Boundary.RegularSingularFactorPair
import KN.ChargedRadial.PhysicalAngularData

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
namespace KN.ChargedRadial
open KN.Analysis KN.Boundary KN.Energy

/-- A transform constructed from the original radial pair. Its injectivity field
is a proved implication, not a substituted mode-exclusion hypothesis. -/
structure PhysicalTransformWitness (b : KN.Background) (m : ℤ)
    (sigma : ℝ) (omega lam : ℂ) (v : ℝ → ℂ) where
  pair : PhysicalPair b m sigma omega lam
  F : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ F {xi : ℂ | xi.im < -(b.eta*omega.im)}
  transform : IsFourierLaplaceTransform pair.v (-(b.eta*omega.im)) F
  bound : (fun x : ℝ => F (omega*x)) =O[atBot]
    (fun x : ℝ => (1+|x|)*Real.exp (omega.im*b.rPlus*x))
  deriv_bound : deriv (fun x : ℝ => F (omega*x)) =O[atBot]
    (fun x : ℝ => (1+|x|)*Real.exp (omega.im*b.rPlus*x))
  injective : (∀ x < -b.h, F (omega*(x:ℂ))=0) → EqOn v 0 (Ioi b.rPlus)

/-- Both nonresonant chiralities and the exceptional delta-corrected branch are
constructed from smooth horizon data and the actual outgoing conormal class. -/
theorem physical_transform_witness
    (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ) (sigma : ℝ)
    (hw : 0 < omega.im) (hs : sigma=1 ∨ sigma= -1)
    (T C D : ℝ) (hT : 0 ≤ T) (hD : D ≤ b.a^2*b.kappa^2)
    (hangular : lam^2=(b.beta:ℂ)^2+(T:ℂ)+omega*(C:ℂ)+omega^2*(D:ℂ))
    (w ws original v z : ℝ → ℂ)
    (hwh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) w (Ici b.rPlus))
    (hwsh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ws (Ici b.rPlus))
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi b.rPlus))
    (hvdef : ∀ r ∈ Ioi b.rPlus, v r=radialMultiplier b m omega (-(1+3*sigma)/2) r*w r)
    (hzdef : ∀ r ∈ Ioi b.rPlus, z r=(b.Delta r:ℂ)*radialMultiplier b m omega (-(1+3*sigma)/2) r*ws r)
    (hrescale : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m omega (3*sigma/4) r*original r)
    (hsmooth : ExteriorSmooth b.rPlus (fun r => gauge b m omega r*original r))
    (hout : PolynomialConormal (fun r => gauge b m omega r*original r))
    (hfirst : ∀ t > b.rPlus, (b.Delta t:ℂ)*deriv v t+physicalL b m sigma omega t*v t =
      (physicalR1 b sigma omega t+Complex.I*sigma*lam)*z t)
    (hsecond : ∀ t > b.rPlus, deriv z t=(physicalR1 b sigma omega t-Complex.I*sigma*lam)*v t) :
    Nonempty (PhysicalTransformWitness b m sigma omega lam v) := by
  obtain ⟨f,g,hf,hg,hfdef,hgdef⟩ := radialMultiplier_pair_factors b m omega sigma w ws hwh hwsh
  have hfv : ∀ t > b.rPlus, v t=((t-b.rPlus:ℝ):ℂ)^(horizonAlpha b m omega sigma)*f t :=
    fun t ht => (hvdef t ht).trans (hfdef t ht)
  have hgz : ∀ t > b.rPlus, z t=((t-b.rPlus:ℝ):ℂ)^(horizonAlpha b m omega sigma+1)*g t :=
    fun t ht => (hzdef t ht).trans (hgdef t ht)
  by_cases ha : horizonAlpha b m omega sigma = -1
  · obtain ⟨f0,hf0,he,pair,hpair,_⟩ := physical_resonant_factorized_supported_pair
      b hQ m omega lam sigma hw hs ha T C D hT hD hangular v z g hv hg hgz hfirst hsecond
    let coeff := g b.rPlus/(physicalR1 b sigma omega b.rPlus-Complex.I*sigma*lam)
    have hb := physical_exceptional_transform_bounds b m omega hw sigma hs w original f0
      hf0.continuous coeff hrescale (fun r hr => (he hr).trans (hvdef r hr)) hout
    refine ⟨⟨pair,correctedLaplace b.rPlus f0 coeff,hb.1,?_,hb.2.2.1,hb.2.2.2,?_⟩⟩
    · simpa only [hpair] using hb.2.1
    · exact physical_resonant_exterior_zero b omega coeff hw f0 v hf0.continuous he _ hb.1 hb.2.1
  · obtain ⟨pair,hpair,_⟩ := physical_nonresonant_supported_pair b m omega lam sigma hw hs ha
      v z f g hf hg hfv hgz hfirst hsecond
    have hb := physical_nonresonant_transform_bounds b m omega hw sigma hs w original f hf
      hrescale hfdef hsmooth hout ha
    dsimp only at hb
    refine ⟨⟨pair,_,hb.1,?_,hb.2.2.1,hb.2.2.2,?_⟩⟩
    · simpa only [hpair] using hb.2.1
    · apply physical_nonresonant_exterior_zero b omega _ hw _ ha f v hf hv.continuousOn (by simpa only [Complex.ofReal_sub] using hfv)
        _ hb.1 hb.2.1
      rcases hs with rfl|rfl
      · exact horizonAlpha_positive_gt_neg_two b m omega hw
      · linarith [horizonAlpha_negative_gt_one b m omega hw]

/-- Physical angular graph data discharge both exceptional nonvanishing
conditions in the unified construction. -/
theorem physical_transform_witness_of_angular_data
    (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ) (sigma : ℝ)
    (hw : 0 < omega.im) (hs : sigma=1 ∨ sigma= -1)
    (angular : PhysicalAngularData b m sigma omega lam)
    (w ws original v z : ℝ → ℂ)
    (hwh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) w (Ici b.rPlus))
    (hwsh : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) ws (Ici b.rPlus))
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi b.rPlus))
    (hvdef : ∀ r ∈ Ioi b.rPlus, v r=radialMultiplier b m omega (-(1+3*sigma)/2) r*w r)
    (hzdef : ∀ r ∈ Ioi b.rPlus, z r=(b.Delta r:ℂ)*radialMultiplier b m omega (-(1+3*sigma)/2) r*ws r)
    (hrescale : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m omega (3*sigma/4) r*original r)
    (hsmooth : ExteriorSmooth b.rPlus (fun r => gauge b m omega r*original r))
    (hout : PolynomialConormal (fun r => gauge b m omega r*original r))
    (hfirst : ∀ t > b.rPlus, (b.Delta t:ℂ)*deriv v t+physicalL b m sigma omega t*v t =
      (physicalR1 b sigma omega t+Complex.I*sigma*lam)*z t)
    (hsecond : ∀ t > b.rPlus, deriv z t=(physicalR1 b sigma omega t-Complex.I*sigma*lam)*v t) :
    Nonempty (PhysicalTransformWitness b m sigma omega lam v) := by
  exact physical_transform_witness b hQ m omega lam sigma hw hs
    (‖angular.staticImage‖^2-b.beta^2) angular.cross (b.a^2*(b.c^2+angular.sineAvg))
    (angular.T_nonneg b hQ m sigma hs omega lam) (angular.D_le b m sigma omega lam)
    angular.squared_expectation w ws original v z hwh hwsh hv hvdef hzdef hrescale hsmooth hout
    hfirst hsecond

end KN.ChargedRadial
