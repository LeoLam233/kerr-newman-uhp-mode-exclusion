import KN.ChargedRadial.ResonanceParameters
import KN.ChargedRadial.ExceptionalPair

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
namespace KN.ChargedRadial

abbrev PhysicalPair (b : KN.Background) (m : ℤ) (sigma omega lam : ℂ) :=
  SupportedPair b.rPlus (fun r => (b.Delta r:ℂ)) (physicalL b m sigma omega)
    (fun r => physicalR1 b sigma omega r+Complex.I*sigma*lam)
    (fun r => physicalR1 b sigma omega r-Complex.I*sigma*lam)
    (physicalDelta_smooth b) (physicalL_smooth b m sigma omega)
    ((physicalR1_smooth b sigma omega).add contDiff_const)
    ((physicalR1_smooth b sigma omega).sub contDiff_const)

/-- Both chiral signs and the exact physical Δ and L instantiate the canonical
supported continuation. No horizon cancellation or coefficient identity is left
as an unproved assumption in this wrapper. -/
theorem physical_nonresonant_supported_pair
    (b : KN.Background) (m : ℤ) (omega lam : ℂ) (sigma : ℝ)
    (hw : 0 < omega.im) (hs : sigma=1 ∨ sigma= -1)
    (hne : KN.Boundary.horizonAlpha b m omega sigma ≠ -1)
    (v z f g : ℝ → ℂ) (hf : Smooth f) (hg : Smooth g)
    (hv : ∀ t > b.rPlus, v t = ((t-b.rPlus : ℝ):ℂ)^(KN.Boundary.horizonAlpha b m omega sigma)*f t)
    (hz : ∀ t > b.rPlus, z t = ((t-b.rPlus : ℝ):ℂ)^(KN.Boundary.horizonAlpha b m omega sigma+1)*g t)
    (hfirst : ∀ t > b.rPlus, (b.Delta t:ℂ)*deriv v t+physicalL b m sigma omega t*v t =
      (physicalR1 b sigma omega t+Complex.I*sigma*lam)*z t)
    (hsecond : ∀ t > b.rPlus, deriv z t = (physicalR1 b sigma omega t-Complex.I*sigma*lam)*v t) :
    ∃ pair : PhysicalPair b m sigma omega lam,
      pair.v = finitePartAt b.rPlus (KN.Boundary.horizonAlpha b m omega sigma) f ∧
      pair.z = regularPowerAt b.rPlus (KN.Boundary.horizonAlpha b m omega sigma+1) g := by
  have ha : -2 < (KN.Boundary.horizonAlpha b m omega sigma).re := by
    rcases hs with rfl | rfl
    · exact KN.Boundary.horizonAlpha_positive_gt_neg_two b m omega hw
    · linarith [KN.Boundary.horizonAlpha_negative_gt_one b m omega hw]
  let d : ℝ → ℂ := fun t => (t:ℂ)-b.rMinus
  have hd : Smooth d := Complex.ofRealCLM.contDiff.sub contDiff_const
  have htd : Smooth (fun t : ℝ => ((t-b.rPlus):ℂ)*d t) :=
    (Complex.ofRealCLM.contDiff.sub contDiff_const).mul hd
  have hDelta : (fun t : ℝ => ((t-b.rPlus):ℂ)*d t) = fun t => (b.Delta t:ℂ) := by
    ext t
    dsimp [d]
    rw [b.delta_factor]
    push_cast
    rfl
  obtain ⟨pair,hvEq,hzEq⟩ := supported_pair_of_factorized_functions b.rPlus
    (KN.Boundary.horizonAlpha b m omega sigma) ha hne v z f g d
    (physicalL b m sigma omega)
    (fun t => physicalR1 b sigma omega t+Complex.I*sigma*lam)
    (fun t => physicalR1 b sigma omega t-Complex.I*sigma*lam)
    hf hg hd (physicalL_smooth b m sigma omega)
    ((physicalR1_smooth b sigma omega).add contDiff_const)
    ((physicalR1_smooth b sigma omega).sub contDiff_const) htd hv hz
    (fun t ht => by
      have hh := congrFun hDelta t
      simpa only [Complex.ofReal_sub, hh] using hfirst t ht)
    hsecond
  refine ⟨⟨pair.v,pair.z,pair.v_support,pair.z_support,?_,pair.second⟩,hvEq,hzEq⟩
  have hh := pair.first
  simpa only [hDelta] using hh

/-- The actual exceptional physical pair, with every horizon coefficient and
nonzero coupling obligation discharged from the indicial and angular identities. -/
theorem physical_resonant_supported_pair
    (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ) (sigma : ℝ)
    (hw : 0 < omega.im) (hs : sigma=1 ∨ sigma= -1)
    (ha : KN.Boundary.horizonAlpha b m omega sigma = -1)
    (T C D : ℝ) (hT : 0 ≤ T) (hD : D ≤ b.a^2*b.kappa^2)
    (hangular : lam^2 = (b.beta:ℂ)^2+(T:ℂ)+omega*(C:ℂ)+omega^2*(D:ℂ))
    (v z : ℝ → ℂ)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi b.rPlus))
    (hz : Smooth z)
    (hfirst : ∀ t > b.rPlus, (b.Delta t:ℂ)*deriv v t+physicalL b m sigma omega t*v t =
      (physicalR1 b sigma omega t+Complex.I*sigma*lam)*z t)
    (hsecond : ∀ t > b.rPlus, deriv z t = (physicalR1 b sigma omega t-Complex.I*sigma*lam)*v t) :
    ∃ f : ℝ → ℂ, Smooth f ∧ EqOn f v (Ioi b.rPlus) ∧
      ∃ pair : PhysicalPair b m sigma omega lam,
        pair.v = zeroExtension b.rPlus f+deltaValue b.rPlus
          (z b.rPlus/(physicalR1 b sigma omega b.rPlus-Complex.I*sigma*lam)) ∧
        pair.z = zeroExtension b.rPlus z := by
  exact supported_exceptional_pair b.rPlus v z _ _ _ _ hv hz
    (physicalDelta_smooth b) (physicalL_smooth b m sigma omega)
    ((physicalR1_smooth b sigma omega).add contDiff_const)
    ((physicalR1_smooth b sigma omega).sub contDiff_const)
    (physicalDelta_horizon_zero b) (resonance_horizon_coefficient b m omega sigma ha)
    (resonant_physical_coupling_nonzero b hQ m omega lam sigma hw hs ha T C D hT hD hangular)
    hfirst hsecond

/-- At the exceptional exponent the actual second component equals its smooth
horizon coefficient on the exterior. This transfers the original differential
pair to that representative before constructing the delta-corrected extension. -/
theorem physical_resonant_factorized_supported_pair
    (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (omega lam : ℂ) (sigma : ℝ)
    (hw : 0 < omega.im) (hs : sigma=1 ∨ sigma= -1)
    (ha : KN.Boundary.horizonAlpha b m omega sigma = -1)
    (T C D : ℝ) (hT : 0 ≤ T) (hD : D ≤ b.a^2*b.kappa^2)
    (hangular : lam^2 = (b.beta:ℂ)^2+(T:ℂ)+omega*(C:ℂ)+omega^2*(D:ℂ))
    (v z g : ℝ → ℂ)
    (hv : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) v (Ioi b.rPlus))
    (hg : Smooth g)
    (hz : ∀ t > b.rPlus, z t =
      ((t-b.rPlus : ℝ):ℂ)^(KN.Boundary.horizonAlpha b m omega sigma+1)*g t)
    (hfirst : ∀ t > b.rPlus, (b.Delta t:ℂ)*deriv v t+physicalL b m sigma omega t*v t =
      (physicalR1 b sigma omega t+Complex.I*sigma*lam)*z t)
    (hsecond : ∀ t > b.rPlus, deriv z t = (physicalR1 b sigma omega t-Complex.I*sigma*lam)*v t) :
    ∃ f : ℝ → ℂ, Smooth f ∧ EqOn f v (Ioi b.rPlus) ∧
      ∃ pair : PhysicalPair b m sigma omega lam,
        pair.v = zeroExtension b.rPlus f+deltaValue b.rPlus
          (g b.rPlus/(physicalR1 b sigma omega b.rPlus-Complex.I*sigma*lam)) ∧
        pair.z = zeroExtension b.rPlus g := by
  have he : EqOn z g (Ioi b.rPlus) := by
    intro t ht
    simpa only [ha, neg_add_cancel, Complex.cpow_zero, one_mul] using hz t ht
  apply physical_resonant_supported_pair b hQ m omega lam sigma hw hs ha
    T C D hT hD hangular v g hv hg
  · intro t ht
    simpa only [he ht] using hfirst t ht
  · intro t ht
    have hd : deriv z t = deriv g t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
      exact he hx
    rw [← hd]
    exact hsecond t ht

end KN.ChargedRadial
