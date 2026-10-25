import KN.ChargedRadial.DistributionMultiplication

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

/-- Complex smooth multiplication agrees with ordinary multiplication on locally
integrable functions, including those of exponential rather than temperate growth. -/
theorem mulComplexDist_ofFun (mu : Measure ℝ) (f g : ℝ → ℂ)
    (hf : LocallyIntegrable f mu)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) :
    mulComplexDist g hg (Distribution.ofFun (⊤ : Opens ℝ) f mu ⊤) =
      Distribution.ofFun (⊤ : Opens ℝ) (fun t => g t*f t) mu ⊤ := by
  ext phi
  have hloc := hf.locallyIntegrableOn (univ : Set ℝ)
  have hprod := (hf.continuous_mul hg.continuous).locallyIntegrableOn (univ : Set ℝ)
  change Distribution.ofFun (⊤ : Opens ℝ) f mu ⊤
      (mulTest (fun t => (g t).re) (Complex.reCLM.contDiff.comp hg) phi) +
    Complex.I*Distribution.ofFun (⊤ : Opens ℝ) f mu ⊤
      (mulTest (fun t => (g t).im) (Complex.imCLM.contDiff.comp hg) phi) = _
  rw [Distribution.ofFun_apply hloc, Distribution.ofFun_apply hloc, Distribution.ofFun_apply hprod]
  have hi1 := (mulTest (fun t => (g t).re) (Complex.reCLM.contDiff.comp hg) phi).integrable_smul hloc
  have hi2 := (mulTest (fun t => (g t).im) (Complex.imCLM.contDiff.comp hg) phi).integrable_smul hloc
  rw [← integral_const_mul, ← integral_add hi1 (hi2.const_mul Complex.I)]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [mulTest_apply, Complex.real_smul, Complex.ofReal_mul]
  calc
    _ = (phi t:ℂ)*((g t).re+(g t).im*Complex.I)*f t := by ring
    _ = _ := by rw [Complex.re_add_im]; ring

theorem mulComplexDist_zeroExtension (r : ℝ) (f g : ℝ → ℂ) (hf : Continuous f)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) :
    mulComplexDist g hg (zeroExtension r f) = zeroExtension r (fun t => g t*f t) := by
  exact mulComplexDist_ofFun _ f g hf.locallyIntegrable hg

lemma zeroExtension_congr (r : ℝ) (f g : ℝ → ℂ)
    (h : EqOn f g (Ioi r)) : zeroExtension r f = zeroExtension r g := by
  apply Distribution.ofFun_congr_ae
  simp only [Opens.coe_top, Measure.restrict_univ]
  exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall h)

/-- The uncorrected second equation's delta coefficient is exactly z(r₊). -/
theorem zeroExtension_second_source (r : ℝ) (v z B : ℝ → ℂ)
    (hv : Continuous v) (hz : ContDiff ℝ 1 z)
    (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B)
    (heq : ∀ t > r, deriv z t = B t*v t) :
    Distribution.lineDerivCLM (1:ℝ) (zeroExtension r z) =
      mulComplexDist B hB (zeroExtension r v)+deltaValue r (z r) := by
  rw [derivative_zeroExtension r z hz, mulComplexDist_zeroExtension r v B hv hB]
  rw [zeroExtension_congr r (deriv z) (fun t => B t*v t) heq]

/-- Actual zero extensions with the coefficient z(r₊)/B(r₊), not a formal
boundary-source assumption. This closes the second equation in (35). -/
theorem corrected_zeroExtension_second (r : ℝ) (v z B : ℝ → ℂ)
    (hv : Continuous v) (hz : ContDiff ℝ 1 z)
    (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hBr : B r ≠ 0) (heq : ∀ t > r, deriv z t = B t*v t) :
    Distribution.lineDerivCLM (1:ℝ) (zeroExtension r z) =
      mulComplexDist B hB (zeroExtension r v+deltaValue r (z r/B r)) := by
  exact complex_correction_repairs_second B hB r hBr _ _ _
    (zeroExtension_second_source r v z B hv hz hB heq)

lemma zeroExtension_add (r : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    zeroExtension r (f+g) = zeroExtension r f+zeroExtension r g := by
  exact Distribution.ofFun_add (hf.locallyIntegrable.locallyIntegrableOn _)
    (hg.locallyIntegrable.locallyIntegrableOn _)

/-- Vanishing of Δ at the horizon removes the first equation's ordinary extension
boundary term. It does not remove the second equation's boundary source. -/
theorem zeroExtension_first_homogeneous (r : ℝ) (v z Delta L A : ℝ → ℂ)
    (hv : ContDiff ℝ 1 v) (hz : Continuous z)
    (hDelta : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Delta)
    (hL : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hzero : Delta r = 0)
    (heq : ∀ t > r, Delta t*deriv v t+L t*v t = A t*z t) :
    mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) (zeroExtension r v))+
      mulComplexDist L hL (zeroExtension r v) = mulComplexDist A hA (zeroExtension r z) := by
  rw [derivative_zeroExtension r v hv, map_add, mulComplexDist_deltaValue, hzero, zero_mul]
  have hd0 : deltaValue r 0 = 0 := by ext phi; simp [deltaValue_apply]
  rw [hd0, add_zero, mulComplexDist_zeroExtension r (deriv v) Delta
    (hv.continuous_deriv le_rfl) hDelta,
    mulComplexDist_zeroExtension r v L hv.continuous hL,
    mulComplexDist_zeroExtension r z A hz hA]
  rw [← zeroExtension_add r (fun t => Delta t*deriv v t) (fun t => L t*v t) (hDelta.continuous.mul (hv.continuous_deriv le_rfl))
    (hL.continuous.mul hv.continuous)]
  exact zeroExtension_congr r _ _ heq

/-- The complete exceptional supported correction, with its ordinary zero-extension
sources derived from the actual first-order equations. Smoothness and the two geometric
horizon identities are explicit hypotheses to be established by radial boundary transport. -/
theorem corrected_zeroExtension_pair (r : ℝ) (v z Delta L A B : ℝ → ℂ)
    (hv : ContDiff ℝ 1 v) (hz : ContDiff ℝ 1 z)
    (hDelta : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Delta)
    (hL : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hzero : Delta r = 0) (hres : L r = deriv Delta r) (hBr : B r ≠ 0)
    (hfirst : ∀ t > r, Delta t*deriv v t+L t*v t = A t*z t)
    (hsecond : ∀ t > r, deriv z t = B t*v t) :
    let ve := zeroExtension r v+deltaValue r (z r/B r)
    let ze := zeroExtension r z
    (mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) ve)+
      mulComplexDist L hL ve = mulComplexDist A hA ze) ∧
    (Distribution.lineDerivCLM (1:ℝ) ze = mulComplexDist B hB ve) := by
  constructor
  · exact complex_correction_preserves_first Delta L A hDelta hL hA r (z r/B r)
      hzero hres _ _ (zeroExtension_first_homogeneous r v z Delta L A hv hz.continuous
        hDelta hL hA hzero hfirst)
  · exact corrected_zeroExtension_second r v z B hv.continuous hz hB hBr hsecond

end KN.ChargedRadial
