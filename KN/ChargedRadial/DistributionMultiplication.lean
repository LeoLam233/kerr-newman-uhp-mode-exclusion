import KN.ChargedRadial.ZeroExtension
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

/-- Multiplication of real test functions by a smooth real function.
Continuity in the LF test-function topology follows by the compact-support stages. -/
def mulTest (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) :
    𝓓((⊤ : Opens ℝ), ℝ) →L[ℝ] 𝓓((⊤ : Opens ℝ), ℝ) :=
  TestFunction.limitCLM ℝ
    (fun phi => ⟨fun x => phi x*g x, phi.contDiff.mul hg,
      phi.hasCompactSupport.mul_right, by simp⟩)
    (fun K hK => TestFunction.ofSupportedInCLM ℝ hK ∘L
      ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) hg)
    (fun _ _ _ => rfl)

lemma mulTest_apply (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (phi : 𝓓((⊤ : Opens ℝ), ℝ)) (x : ℝ) : mulTest g hg phi x = phi x*g x := rfl

/-- Smooth real multiplication on general complex distributions. -/
def mulDist (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) :
    CDist →L[ℝ] CDist := (mulTest g hg).precompCompactConvergenceCLM ℂ

lemma mulDist_apply (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (T : CDist) (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    mulDist g hg T phi = T (mulTest g hg phi) := rfl

lemma mulDist_deltaValue (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g)
    (r : ℝ) (z : ℂ) : mulDist g hg (deltaValue r z) = deltaValue r (g r • z) := by
  ext phi
  simp only [mulDist_apply, deltaValue_apply, mulTest_apply, mul_smul]

/-- The delta derivative multiplication formula in the ordinary, non-tempered
space of distributions. This permits polynomial coefficients despite an exponentially
growing outgoing tail. -/
theorem mulDist_derivative_deltaValue
    (g : ℝ → ℝ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) (r : ℝ) (z : ℂ) :
    mulDist g hg (Distribution.lineDerivCLM (1:ℝ) (deltaValue r z)) =
      Distribution.lineDerivCLM (1:ℝ) (deltaValue r (g r • z)) -
        deltaValue r (deriv g r • z) := by
  ext phi
  simp only [mulDist_apply, Distribution.lineDerivCLM_apply, deltaValue_apply]
  change -(TestFunction.lineDerivCLM ℝ (1:ℝ) (mulTest g hg phi) r • z) =
    -(TestFunction.lineDerivCLM ℝ (1:ℝ) phi r • (g r • z)) - phi r • (deriv g r • z)
  rw [testFunction_deriv, testFunction_deriv]
  have he : (mulTest g hg phi : ℝ → ℝ) = (phi : ℝ → ℝ)*g := rfl
  rw [he, deriv_mul (phi.contDiff.differentiable (by simp) r) (hg.differentiable (by simp) r)]
  simp only [add_smul, mul_smul]
  abel

/-- The geometric horizon cancellation for real Δ and real L on ordinary
complex distributions, with no tempered-growth assumption. -/
theorem resonant_delta_general
    (Delta L : ℝ → ℝ)
    (hDelta : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Delta)
    (hL : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) L)
    (r : ℝ) (z : ℂ) (hzero : Delta r = 0) (hres : L r = deriv Delta r) :
    mulDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) (deltaValue r z)) +
      mulDist L hL (deltaValue r z) = 0 := by
  rw [mulDist_derivative_deltaValue, mulDist_deltaValue, hzero, hres]
  ext phi
  simp [Distribution.lineDerivCLM_apply, deltaValue_apply]

/-- Complex smooth multiplication obtained by complexifying real test functions. -/
def mulComplexDist (g : ℝ → ℂ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) :
    CDist →L[ℝ] CDist :=
  mulDist (fun t => (g t).re) (Complex.reCLM.contDiff.comp hg) +
    Complex.I • mulDist (fun t => (g t).im) (Complex.imCLM.contDiff.comp hg)

lemma mulComplexDist_deltaValue
    (g : ℝ → ℂ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) (r : ℝ) (z : ℂ) :
    mulComplexDist g hg (deltaValue r z) = deltaValue r (g r*z) := by
  ext phi
  change (phi r*(g r).re) • z + Complex.I*((phi r*(g r).im) • z) = phi r • (g r*z)
  simp only [Complex.real_smul, Complex.ofReal_mul]
  calc
    _ = (phi r:ℂ)*((g r).re+(g r).im*Complex.I)*z := by ring
    _ = _ := by rw [Complex.re_add_im]; ring

lemma realPart_deriv (g : ℝ → ℂ) (hg : Differentiable ℝ g) (r : ℝ) :
    deriv (fun t => (g t).re) r = (deriv g r).re := by
  exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hg r).hasDerivAt).deriv

lemma imagPart_deriv (g : ℝ → ℂ) (hg : Differentiable ℝ g) (r : ℝ) :
    deriv (fun t => (g t).im) r = (deriv g r).im := by
  exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (hg r).hasDerivAt).deriv

/-- Full complex polynomial coefficient delta cancellation in ordinary distributions. -/
theorem mulComplexDist_derivative_deltaValue
    (g : ℝ → ℂ) (hg : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) g) (r : ℝ) (z : ℂ) :
    mulComplexDist g hg (Distribution.lineDerivCLM (1:ℝ) (deltaValue r z)) =
      Distribution.lineDerivCLM (1:ℝ) (deltaValue r (g r*z)) -
        deltaValue r (deriv g r*z) := by
  change mulDist _ _ _ + Complex.I • mulDist _ _ _ = _
  rw [mulDist_derivative_deltaValue, mulDist_derivative_deltaValue,
    realPart_deriv g (hg.differentiable (by simp)),
    imagPart_deriv g (hg.differentiable (by simp))]
  ext phi
  change -(deriv phi r • ((g r).re • z)) - phi r • ((deriv g r).re • z) +
    Complex.I*(-(deriv phi r • ((g r).im • z)) - phi r • ((deriv g r).im • z)) =
    -(deriv phi r • (g r*z)) - phi r • (deriv g r*z)
  simp only [Complex.real_smul]
  calc
    _ = -((deriv (phi : ℝ → ℝ) r : ℝ):ℂ)*((g r).re+(g r).im*Complex.I)*z -
      (phi r:ℂ)*((deriv g r).re+(deriv g r).im*Complex.I)*z := by ring
    _ = _ := by rw [Complex.re_add_im, Complex.re_add_im]; ring

theorem complex_resonant_delta_annihilated
    (Delta L : ℝ → ℂ)
    (hDelta : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Delta)
    (hL : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) L)
    (r : ℝ) (z : ℂ) (hzero : Delta r = 0) (hres : L r = deriv Delta r) :
    mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) (deltaValue r z)) +
      mulComplexDist L hL (deltaValue r z) = 0 := by
  rw [mulComplexDist_derivative_deltaValue, mulComplexDist_deltaValue, hzero, hres, zero_mul]
  ext phi
  change -((TestFunction.lineDerivCLM ℝ (1:ℝ) phi) r • (0:ℂ)) -
    phi r • (deriv Delta r*z) + phi r • (deriv Delta r*z) = 0
  simp

/-- Exact C002 (35) coefficient, in the ordinary distribution space. -/
theorem complex_correction_repairs_second
    (B : ℝ → ℂ) (hB : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) B)
    (r : ℝ) (hBr : B r ≠ 0) (v₀ z₀ : CDist) (zH : ℂ)
    (hz : Distribution.lineDerivCLM (1:ℝ) z₀ = mulComplexDist B hB v₀+deltaValue r zH) :
    Distribution.lineDerivCLM (1:ℝ) z₀ =
      mulComplexDist B hB (v₀+deltaValue r (zH/B r)) := by
  rw [map_add, mulComplexDist_deltaValue, mul_div_cancel₀ zH hBr]
  exact hz

theorem complex_correction_preserves_first
    (Delta L A : ℝ → ℂ)
    (hDelta : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Delta)
    (hL : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) L)
    (hA : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) A)
    (r : ℝ) (z : ℂ) (hzero : Delta r = 0) (hres : L r = deriv Delta r)
    (v₀ z₀ : CDist)
    (hfirst : mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) v₀)+
      mulComplexDist L hL v₀ = mulComplexDist A hA z₀) :
    mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) (v₀+deltaValue r z))+
      mulComplexDist L hL (v₀+deltaValue r z) = mulComplexDist A hA z₀ := by
  simp only [map_add]
  have h := complex_resonant_delta_annihilated Delta L hDelta hL r z hzero hres
  calc
    _ = (mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) v₀)+mulComplexDist L hL v₀) +
      (mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) (deltaValue r z))+
        mulComplexDist L hL (deltaValue r z)) := by abel
    _ = _ := by rw [hfirst, h, add_zero]

end KN.ChargedRadial
