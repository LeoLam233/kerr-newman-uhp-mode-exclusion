import KN.ChargedRadial.TranslatedPower

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

/-- General canonical one-sided-power calculus, independent of Kerr–Newman.
Source: Gel'fand–Shilov, Generalized Functions, Vol. I, Chapter I §3
(analytic continuation of x₊^λ and multiplication/differentiation).
This interface concerns the concrete finite-part integral above, not an
unspecified extension or a differential-equation solution. -/
structure TranslatedCanonicalPowerCalculus : Prop where
  agrees (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f : ℝ → ℂ) (hf : Smooth f) (phi : 𝓓((⊤ : Opens ℝ), ℝ))
    (hphi : tsupport phi ⊆ Ioi r) :
    finitePartAt r alpha f phi =
      ∫ t in Ioi r, phi t • (((t-r):ℂ)^alpha*f t)
  mul (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f g : ℝ → ℂ) (hf : Smooth f) (hg : Smooth g) :
    mulComplexDist g hg (finitePartAt r alpha f) = finitePartAt r alpha (fun t => g t*f t)
  euler (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f d : ℝ → ℂ) (hf : Smooth f) (hd : Smooth d)
    (htd : Smooth (fun t : ℝ => ((t-r):ℂ)*d t)) :
    mulComplexDist (fun t : ℝ => ((t-r):ℂ)*d t) htd
      (Distribution.lineDerivCLM (1:ℝ) (finitePartAt r alpha f)) =
      finitePartAt r alpha (fun t : ℝ => d t*(alpha*f t+((t-r):ℂ)*deriv f t))
  derivative (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (g : ℝ → ℂ) (hg : Smooth g) :
    Distribution.lineDerivCLM (1:ℝ) (regularPowerAt r (alpha+1) g) =
      finitePartAt r alpha (fun t : ℝ => (alpha+1)*g t+((t-r):ℂ)*deriv g t)
  raise (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (g : ℝ → ℂ) (hg : Smooth g) :
    regularPowerAt r (alpha+1) g = finitePartAt r alpha (fun t : ℝ => ((t-r):ℂ)*g t)

/-- The smooth-factor residual vanishes as a canonical distribution whenever
it vanishes on the open positive half-line. No boundary value is presumed. -/
lemma finitePartAt_eq_zero_of_positive (r : ℝ) (alpha : ℂ) (f : ℝ → ℂ)
    (hf : ∀ t > r, f t = 0) : finitePartAt r alpha f = 0 := by
  rw [finitePartAt_eq_on_positive r alpha f 0 (fun t ht => hf t ht)]
  simp only [finitePartAt, regularPowerAt, Pi.zero_apply, mul_zero, deriv_zero]
  change (alpha+1)⁻¹ • (Distribution.lineDerivCLM (1:ℝ)
    (Distribution.ofFun ⊤ (0 : ℝ → ℂ) (volume.restrict (Ioi r)) ⊤) -
    Distribution.ofFun ⊤ (0 : ℝ → ℂ) (volume.restrict (Ioi r)) ⊤) = 0
  rw [Distribution.ofFun_zero]
  simp

/-- The first Fuchsian equation extends homogeneously by canonical powers.
The residual hypotheses are pointwise smooth-factor identities, not assumed
distributional equations; the canonical-power interface is wholly general. -/
theorem translated_canonical_pair_homogeneous (pc : TranslatedCanonicalPowerCalculus)
    (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f g d L A B : ℝ → ℂ)
    (hf : Smooth f) (hg : Smooth g) (hd : Smooth d)
    (hL : Smooth L) (hA : Smooth A) (hB : Smooth B)
    (htd : Smooth (fun t : ℝ => ((t-r):ℂ)*d t))
    (hfirst : ∀ t > r, d t*(alpha*f t+((t-r):ℂ)*deriv f t)+L t*f t = A t*(((t-r):ℂ)*g t))
    (hsecond : ∀ t > r, (alpha+1)*g t+((t-r):ℂ)*deriv g t = B t*f t) :
    (mulComplexDist (fun t : ℝ => ((t-r):ℂ)*d t) htd
      (Distribution.lineDerivCLM (1:ℝ) (finitePartAt r alpha f)) +
      mulComplexDist L hL (finitePartAt r alpha f) =
      mulComplexDist A hA (regularPowerAt r (alpha+1) g)) ∧
    (Distribution.lineDerivCLM (1:ℝ) (regularPowerAt r (alpha+1) g) =
      mulComplexDist B hB (finitePartAt r alpha f)) := by
  have htg : Smooth (fun t : ℝ => ((t-r):ℂ)*g t) := by
    exact ((Complex.ofRealCLM.contDiff).sub contDiff_const).mul hg
  constructor
  · rw [pc.euler r alpha ha hne f d hf hd htd, pc.mul r alpha ha hne f L hf hL,
      pc.raise r alpha ha hne g hg, pc.mul r alpha ha hne _ A htg hA]
    have hdf : ContDiff ℝ 1 (fun t : ℝ => d t*(alpha*f t+((t-r):ℂ)*deriv f t)) := by
      have hfd : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) := hf.deriv'
      exact (hd.mul ((contDiff_const.mul hf).add
        (((Complex.ofRealCLM.contDiff).sub contDiff_const).mul hfd))).of_le (by simp)
    have hLf : ContDiff ℝ 1 (fun t => L t*f t) := (hL.mul hf).of_le (by simp)
    rw [← finitePartAt_add r alpha ha _ _ hdf hLf]
    apply finitePartAt_eq_on_positive
    exact fun t ht => hfirst t ht
  · rw [pc.derivative r alpha ha hne g hg, pc.mul r alpha ha hne f B hf hB]
    exact finitePartAt_eq_on_positive r _ _ _ (fun t ht => hsecond t ht)

end KN.ChargedRadial
