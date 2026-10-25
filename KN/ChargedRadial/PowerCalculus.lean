import KN.ChargedRadial.FinitePart

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

abbrev Smooth (f : ℝ → ℂ) := ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f

/-- General canonical one-sided-power calculus, independent of Kerr–Newman.
Source: Gel'fand–Shilov, Generalized Functions, Vol. I, Chapter I §3
(analytic continuation of x₊^λ and multiplication/differentiation).
This interface concerns the concrete finite-part integral above, not an
unspecified extension or a differential-equation solution. -/
structure CanonicalPowerCalculus : Prop where
  mul (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f g : ℝ → ℂ) (hf : Smooth f) (hg : Smooth g) :
    mulComplexDist g hg (finitePart alpha f) = finitePart alpha (fun t => g t*f t)
  euler (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f d : ℝ → ℂ) (hf : Smooth f) (hd : Smooth d)
    (htd : Smooth (fun t : ℝ => (t:ℂ)*d t)) :
    mulComplexDist (fun t : ℝ => (t:ℂ)*d t) htd
      (Distribution.lineDerivCLM (1:ℝ) (finitePart alpha f)) =
      finitePart alpha (fun t : ℝ => d t*(alpha*f t+(t:ℂ)*deriv f t))
  derivative (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (g : ℝ → ℂ) (hg : Smooth g) :
    Distribution.lineDerivCLM (1:ℝ) (regularPower (alpha+1) g) =
      finitePart alpha (fun t : ℝ => (alpha+1)*g t+(t:ℂ)*deriv g t)
  raise (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (g : ℝ → ℂ) (hg : Smooth g) :
    regularPower (alpha+1) g = finitePart alpha (fun t : ℝ => (t:ℂ)*g t)

/-- The smooth-factor residual vanishes as a canonical distribution whenever
it vanishes on the open positive half-line. No boundary value is presumed. -/
lemma finitePart_eq_zero_of_positive (alpha : ℂ) (f : ℝ → ℂ)
    (hf : ∀ t > 0, f t = 0) : finitePart alpha f = 0 := by
  rw [finitePart_eq_on_positive alpha f 0 (fun t ht => hf t ht)]
  simp only [finitePart, regularPower, Pi.zero_apply, mul_zero, deriv_zero]
  change (alpha+1)⁻¹ • (Distribution.lineDerivCLM (1:ℝ)
    (Distribution.ofFun ⊤ (0 : ℝ → ℂ) (volume.restrict (Ioi 0)) ⊤) -
    Distribution.ofFun ⊤ (0 : ℝ → ℂ) (volume.restrict (Ioi 0)) ⊤) = 0
  rw [Distribution.ofFun_zero]
  simp

/-- The first Fuchsian equation extends homogeneously by canonical powers.
The residual hypotheses are pointwise smooth-factor identities, not assumed
distributional equations; the canonical-power interface is wholly general. -/
theorem canonical_pair_homogeneous (pc : CanonicalPowerCalculus)
    (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f g d L A B : ℝ → ℂ)
    (hf : Smooth f) (hg : Smooth g) (hd : Smooth d)
    (hL : Smooth L) (hA : Smooth A) (hB : Smooth B)
    (htd : Smooth (fun t : ℝ => (t:ℂ)*d t))
    (hfirst : ∀ t > 0, d t*(alpha*f t+(t:ℂ)*deriv f t)+L t*f t = A t*((t:ℂ)*g t))
    (hsecond : ∀ t > 0, (alpha+1)*g t+(t:ℂ)*deriv g t = B t*f t) :
    (mulComplexDist (fun t : ℝ => (t:ℂ)*d t) htd
      (Distribution.lineDerivCLM (1:ℝ) (finitePart alpha f)) +
      mulComplexDist L hL (finitePart alpha f) =
      mulComplexDist A hA (regularPower (alpha+1) g)) ∧
    (Distribution.lineDerivCLM (1:ℝ) (regularPower (alpha+1) g) =
      mulComplexDist B hB (finitePart alpha f)) := by
  have htg : Smooth (fun t : ℝ => (t:ℂ)*g t) := by
    exact Complex.ofRealCLM.contDiff.mul hg
  constructor
  · rw [pc.euler alpha ha hne f d hf hd htd, pc.mul alpha ha hne f L hf hL,
      pc.raise alpha ha hne g hg, pc.mul alpha ha hne _ A htg hA]
    have hdf : ContDiff ℝ 1 (fun t : ℝ => d t*(alpha*f t+(t:ℂ)*deriv f t)) := by
      have hfd : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) := hf.deriv'
      exact (hd.mul ((contDiff_const.mul hf).add
        (Complex.ofRealCLM.contDiff.mul hfd))).of_le (by simp)
    have hLf : ContDiff ℝ 1 (fun t => L t*f t) := (hL.mul hf).of_le (by simp)
    rw [← finitePart_add alpha ha _ _ hdf hLf]
    apply finitePart_eq_on_positive
    exact fun t ht => hfirst t ht
  · rw [pc.derivative alpha ha hne g hg, pc.mul alpha ha hne f B hf hB]
    exact finitePart_eq_on_positive _ _ _ (fun t ht => hsecond t ht)

end KN.ChargedRadial
