import KN.ChargedRadial.CanonicalInterface
import KN.ChargedRadial.TranslatedResidual

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

/-- A concrete supported pair satisfying the two first-order equations. -/
structure SupportedPair (r : ℝ) (Delta L A B : ℝ → ℂ)
    (hDelta : Smooth Delta) (hL : Smooth L) (hA : Smooth A) (hB : Smooth B) where
  v : CDist
  z : CDist
  v_support : Distribution.dsupport v ⊆ Ici r
  z_support : Distribution.dsupport z ⊆ Ici r
  first : mulComplexDist Delta hDelta (Distribution.lineDerivCLM (1:ℝ) v)+
    mulComplexDist L hL v = mulComplexDist A hA z
  second : Distribution.lineDerivCLM (1:ℝ) z = mulComplexDist B hB v

lemma regularPowerAt_support (r : ℝ) (alpha : ℂ) (ha : -1 < alpha.re)
    (g : ℝ → ℂ) (hg : Continuous g) :
    Distribution.dsupport (regularPowerAt r alpha g) ⊆ Ici r := by
  intro x hx
  apply (Distribution.mem_dsupport_iff x).1 hx (Ici r) ?_ isClosed_Ici
  rw [compl_Ici]
  exact regularPowerAt_vanishes_negative r alpha ha g hg

/-- Supported continuation of a power-factorized Fuchsian pair. All specialized
ODE cancellations are proved from the original pointwise equations; only the
general canonical-power identities are imported from the published interface. -/
theorem supported_pair_of_power_ODE
    (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (f g d L A B : ℝ → ℂ)
    (hf : Smooth f) (hg : Smooth g) (hd : Smooth d)
    (hL : Smooth L) (hA : Smooth A) (hB : Smooth B)
    (htd : Smooth (fun t : ℝ => ((t-r):ℂ)*d t))
    (hfirst : ∀ (t : ℝ), t > r →
      (((t-r : ℝ):ℂ)*d t)*deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^alpha*f x) t+
        L t*(((t-r : ℝ):ℂ)^alpha*f t) = A t*(((t-r : ℝ):ℂ)^(alpha+1)*g t))
    (hsecond : ∀ (t : ℝ), t > r →
      deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^(alpha+1)*g x) t =
        B t*(((t-r : ℝ):ℂ)^alpha*f t)) :
    ∃ pair : SupportedPair r (fun t : ℝ => ((t-r):ℂ)*d t) L A B htd hL hA hB,
      pair.v = finitePartAt r alpha f ∧ pair.z = regularPowerAt r (alpha+1) g := by
  obtain ⟨hres1,hres2⟩ := translated_power_pair_residuals r alpha f g d L A B
    (hf.differentiable (by simp)) (hg.differentiable (by simp)) hfirst hsecond
  have heq := translated_canonical_pair_homogeneous External.canonical_power_calculus
    r alpha ha hne f g d L A B hf hg hd hL hA hB htd
    (by simpa only [Complex.ofReal_sub] using hres1)
    (by simpa only [Complex.ofReal_sub] using hres2)
  have ha' : -1 < (alpha+1).re := by simpa using (show -1 < alpha.re+1 by linarith)
  exact ⟨⟨finitePartAt r alpha f, regularPowerAt r (alpha+1) g,
    finitePartAt_support r alpha ha f (hf.of_le (by simp)),
    regularPowerAt_support r (alpha+1) ha' g hg.continuous, heq.1, heq.2⟩, rfl, rfl⟩

/-- Local equality on the exterior transports the ordinary derivatives, so the
canonical supported pair applies to the original radial functions themselves. -/
theorem supported_pair_of_factorized_functions
    (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re) (hne : alpha ≠ -1)
    (v z f g d L A B : ℝ → ℂ)
    (hf : Smooth f) (hg : Smooth g) (hd : Smooth d)
    (hL : Smooth L) (hA : Smooth A) (hB : Smooth B)
    (htd : Smooth (fun t : ℝ => ((t-r):ℂ)*d t))
    (hv : ∀ t > r, v t = ((t-r : ℝ):ℂ)^alpha*f t)
    (hz : ∀ t > r, z t = ((t-r : ℝ):ℂ)^(alpha+1)*g t)
    (hfirst : ∀ t > r, (((t-r : ℝ):ℂ)*d t)*deriv v t+L t*v t = A t*z t)
    (hsecond : ∀ t > r, deriv z t = B t*v t) :
    ∃ pair : SupportedPair r (fun t : ℝ => ((t-r):ℂ)*d t) L A B htd hL hA hB,
      pair.v = finitePartAt r alpha f ∧ pair.z = regularPowerAt r (alpha+1) g := by
  have hdv (t : ℝ) (ht : r < t) :
      deriv v t = deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^alpha*f x) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact hv x hx
  have hdz (t : ℝ) (ht : r < t) :
      deriv z t = deriv (fun x : ℝ => ((x-r : ℝ):ℂ)^(alpha+1)*g x) t := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with x hx
    exact hz x hx
  apply supported_pair_of_power_ODE r alpha ha hne f g d L A B hf hg hd hL hA hB htd
  · intro t ht
    simpa only [hdv t ht, hv t ht, hz t ht] using hfirst t ht
  · intro t ht
    simpa only [hdz t ht, hv t ht] using hsecond t ht

end KN.ChargedRadial
