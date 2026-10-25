import KN.ChargedRadial.DistributionMultiplication
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

lemma cpow_locallyIntegrable (alpha : ℂ) (ha : -1 < alpha.re) :
    LocallyIntegrable (fun t : ℝ => (t:ℂ)^alpha) volume := by
  intro x
  refine ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegral.intervalIntegrable_cpow' ha (a := x-1) (b := x+1)).1.mono_set
    Ioo_subset_Ioc_self

/-- The locally integrable positive power, with a smooth coefficient, as an actual distribution. -/
def regularPower (alpha : ℂ) (f : ℝ → ℂ) : CDist :=
  Distribution.ofFun (⊤ : Opens ℝ) (fun t => (t:ℂ)^alpha*f t)
    (volume.restrict (Ioi 0)) ⊤

lemma regularPower_apply (alpha : ℂ) (ha : -1 < alpha.re)
    (f : ℝ → ℂ) (hf : Continuous f) (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    regularPower alpha f phi = ∫ t in Ioi (0:ℝ), phi t • ((t:ℂ)^alpha*f t) := by
  exact Distribution.ofFun_apply
    ((((cpow_locallyIntegrable alpha ha).mul_continuous hf).mono_measure
      Measure.restrict_le_self).locallyIntegrableOn _)

/-- C002 (48a), taken as a concrete construction rather than an unnamed extension.
For Re α > -2 and α ≠ -1 both undifferentiated terms are locally integrable.
The exceptional α=-1 branch must use the separately proved delta correction. -/
def finitePart (alpha : ℂ) (f : ℝ → ℂ) : CDist :=
  (alpha+1)⁻¹ • (Distribution.lineDerivCLM (1:ℝ) (regularPower (alpha+1) f) -
    regularPower (alpha+1) (deriv f))

lemma finitePart_apply (alpha : ℂ) (ha : -2 < alpha.re)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    finitePart alpha f phi = (alpha+1)⁻¹ *
      (-(∫ t in Ioi (0:ℝ), deriv phi t • ((t:ℂ)^(alpha+1)*f t)) -
        ∫ t in Ioi (0:ℝ), phi t • ((t:ℂ)^(alpha+1)*deriv f t)) := by
  have ha' : -1 < (alpha+1).re := by simpa using (show -1 < alpha.re+1 by linarith)
  change (alpha+1)⁻¹ *
    (-(regularPower (alpha+1) f (TestFunction.lineDerivCLM ℝ (1:ℝ) phi)) -
      regularPower (alpha+1) (deriv f) phi) = _
  rw [regularPower_apply _ ha' _ hf.continuous,
    regularPower_apply _ ha' _ (hf.continuous_deriv le_rfl)]
  simp_rw [testFunction_deriv]

lemma regularPower_vanishes_negative (alpha : ℂ) (ha : -1 < alpha.re)
    (f : ℝ → ℂ) (hf : Continuous f) :
    Distribution.IsVanishingOn (regularPower alpha f) (Iio (0:ℝ)) := by
  intro phi hphi
  rw [regularPower_apply _ ha _ hf]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have hz : phi t = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hs
    have hh := hphi hs
    exact (not_lt_of_ge (le_of_lt (show 0 < t from ht))) (show t < 0 from hh))
  rw [hz, zero_smul]

/-- The concrete finite-part construction is supported on the closed positive half-line. -/
theorem finitePart_support (alpha : ℂ) (ha : -2 < alpha.re)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    Distribution.dsupport (finitePart alpha f) ⊆ Ici (0:ℝ) := by
  intro x hx
  apply (Distribution.mem_dsupport_iff x).1 hx (Ici 0) ?_ isClosed_Ici
  rw [compl_Ici]
  intro phi hphi
  rw [finitePart_apply _ ha _ hf]
  have hz : ∀ t ∈ Ioi (0:ℝ), phi t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (by
      intro hs
      exact (not_lt_of_ge (le_of_lt (show 0 < t from ht))) (show t < 0 from hphi hs))
  have hdz : ∀ t ∈ Ioi (0:ℝ), deriv phi t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (by
      intro hs
      exact (not_lt_of_ge (le_of_lt (show 0 < t from ht))) (show t < 0 from hphi (tsupport_deriv_subset hs)))
  have hi1 : (∫ t in Ioi (0:ℝ), deriv phi t • ((t:ℂ)^(alpha+1)*f t)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun t ht => by rw [hdz t ht, zero_smul])
  have hi2 : (∫ t in Ioi (0:ℝ), phi t • ((t:ℂ)^(alpha+1)*deriv f t)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun t ht => by rw [hz t ht, zero_smul])
  rw [hi1, hi2]
  simp

lemma regularPower_add (alpha : ℂ) (ha : -1 < alpha.re)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    regularPower alpha (f+g) = regularPower alpha f+regularPower alpha g := by
  have hfl := (((cpow_locallyIntegrable alpha ha).mul_continuous hf).mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioi (0:ℝ)))).locallyIntegrableOn univ
  have hgl := (((cpow_locallyIntegrable alpha ha).mul_continuous hg).mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioi (0:ℝ)))).locallyIntegrableOn univ
  have he : (fun t : ℝ => (t:ℂ)^alpha*(f+g) t) =
      (fun t : ℝ => (t:ℂ)^alpha*f t)+(fun t : ℝ => (t:ℂ)^alpha*g t) := by ext t; simp [mul_add]
  unfold regularPower
  rw [he, Distribution.ofFun_add hfl hgl]

lemma finitePart_add (alpha : ℂ) (ha : -2 < alpha.re)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    finitePart alpha (f+g) = finitePart alpha f+finitePart alpha g := by
  have ha' : -1 < (alpha+1).re := by simpa using (show -1 < alpha.re+1 by linarith)
  have hd : deriv (f+g) = deriv f+deriv g := by
    ext t
    exact deriv_add (hf.differentiable one_ne_zero t) (hg.differentiable one_ne_zero t)
  unfold finitePart
  rw [hd, regularPower_add _ ha' _ _ hf.continuous hg.continuous,
    regularPower_add _ ha' _ _ (hf.continuous_deriv le_rfl) (hg.continuous_deriv le_rfl), map_add]
  module

lemma regularPower_eq_on_positive (alpha : ℂ) (f g : ℝ → ℂ)
    (he : EqOn f g (Ioi (0:ℝ))) : regularPower alpha f = regularPower alpha g := by
  apply Distribution.ofFun_congr_ae
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply (ae_restrict_iff' measurableSet_Ioi).2
  filter_upwards [] with t ht
  rw [he ht]

/-- Locality of the actual finite-part formula: only the values on the open
positive half-line contribute. -/
theorem finitePart_eq_on_positive (alpha : ℂ) (f g : ℝ → ℂ)
    (he : EqOn f g (Ioi (0:ℝ))) : finitePart alpha f = finitePart alpha g := by
  have hd : EqOn (deriv f) (deriv g) (Ioi (0:ℝ)) := by
    intro t ht
    have hevent : f =ᶠ[nhds t] g :=
      Filter.Eventually.mono (isOpen_Ioi.mem_nhds ht) (fun x hx => he hx)
    exact hevent.deriv_eq
  unfold finitePart
  rw [regularPower_eq_on_positive _ _ _ he, regularPower_eq_on_positive _ _ _ hd]

end KN.ChargedRadial
