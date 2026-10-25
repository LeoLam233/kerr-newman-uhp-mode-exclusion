import KN.ChargedRadial.PowerCalculus
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.Calculus.Deriv.Support

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions
namespace KN.ChargedRadial

lemma shifted_cpow_locallyIntegrable (r : ℝ) (alpha : ℂ) (ha : -1 < alpha.re) :
    LocallyIntegrable (fun t : ℝ => ((t-r):ℂ)^alpha) volume := by
  intro x
  refine ⟨Ioo (x-1) (x+1), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  have hi := (intervalIntegral.intervalIntegrable_cpow' ha
    (a := x-1-r) (b := x+1-r)).comp_sub_right r
  have hj : IntervalIntegrable (fun t : ℝ => ((t-r):ℂ)^alpha) volume (x-1) (x+1) := by
    simpa only [sub_add_cancel, Complex.ofReal_sub] using hi
  exact hj.1.mono_set Ioo_subset_Ioc_self

/-- The locally integrable positive power, with a smooth coefficient, as an actual distribution. -/
def regularPowerAt (r : ℝ) (alpha : ℂ) (f : ℝ → ℂ) : CDist :=
  Distribution.ofFun (⊤ : Opens ℝ) (fun t => ((t-r):ℂ)^alpha*f t)
    (volume.restrict (Ioi r)) ⊤

lemma regularPowerAt_apply (r : ℝ) (alpha : ℂ) (ha : -1 < alpha.re)
    (f : ℝ → ℂ) (hf : Continuous f) (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    regularPowerAt r alpha f phi = ∫ t in Ioi r, phi t • (((t-r):ℂ)^alpha*f t) := by
  exact Distribution.ofFun_apply
    ((((shifted_cpow_locallyIntegrable r alpha ha).mul_continuous hf).mono_measure
      Measure.restrict_le_self).locallyIntegrableOn _)

/-- C002 (48a), taken as a concrete construction rather than an unnamed extension.
For Re α > -2 and α ≠ -1 both undifferentiated terms are locally integrable.
The exceptional α=-1 branch must use the separately proved delta correction. -/
def finitePartAt (r : ℝ) (alpha : ℂ) (f : ℝ → ℂ) : CDist :=
  (alpha+1)⁻¹ • (Distribution.lineDerivCLM (1:ℝ) (regularPowerAt r (alpha+1) f) -
    regularPowerAt r (alpha+1) (deriv f))

lemma finitePartAt_apply (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    finitePartAt r alpha f phi = (alpha+1)⁻¹ *
      (-(∫ t in Ioi r, deriv phi t • (((t-r):ℂ)^(alpha+1)*f t)) -
        ∫ t in Ioi r, phi t • (((t-r):ℂ)^(alpha+1)*deriv f t)) := by
  have ha' : -1 < (alpha+1).re := by simpa using (show -1 < alpha.re+1 by linarith)
  change (alpha+1)⁻¹ *
    (-(regularPowerAt r (alpha+1) f (TestFunction.lineDerivCLM ℝ (1:ℝ) phi)) -
      regularPowerAt r (alpha+1) (deriv f) phi) = _
  rw [regularPowerAt_apply r _ ha' _ hf.continuous,
    regularPowerAt_apply r _ ha' _ (hf.continuous_deriv le_rfl)]
  simp_rw [testFunction_deriv]

lemma regularPowerAt_vanishes_negative (r : ℝ) (alpha : ℂ) (ha : -1 < alpha.re)
    (f : ℝ → ℂ) (hf : Continuous f) :
    Distribution.IsVanishingOn (regularPowerAt r alpha f) (Iio r) := by
  intro phi hphi
  rw [regularPowerAt_apply r _ ha _ hf]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have hz : phi t = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hs
    have hh := hphi hs
    exact (not_lt_of_ge (le_of_lt (show r < t from ht))) (show t < r from hh))
  rw [hz, zero_smul]

/-- The concrete finite-part construction is supported on the closed positive half-line. -/
theorem finitePartAt_support (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re)
    (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f) :
    Distribution.dsupport (finitePartAt r alpha f) ⊆ Ici r := by
  intro x hx
  apply (Distribution.mem_dsupport_iff x).1 hx (Ici r) ?_ isClosed_Ici
  rw [compl_Ici]
  intro phi hphi
  rw [finitePartAt_apply r _ ha _ hf]
  have hz : ∀ t ∈ Ioi r, phi t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (by
      intro hs
      exact (not_lt_of_ge (le_of_lt (show r < t from ht))) (show t < r from hphi hs))
  have hdz : ∀ t ∈ Ioi r, deriv phi t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (by
      intro hs
      exact (not_lt_of_ge (le_of_lt (show r < t from ht))) (show t < r from hphi (tsupport_deriv_subset hs)))
  have hi1 : (∫ t in Ioi r, deriv phi t • (((t-r):ℂ)^(alpha+1)*f t)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun t ht => by rw [hdz t ht, zero_smul])
  have hi2 : (∫ t in Ioi r, phi t • (((t-r):ℂ)^(alpha+1)*deriv f t)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun t ht => by rw [hz t ht, zero_smul])
  rw [hi1, hi2]
  simp

lemma regularPowerAt_add (r : ℝ) (alpha : ℂ) (ha : -1 < alpha.re)
    (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g) :
    regularPowerAt r alpha (f+g) = regularPowerAt r alpha f+regularPowerAt r alpha g := by
  have hfl := (((shifted_cpow_locallyIntegrable r alpha ha).mul_continuous hf).mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioi r))).locallyIntegrableOn univ
  have hgl := (((shifted_cpow_locallyIntegrable r alpha ha).mul_continuous hg).mono_measure
    (Measure.restrict_le_self (μ := volume) (s := Ioi r))).locallyIntegrableOn univ
  have he : (fun t : ℝ => ((t-r):ℂ)^alpha*(f+g) t) =
      (fun t : ℝ => ((t-r):ℂ)^alpha*f t)+(fun t : ℝ => ((t-r):ℂ)^alpha*g t) := by ext t; simp [mul_add]
  unfold regularPowerAt
  rw [he, Distribution.ofFun_add hfl hgl]

lemma finitePartAt_add (r : ℝ) (alpha : ℂ) (ha : -2 < alpha.re)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    finitePartAt r alpha (f+g) = finitePartAt r alpha f+finitePartAt r alpha g := by
  have ha' : -1 < (alpha+1).re := by simpa using (show -1 < alpha.re+1 by linarith)
  have hd : deriv (f+g) = deriv f+deriv g := by
    ext t
    exact deriv_add (hf.differentiable one_ne_zero t) (hg.differentiable one_ne_zero t)
  unfold finitePartAt
  rw [hd, regularPowerAt_add r _ ha' _ _ hf.continuous hg.continuous,
    regularPowerAt_add r _ ha' _ _ (hf.continuous_deriv le_rfl) (hg.continuous_deriv le_rfl), map_add]
  module

lemma regularPowerAt_eq_on_positive (r : ℝ) (alpha : ℂ) (f g : ℝ → ℂ)
    (he : EqOn f g (Ioi r)) : regularPowerAt r alpha f = regularPowerAt r alpha g := by
  apply Distribution.ofFun_congr_ae
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply (ae_restrict_iff' measurableSet_Ioi).2
  filter_upwards [] with t ht
  rw [he ht]

/-- Locality of the actual finite-part formula: only the values on the open
positive half-line contribute. -/
theorem finitePartAt_eq_on_positive (r : ℝ) (alpha : ℂ) (f g : ℝ → ℂ)
    (he : EqOn f g (Ioi r)) : finitePartAt r alpha f = finitePartAt r alpha g := by
  have hd : EqOn (deriv f) (deriv g) (Ioi r) := by
    intro t ht
    have hevent : f =ᶠ[nhds t] g :=
      Filter.Eventually.mono (isOpen_Ioi.mem_nhds ht) (fun x hx => he hx)
    exact hevent.deriv_eq
  unfold finitePartAt
  rw [regularPowerAt_eq_on_positive r _ _ _ he, regularPowerAt_eq_on_positive r _ _ _ hd]

end KN.ChargedRadial
