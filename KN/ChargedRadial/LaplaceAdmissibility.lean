import KN.ChargedRadial.TranslatedPower
import KN.Analysis.LaplaceInterface
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory TopologicalSpace
open scoped Distributions SchwartzMap
namespace KN.ChargedRadial
open KN.Analysis

/-- The actual tempered distribution associated with an L¹ function. -/
def integrableTempered (f : ℝ → ℂ) (hf : Integrable f) : TemperedDistribution ℝ ℂ :=
  Lp.toTemperedDistribution ((memLp_one_iff_integrable.2 hf).toLp f)

lemma integrableTempered_apply (f : ℝ → ℂ) (hf : Integrable f)
    (phi : SchwartzMap ℝ ℂ) :
    integrableTempered f hf phi = ∫ t : ℝ, phi t*f t := by
  rw [integrableTempered, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(memLp_one_iff_integrable.2 hf).coeFn_toLp] with t ht
  rw [ht]
  rfl

/-- Exponentially damped ordinary one-sided power, including its actual
zero extension rather than an unspecified representing tempered distribution. -/
def dampedPowerFunction (r beta : ℝ) (alpha : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Ioi r).indicator (fun t => (Real.exp (beta*t):ℂ)*(((t-r):ℂ)^alpha*f t))

lemma damped_regularPower_matches (r beta : ℝ) (alpha : ℂ)
    (ha : -1 < alpha.re) (f : ℝ → ℂ) (hf : Continuous f)
    (hi : Integrable (dampedPowerFunction r beta alpha f)) :
    DampedMatches (regularPowerAt r alpha f) beta
      (integrableTempered (dampedPowerFunction r beta alpha f) hi) := by
  intro phi
  rw [integrableTempered_apply, mulDist_apply, regularPowerAt_apply r alpha ha f hf]
  have he : (fun t : ℝ => testSchwartz phi t*dampedPowerFunction r beta alpha f t) =
      (Ioi r).indicator (fun t => (phi t*Real.exp (beta*t)) • (((t-r):ℂ)^alpha*f t)) := by
    ext t
    by_cases ht : t ∈ Ioi r
    · simp only [dampedPowerFunction, indicator_of_mem ht]
      change (phi t:ℂ)*((Real.exp (beta*t):ℂ)*(((t-r):ℂ)^alpha*f t)) = _
      simp only [Complex.real_smul, Complex.ofReal_mul]
      ring
    · simp [dampedPowerFunction, ht]
  rw [he, integral_indicator measurableSet_Ioi]
  rfl

lemma testSchwartz_derivative (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    SchwartzMap.derivCLM ℂ ℂ (testSchwartz phi) =
      testSchwartz (TestFunction.lineDerivCLM ℝ (1:ℝ) phi) := by
  ext t
  rw [SchwartzMap.derivCLM_apply]
  change deriv (fun x : ℝ => (phi x:ℂ)) t =
    (TestFunction.lineDerivCLM ℝ (1:ℝ) phi t:ℂ)
  rw [testFunction_deriv]
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
    (phi.contDiff.differentiable (by simp) t).hasDerivAt).deriv

lemma damping_test_derivative (beta : ℝ) (phi : 𝓓((⊤ : Opens ℝ), ℝ)) :
    TestFunction.lineDerivCLM ℝ (1:ℝ) (mulTest (damping beta) (damping_smooth beta) phi) =
      mulTest (damping beta) (damping_smooth beta) (TestFunction.lineDerivCLM ℝ (1:ℝ) phi)+
      beta • mulTest (damping beta) (damping_smooth beta) phi := by
  ext t
  rw [testFunction_deriv]
  change deriv (fun x => phi x*Real.exp (beta*x)) t = _
  have hp := (phi.contDiff.differentiable (by simp) t).hasDerivAt
  have he : HasDerivAt (fun x => Real.exp (beta*x)) (beta*Real.exp (beta*t)) t := by
    convert ((hasDerivAt_id t).const_mul beta).exp using 1 <;> simp [mul_comm]
  have hprod : HasDerivAt (fun x => phi x*Real.exp (beta*x))
      (deriv phi t*Real.exp (beta*t)+phi t*(beta*Real.exp (beta*t))) t := by
    convert hp.mul he using 1
  rw [hprod.deriv]
  change _ = (TestFunction.lineDerivCLM ℝ (1:ℝ) phi t)*Real.exp (beta*t)+
    beta*(phi t*Real.exp (beta*t))
  rw [testFunction_deriv]
  ring

/-- Damping and differentiating are related by the actual product rule on tests.
Thus admissibility of a finite-part derivative is not an extra interface. -/
theorem damped_derivative_matches (T : CDist) (beta : ℝ)
    (U : TemperedDistribution ℝ ℂ) (hU : DampedMatches T beta U) :
    DampedMatches (Distribution.lineDerivCLM (1:ℝ) T) beta
      (TemperedDistribution.derivCLM ℂ U - (beta:ℂ) • U) := by
  intro phi
  change U (-SchwartzMap.derivCLM ℂ ℂ (testSchwartz phi))-
    (beta:ℂ)*U (testSchwartz phi) =
      -(T (TestFunction.lineDerivCLM ℝ (1:ℝ)
        (mulTest (damping beta) (damping_smooth beta) phi)))
  rw [map_neg, testSchwartz_derivative, hU, hU, damping_test_derivative,
    map_add, map_smul]
  change -T (mulTest (damping beta) (damping_smooth beta)
    (TestFunction.lineDerivCLM ℝ (1:ℝ) phi))-
    (beta:ℂ)*T (mulTest (damping beta) (damping_smooth beta) phi) = _
  rw [Complex.real_smul]
  ring

lemma damped_smul_matches (T : CDist) (beta : ℝ)
    (U : TemperedDistribution ℝ ℂ) (hU : DampedMatches T beta U) (c : ℂ) :
    DampedMatches (c • T) beta (c • U) := by
  intro phi
  change c*U (testSchwartz phi) = c*T (mulTest (damping beta) (damping_smooth beta) phi)
  rw [hU]
  rfl

lemma damped_sub_matches (T S : CDist) (beta : ℝ)
    (U V : TemperedDistribution ℝ ℂ)
    (hU : DampedMatches T beta U) (hV : DampedMatches S beta V) :
    DampedMatches (T-S) beta (U-V) := by
  intro phi
  change U (testSchwartz phi)-V (testSchwartz phi) =
    T (mulTest (damping beta) (damping_smooth beta) phi)-
    S (mulTest (damping beta) (damping_smooth beta) phi)
  rw [hU,hV]
  rfl

/-- Concrete admissibility criterion for the canonical finite part: both
undifferentiated powers in (48a) are exponentially damped L¹ functions.
All tempered-distribution representatives and their derivative correction
are constructed here, not supplied as a specialized existence hypothesis. -/
theorem finitePartAt_laplaceAdmissible (r c : ℝ) (alpha : ℂ)
    (ha : -2 < alpha.re) (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hi : ∀ beta < c,
      Integrable (dampedPowerFunction r beta (alpha+1) f) ∧
      Integrable (dampedPowerFunction r beta (alpha+1) (deriv f))) :
    LaplaceAdmissible r c (finitePartAt r alpha f) := by
  refine ⟨finitePartAt_support r alpha ha f hf, ?_⟩
  intro beta hb
  have ha' : -1 < (alpha+1).re := by simpa using (show -1 < alpha.re+1 by linarith)
  obtain ⟨hi1,hi2⟩ := hi beta hb
  let U := integrableTempered (dampedPowerFunction r beta (alpha+1) f) hi1
  let V := integrableTempered (dampedPowerFunction r beta (alpha+1) (deriv f)) hi2
  have hU := damped_regularPower_matches r beta (alpha+1) ha' f hf.continuous hi1
  have hV := damped_regularPower_matches r beta (alpha+1) ha' (deriv f)
    (hf.continuous_deriv le_rfl) hi2
  exact ⟨(alpha+1)⁻¹ • (TemperedDistribution.derivCLM ℂ U-(beta:ℂ) • U-V),
    damped_smul_matches _ beta _
      (damped_sub_matches _ _ beta _ _ (damped_derivative_matches _ beta _ hU) hV) _⟩

/-- Local integrability plus a genuine exponential tail bound suffices for
all the L¹ hypotheses above. The singular power at the horizon is retained. -/
theorem dampedPower_integrable_of_exp_bound (r beta k : ℝ) (hk : 0 < k)
    (alpha : ℂ) (ha : -1 < alpha.re) (f : ℝ → ℂ) (hf : Continuous f)
    (ho : (fun t : ℝ => (Real.exp (beta*t):ℂ)*(((t-r):ℂ)^alpha*f t))
      =O[Filter.atTop] (fun t : ℝ => Real.exp (-k*t))) :
    Integrable (dampedPowerFunction r beta alpha f) := by
  have hc : Continuous (fun t : ℝ => (Real.exp (beta*t):ℂ)*f t) := by fun_prop
  have hlocal : LocallyIntegrable
      (fun t : ℝ => (Real.exp (beta*t):ℂ)*(((t-r):ℂ)^alpha*f t)) volume := by
    have h := (shifted_cpow_locallyIntegrable r alpha ha).mul_continuous hc
    convert h using 1
    ext t
    ring
  have hi := (hlocal.locallyIntegrableOn (Ici r)).integrableOn_of_isBigO_atTop ho
    (show IntegrableAtFilter (fun t : ℝ => Real.exp (-k*t)) Filter.atTop volume from
      ⟨Ioi r, Filter.Ioi_mem_atTop r, integrableOn_exp_mul_Ioi (by linarith : -k < 0) r⟩)
  exact (integrable_indicator_iff measurableSet_Ioi).2 (hi.mono_set Ioi_subset_Ici_self)

end KN.ChargedRadial
