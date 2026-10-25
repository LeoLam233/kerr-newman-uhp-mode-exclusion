import KN.Energy.Coercivity
import KN.Energy.Vanishing
import KN.Energy.Weights
import KN.ChargedRadial.RegularDistribution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Distributions Topology
namespace EnergyControls
open KN.Energy KN.ChargedRadial

/-- Removing UHP permits strictly positive mass energy satisfying the exact equation. -/
example : -(1:ℂ)-0+(1:ℂ)*0+(1:ℂ)^2*1=0 ∧ (1:ℝ)≠0 := by norm_num

/-- Nonnegative k-energy is indispensable, even at omega=i. -/
example : -(0:ℂ)-(-1)+Complex.I*0+Complex.I^2*1=0 ∧ (1:ℝ)≠0 := by
  norm_num [Complex.I_sq]

/-- The physical negative-axis domain cannot be replaced by x<0. -/
example : Pplus 0 (-1)<0 ∧ Pminus 0 (-1)<0 := by norm_num [Pplus,Pminus]

/-- q≤1 cannot simply be discarded from the coercive B bound. -/
example : (3:ℝ)^2*(1^2+2*0^2/(3-2))+2*1^2*3-1^2*100<0 := by norm_num

/-- Strict mass weight is essential: the zero-density constant solution is nonzero. -/
example :
    (∀x : ℝ, HasDerivAt (fun _ : ℝ => (1:ℂ)) 0 x) ∧
    (∀x : ℝ, HasDerivAt (fun _ : ℝ => (0:ℂ))
      ((1:ℂ)*(0-Complex.I*0-Complex.I^2*0)*1) x) ∧
    (∀x : ℝ, density Complex.I (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0)
      (fun _ => 1) (fun _ => 0) x=0) ∧
    (∀x : ℝ, current Complex.I (fun _ => 1) (fun _ => 1) (fun _ => 0) x=0) ∧
    (1:ℂ)≠0 := by
  refine ⟨fun x => hasDerivAt_const x 1,?_,?_,?_,one_ne_zero⟩
  · intro x; simpa using hasDerivAt_const x (0:ℂ)
  · intro x; simp [density]
  · intro x; simp [current]

/-- A real growing exponential solves the UHP divergence equation and decays at
minus infinity, but carries nonzero finite-endpoint flux. -/
def expField (x : ℝ) : ℂ := Real.exp x
lemma expField_deriv (x : ℝ) : HasDerivAt expField (expField x) x := (Real.hasDerivAt_exp x).ofReal_comp
lemma expField_divergence (x : ℝ) :
    HasDerivAt (fun y => (1:ℂ)*expField y)
      ((1:ℂ)*(0-Complex.I*0-Complex.I^2*1)*expField x) x := by
  simpa [Complex.I_sq] using expField_deriv x
lemma expField_current (x : ℝ) :
    current Complex.I (fun _ => 1) expField expField x=-(Real.exp x)^2 := by
  simp [current,expField,Complex.mul_im,Complex.mul_re,pow_two,Complex.exp_re]
lemma expField_density (x : ℝ) :
    density Complex.I (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1)
      expField expField x=2*Real.exp (2*x) := by
  simp only [density,expField,Complex.normSq_I,Complex.normSq_ofReal,one_mul,mul_zero,zero_mul,add_zero]
  rw [show 2*x=x+x by ring,Real.exp_add]
  ring
lemma expField_density_integrable :
    IntegrableOn (density Complex.I (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1)
      expField expField) (Iio (0:ℝ)) := by
  have he : density Complex.I (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 1)
      expField expField=(fun x => 2*Real.exp (2*x)) := funext expField_density
  rw [he]
  exact ((integrableOn_exp_mul_Iic (a:=2) (by norm_num) 0).mono_set Iio_subset_Iic_self).const_mul 2
lemma expField_current_atBot :
    Tendsto (current Complex.I (fun _ => 1) expField expField) atBot (𝓝 0) := by
  have he : current Complex.I (fun _ => 1) expField expField=(fun x => -(Real.exp x)^2) :=
    funext expField_current
  rw [he]
  simpa using (Real.tendsto_exp_atBot.pow 2).neg
lemma expField_zero_endpoint_flux_false :
    ¬ Tendsto (current Complex.I (fun _ => 1) expField expField) (𝓝[<] (0:ℝ)) (𝓝 0) := by
  have hc : Continuous (current Complex.I (fun _ => 1) expField expField) := by
    have he : current Complex.I (fun _ => 1) expField expField=(fun x => -(Real.exp x)^2) :=
      funext expField_current
    rw [he]
    fun_prop
  intro h
  have he := tendsto_nhds_unique h (hc.continuousAt.tendsto.mono_left inf_le_left)
  simp [expField_current] at he

/-- Concrete compactly-supported test function detecting the omitted delta. -/
def detectorBump : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def detector : 𝓓((⊤ : Opens ℝ), ℝ) :=
  ⟨detectorBump,detectorBump.contDiff,detectorBump.hasCompactSupport,by simp⟩
lemma detector_zero : detector 0=1 := by
  exact detectorBump.one_of_mem_closedBall (by simp [detectorBump,Metric.mem_closedBall])
lemma unit_delta_ne_zero : deltaValue 0 1 ≠ 0 := by
  intro h
  have hh := congrArg (fun T : CDist => T detector) h
  change detector 0 • (1:ℂ)=0 at hh
  rw [detector_zero,one_smul] at hh
  exact one_ne_zero hh
lemma constant_zeroExtension_source :
    Distribution.lineDerivCLM (1:ℝ) (zeroExtension 0 (fun _ => (1:ℂ)))=deltaValue 0 1 := by
  have h := derivative_zeroExtension 0 (fun _ => (1:ℂ)) contDiff_const
  have hz : zeroExtension 0 (fun _ : ℝ => (0:ℂ))=0 := by
    ext phi
    rw [zeroExtension_apply 0 (fun _ => (0:ℂ)) continuous_const]
    simp
  have hd : deriv (fun _ : ℝ => (1:ℂ))=(fun _ => 0) := funext (fun r => deriv_const r 1)
  rw [hd,hz,zero_add] at h
  exact h
lemma omit_delta_is_false :
    Distribution.lineDerivCLM (1:ℝ) (zeroExtension 0 (fun _ => (1:ℂ)))≠(0:CDist) := by
  rw [constant_zeroExtension_source]
  exact unit_delta_ne_zero

/-- The actual correction repairs this source; it is not merely a formal symbol. -/
example : Distribution.lineDerivCLM (1:ℝ) (zeroExtension 0 (fun _ => (1:ℂ)))=
    mulComplexDist (fun _ => (1:ℂ)) contDiff_const
      (zeroExtension 0 (fun _ => (0:ℂ))+deltaValue 0 (1/1)) := by
  exact corrected_zeroExtension_second 0 (fun _ => 0) (fun _ => 1) (fun _ => 1)
    continuous_const contDiff_const contDiff_const one_ne_zero (by intros; simp)

#print axioms EnergyControls.omit_delta_is_false
#print axioms EnergyControls.expField_zero_endpoint_flux_false
end EnergyControls
