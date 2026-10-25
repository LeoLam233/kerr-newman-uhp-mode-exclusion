import KN.ChargedRadial.EigenmodeExclusion
import KN.Physics.SourceHilbertRecovery
import Mathlib.Analysis.Calculus.BumpFunction.Basic

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace MeasureTheory
open scoped Distributions Matrix
namespace RadialControls
open KN.ChargedRadial KN.Physics

def bump : ContDiffBump (0:ℝ) := ⟨1,2,by norm_num,by norm_num⟩
def test : 𝓓((⊤ : Opens ℝ),ℝ) := ⟨bump,bump.contDiff,bump.hasCompactSupport,by simp⟩
lemma test_zero : test 0=1 := by
  exact bump.one_of_mem_closedBall (by simp [bump])

/-- Actual delta detection by a compactly supported C-infinity test. -/
theorem delta_nonzero : deltaValue 0 (1:ℂ) ≠ 0 := by
  intro h
  have hh := congrArg (fun T : CDist => T test) h
  rw [deltaValue_apply,test_zero] at hh
  norm_num at hh

/-- The total Lean finitePart function is NOT a canonical extension at the pole.
The public theorem excludes this parameter, and this regression test explains why. -/
theorem finitePart_at_pole_is_zero : finitePartAt 0 (-1) (fun _ => (1:ℂ))=0 := by
  ext phi
  simp [finitePartAt]

theorem exterior_power_at_pole_nonzero : (((1:ℝ):ℂ)^(-1:ℂ))*(1:ℂ) ≠ 0 := by norm_num

/-- The zero extension of the nonzero horizon value has an actual boundary source. -/
theorem step_derivative : Distribution.lineDerivCLM (1:ℝ) (zeroExtension 0 (fun _ => (1:ℂ)))=
    deltaValue 0 1 := by
  rw [derivative_zeroExtension 0 (fun _ => (1:ℂ)) contDiff_const]
  have hz : zeroExtension 0 (deriv (fun _ : ℝ => (1:ℂ)))=0 := by
    have hd : deriv (fun _ : ℝ => (1:ℂ)) = fun _ => 0 := by
      funext x
      exact deriv_const x 1
    rw [hd]
    exact Distribution.ofFun_zero
  rw [hz,zero_add]

theorem omitted_delta_fails : Distribution.lineDerivCLM (1:ℝ)
    (zeroExtension 0 (fun _ => (1:ℂ))) ≠ (0 : CDist) := by
  rw [step_derivative]
  exact delta_nonzero

theorem wrong_delta_sign_fails : Distribution.lineDerivCLM (1:ℝ)
    (zeroExtension 0 (fun _ => (1:ℂ))) ≠ -deltaValue 0 1 := by
  rw [step_derivative]
  intro hh
  have ht := congrArg (fun T : CDist => T test) hh
  change deltaValue 0 1 test = -(deltaValue 0 1 test) at ht
  rw [deltaValue_apply,test_zero] at ht
  norm_num at ht

/-- The correct exceptional coefficient repairs the ordinary second equation. -/
theorem exact_delta_repairs : Distribution.lineDerivCLM (1:ℝ)
    (zeroExtension 0 (fun _ => (1:ℂ))) =
    mulComplexDist (fun _ => (1:ℂ)) contDiff_const
      (zeroExtension 0 (fun _ => (0:ℂ))+deltaValue 0 (1/1)) := by
  exact corrected_zeroExtension_second 0 (fun _ => 0) (fun _ => 1) (fun _ => 1)
    continuous_const contDiff_const contDiff_const (by norm_num) (by simp)

/-- Omitting the minus chiral block destroys injectivity even for the literal
physical source transformation, not merely an abstract singular matrix. -/
theorem plus_block_alone_not_injective (positive : Bool) (b : KN.Background) (r t : ℝ) :
    ∃ u : Fin 4 → ℂ, u ≠ 0 ∧ (sourceTransform positive b r t u).1=0 := by
  let u : Fin 4 → ℂ := ![-Complex.I*transformMix positive b r,1,0,0]
  refine ⟨u,?_,?_⟩
  · intro h
    have hh := congrFun h 1
    norm_num [u] at hh
  · have hi : chiralInput (transformScale positive b r t) (transformCharge positive b)
        (transformMix positive b r) 1 u=0 := by
      ext j
      fin_cases j <;> simp [chiralInput,u]
    change (physicalSourceMatrix b r t).adjugate *ᵥ _=0
    rw [hi,Matrix.mulVec_zero]

theorem minus_block_alone_not_injective (positive : Bool) (b : KN.Background) (r t : ℝ) :
    ∃ u : Fin 4 → ℂ, u ≠ 0 ∧ (sourceTransform positive b r t u).2=0 := by
  let u : Fin 4 → ℂ := ![Complex.I*transformMix positive b r,1,0,0]
  refine ⟨u,?_,?_⟩
  · intro h
    have hh := congrFun h 1
    norm_num [u] at hh
  · have hi : chiralInput (transformScale positive b r t) (transformCharge positive b)
        (transformMix positive b r) (-1) u=0 := by
      ext j
      fin_cases j <;> simp [chiralInput,u]
    change (physicalSourceMatrix b r t).conjTranspose *ᵥ _=0
    rw [hi,Matrix.mulVec_zero]

open KN.Boundary KN.Angular KN.Energy
theorem original_boundary_and_equation_accepted (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ)
    (omega lam : ℂ) (hw : 0 < omega.im) (u v : AngularHilbert) (hu : ‖u‖ = 1)
    (hg : StaticGraph (spinSign positive) b.beta m u v)
    (he : v + omega • reducedFrequencyMultiplier b (spinSign positive) u = lam • u)
    (y z : ℝ → ℂ)
    (hy : HorizonRegular b m omega (-(3*spinSign positive/4)) y)
    (hz : HorizonRegular b m omega (-(3*spinSign positive/4-1/2)) z)
    (ho : Outgoing b m omega y)
    (hp : OriginalSelectedPair b m (spinSign positive) omega lam y z) : EqOn y 0 (Ioi b.rPlus) ∧ EqOn z 0 (Ioi b.rPlus) := by
  exact charged_original_eigenmode_exclusion positive b hQ m omega lam hw u v hu hg he y z hy hz ho hp


/-- Both chiral blocks and actual exterior nondegeneracy recover the literal source. -/
theorem both_blocks_recover (positive : Bool) (b : KN.Background) (hQ : b.Q ≠ 0)
    {r t : ℝ} (hr : b.rPlus < r) (ht : 0 < t) (hp : t < Real.pi)
    (u : Fin 4 → ℂ) (hz : sourceTransform positive b r t u = 0) : u = 0 :=
  sourceTransform_zero positive b hQ hr ht hp u hz

#check KN.ChargedRadial.charged_original_eigenmode_exclusion
#check KN.Physics.sourceFullTransform_original_pointwise_zero
#print axioms RadialControls.omitted_delta_fails
#print axioms RadialControls.plus_block_alone_not_injective
end RadialControls
