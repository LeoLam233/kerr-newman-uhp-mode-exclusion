import KN.Kerr.SmoothRadial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace KN.Kerr
open Set
open scoped ContDiff

/-- A global smooth chart ℝ → (rp,∞). This avoids assuming an exterior
solution extends smoothly through the inner horizon or to all real radii. -/
noncomputable def exteriorChart (rp t : ℝ) : ℝ := rp + Real.exp t

theorem exteriorChart_mem (rp t : ℝ) : exteriorChart rp t ∈ Ioi rp := by
  change rp < rp + Real.exp t
  exact lt_add_of_pos_right rp (Real.exp_pos t)

theorem exteriorChart_surjective (rp r : ℝ) (hr : rp < r) :
    exteriorChart rp (Real.log (r - rp)) = r := by
  rw [exteriorChart, Real.exp_log (sub_pos.mpr hr)]
  ring

noncomputable def exteriorCoordinate (rp : ℝ) : SmoothRadial :=
  ⟨fun t => (exteriorChart rp t : ℂ), by
    change ContDiff ℝ ∞ (fun t => (exteriorChart rp t : ℂ))
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.add Real.contDiff_exp)⟩

noncomputable def exteriorWeight : SmoothRadial :=
  ⟨fun t => (Real.exp (-t) : ℂ), by
    change ContDiff ℝ ∞ (fun t => (Real.exp (-t) : ℂ))
    exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)⟩

/-- d/dr in the exponential exterior chart is e^(-t) d/dt. -/
noncomputable def exteriorDerivation : Derivation ℂ SmoothRadial SmoothRadial :=
  exteriorWeight • radialDerivation

@[simp] theorem exteriorDerivation_coordinate (rp : ℝ) :
    exteriorDerivation (exteriorCoordinate rp) = 1 := by
  apply Subtype.ext
  funext t
  change (Real.exp (-t) : ℂ) * deriv (fun t => ((rp + Real.exp t : ℝ) : ℂ)) t = 1
  have hd : HasDerivAt (fun t : ℝ => ((rp + Real.exp t : ℝ) : ℂ)) (Real.exp t : ℂ) t := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      ((Real.hasDerivAt_exp t).const_add rp)
  rw [hd.deriv, ← Complex.ofReal_mul, Real.exp_neg, inv_mul_cancel₀ (ne_of_gt (Real.exp_pos t))]
  norm_num

/-- Pullback of any C∞ exterior function, with no requirement outside the exterior. -/
noncomputable def exteriorPullback (rp : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi rp)) : SmoothRadial :=
  ⟨fun t => f (exteriorChart rp t), by
    change ContDiff ℝ ∞ (fun t => f (exteriorChart rp t))
    exact hf.comp_contDiff (contDiff_const.add Real.contDiff_exp) (exteriorChart_mem rp)⟩

/-- The weighted derivation is exactly the physical radial derivative. -/
theorem exteriorDerivation_pullback (rp : ℝ) (f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ioi rp)) (t : ℝ) :
    (exteriorDerivation (exteriorPullback rp f hf)).val t =
      deriv f (exteriorChart rp t) := by
  change (Real.exp (-t) : ℂ) * deriv (fun t => f (exteriorChart rp t)) t = _
  have hfd : DifferentiableAt ℝ f (exteriorChart rp t) :=
    ((hf _ (exteriorChart_mem rp t)).contDiffAt
      (isOpen_Ioi.mem_nhds (exteriorChart_mem rp t))).differentiableAt (by simp)
  have hd : HasDerivAt (fun t => f (exteriorChart rp t))
      (Real.exp t • deriv f (exteriorChart rp t)) t := by
    exact hfd.hasDerivAt.scomp t ((Real.hasDerivAt_exp t).const_add rp)
  rw [hd.deriv]
  simp only [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, Real.exp_neg,
    inv_mul_cancel₀ (ne_of_gt (Real.exp_pos t)), Complex.ofReal_one, one_mul]

/-- The spin-one differential identity on the entire physical exterior. -/
theorem exterior_intertwiner_one (rp : ℝ) (M a m omega Λ : ℂ) (f : SmoothRadial) :
    exteriorDerivation (exteriorDerivation
      (radialOperator exteriorDerivation (exteriorCoordinate rp) M a m omega Λ 1 f)) =
    radialOperator exteriorDerivation (exteriorCoordinate rp) M a m omega Λ (-1)
      (exteriorDerivation (exteriorDerivation f)) :=
  intertwiner_spin_one exteriorDerivation (exteriorCoordinate rp) M a m omega Λ
    (exteriorDerivation_coordinate rp) f

/-- The spin-two identity on the entire exterior, including exceptional frequencies. -/
theorem exterior_intertwiner_two (rp : ℝ) (M a m omega Λ : ℂ) (f : SmoothRadial) :
    exteriorDerivation (exteriorDerivation (exteriorDerivation (exteriorDerivation
      (radialOperator exteriorDerivation (exteriorCoordinate rp) M a m omega Λ 2 f)))) =
    radialOperator exteriorDerivation (exteriorCoordinate rp) M a m omega Λ (-2)
      (exteriorDerivation (exteriorDerivation (exteriorDerivation (exteriorDerivation f)))) :=
  intertwiner_spin_two exteriorDerivation (exteriorCoordinate rp) M a m omega Λ
    (exteriorDerivation_coordinate rp) f

end KN.Kerr
