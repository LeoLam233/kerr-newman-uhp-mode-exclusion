import KN.Physics.SourceHilbertBoundaryMatrix
noncomputable section
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
open Matrix
open Set MeasureTheory
open scoped BoundedContinuousFunction ContDiff
namespace KN.Physics
open KN.Angular

def horizonEvenL (b : KN.Background) (r : ℝ) : AngularHilbert →L[ℂ] AngularHilbert :=
  matrixCoefficientL ((2*(b.Q:ℂ)) • rhoReciprocal (-b.a) r) 0 0
    ((2*(b.Q:ℂ)) • rhoReciprocal b.a r)

def horizonOddL (b : KN.Background) (r : ℝ) : AngularHilbert →L[ℂ] AngularHilbert :=
  matrixCoefficientL
    ((-2*(b.Q:ℂ)*b.a) • (angularSine*rhoReciprocal (-b.a) r))
    ((2*Complex.I) • ((b.M:ℂ) • (1:ℝ →ᵇ ℂ)-(b.Q:ℂ)^2 • rhoReciprocal b.a r))
    ((-2*Complex.I) • ((b.M:ℂ) • (1:ℝ →ᵇ ℂ)-(b.Q:ℂ)^2 • rhoReciprocal (-b.a) r))
    ((2*(b.Q:ℂ)*b.a) • (angularSine*rhoReciprocal b.a r))

lemma rhoReciprocal_closed_smooth (b : KN.Background) (a : ℝ) :
    ContDiffOn ℝ ∞ (rhoReciprocal a) (Ici b.rPlus) :=
  (rhoReciprocal_smooth a).mono (fun _ hr => b.rPlus_pos.trans_le hr)

lemma horizonEvenL_action_smooth (b : KN.Background) (u : ℝ → AngularHilbert)
    (hu : ContDiffOn ℝ ∞ u (Ici b.rPlus)) :
    ContDiffOn ℝ ∞ (fun r => horizonEvenL b r (u r)) (Ici b.rPlus) := by
  exact matrixCoefficient_action_smooth _ _ _ _ u
    (contDiffOn_const.fun_smul (rhoReciprocal_closed_smooth b (-b.a))) contDiffOn_const contDiffOn_const
    (contDiffOn_const.fun_smul (rhoReciprocal_closed_smooth b b.a)) hu

lemma horizonOddL_action_smooth (b : KN.Background) (u : ℝ → AngularHilbert)
    (hu : ContDiffOn ℝ ∞ u (Ici b.rPlus)) :
    ContDiffOn ℝ ∞ (fun r => horizonOddL b r (u r)) (Ici b.rPlus) := by
  exact matrixCoefficient_action_smooth _ _ _ _ u
    (contDiffOn_const.fun_smul (contDiffOn_const.mul (rhoReciprocal_closed_smooth b (-b.a))))
    (contDiffOn_const.fun_smul (contDiffOn_const.sub (contDiffOn_const.fun_smul (rhoReciprocal_closed_smooth b b.a))))
    (contDiffOn_const.fun_smul (contDiffOn_const.sub (contDiffOn_const.fun_smul (rhoReciprocal_closed_smooth b (-b.a)))))
    (contDiffOn_const.fun_smul (contDiffOn_const.mul (rhoReciprocal_closed_smooth b b.a))) hu

lemma horizonEvenL_ae (b : KN.Background) {r : ℝ} (hr : b.rPlus≤r) (u : AngularHilbert) :
    horizonEvenL b r u =ᵐ[angularMeasure] fun t => WithLp.toLp 2
      (horizonEven b.Q b.a r (Real.cos t) *ᵥ (u t : Fin 2 → ℂ)) := by
  have hr0 := b.rPlus_pos.trans_le hr
  filter_upwards [matrixCoefficientL_ae ((2*(b.Q:ℂ)) • rhoReciprocal (-b.a) r) 0 0
    ((2*(b.Q:ℂ)) • rhoReciprocal b.a r) u] with t ht
  change (matrixCoefficientL _ _ _ _ u) t = _
  rw [ht]
  ext j
  fin_cases j <;> simp [horizonEven,Matrix.mulVec,vecHead,vecTail,rhoReciprocal_apply _ _ _ hr0,
    div_eq_mul_inv] <;> ring_nf <;> simp

lemma horizonOddL_ae (b : KN.Background) {r : ℝ} (hr : b.rPlus≤r) (u : AngularHilbert) :
    horizonOddL b r u =ᵐ[angularMeasure] fun t => WithLp.toLp 2
      (horizonOdd b.M b.Q b.a r (Real.sin t) (Real.cos t) *ᵥ (u t : Fin 2 → ℂ)) := by
  have hr0 := b.rPlus_pos.trans_le hr
  filter_upwards [matrixCoefficientL_ae
    ((-2*(b.Q:ℂ)*b.a) • (angularSine*rhoReciprocal (-b.a) r))
    ((2*Complex.I) • ((b.M:ℂ) • (1:ℝ →ᵇ ℂ)-(b.Q:ℂ)^2 • rhoReciprocal b.a r))
    ((-2*Complex.I) • ((b.M:ℂ) • (1:ℝ →ᵇ ℂ)-(b.Q:ℂ)^2 • rhoReciprocal (-b.a) r))
    ((2*(b.Q:ℂ)*b.a) • (angularSine*rhoReciprocal b.a r)) u] with t ht
  change (matrixCoefficientL _ _ _ _ u) t = _
  rw [ht]
  ext j
  fin_cases j <;> simp [horizonOdd,Matrix.mulVec,vecHead,vecTail,rhoReciprocal_apply _ _ _ hr0,
    angularSine,div_eq_mul_inv] <;> ring_nf <;> simp

end KN.Physics
