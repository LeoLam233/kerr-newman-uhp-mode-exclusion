import KN.Physics.SourceHilbertBoundaryOutgoing

noncomputable section
open Set MeasureTheory
open scoped ContDiff BoundedContinuousFunction
namespace KN.Physics
open KN.Angular KN.Boundary

/-- Exterior smoothness and the actual all-orders Euler polynomial bounds. -/
def SourceSC {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (rp : ℝ) (f : ℝ → E) : Prop := RadialSmooth rp f ∧ PolynomialConormal f

namespace SourceSC
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {rp : ℝ}
lemma const (c : E) : SourceSC rp (fun _ => c) := ⟨contDiffOn_const,PolynomialConormal.const c⟩
lemma add {f g : ℝ → E} (hf : SourceSC rp f) (hg : SourceSC rp g) :
    SourceSC rp (fun r => f r+g r) := ⟨hf.1.add hg.1,hf.2.add_on hg.2 hf.1 hg.1⟩
lemma sub {f g : ℝ → E} (hf : SourceSC rp f) (hg : SourceSC rp g) :
    SourceSC rp (fun r => f r-g r) := ⟨hf.1.sub hg.1,hf.2.sub_on hg.2 hf.1 hg.1⟩
lemma smul {f : ℝ → ℂ} {g : ℝ → E} (hf : SourceSC rp f) (hg : SourceSC rp g) :
    SourceSC rp (fun r => f r • g r) := ⟨hf.1.fun_smul hg.1,hf.2.smul_on hg.2 hf.1 hg.1⟩
lemma const_smul {g : ℝ → E} (hg : SourceSC rp g) (c : ℂ) :
    SourceSC rp (fun r => c • g r) := (const c).smul hg
lemma map {f : ℝ → E} (hf : SourceSC rp f) (L : E →L[ℂ] F) :
    SourceSC rp (fun r => L (f r)) :=
  ⟨(L.restrictScalars ℝ).contDiff.comp_contDiffOn hf.1,hf.2.map_on hf.1 L⟩
lemma mul {f g : ℝ → AngularCoefficient} (hf : SourceSC rp f) (hg : SourceSC rp g) :
    SourceSC rp (fun r => f r*g r) :=
  ⟨hf.1.mul hg.1,PolynomialConormal.bilinear_on (ContinuousLinearMap.mul ℝ AngularCoefficient)
    hf.2 hg.2 hf.1 hg.1⟩
lemma matrix (a00 a01 a10 a11 : ℝ → AngularCoefficient) (u : ℝ → AngularHilbert)
    (h00 : SourceSC rp a00) (h01 : SourceSC rp a01)
    (h10 : SourceSC rp a10) (h11 : SourceSC rp a11) (hu : SourceSC rp u) :
    SourceSC rp (fun r => matrixCoefficientL (a00 r) (a01 r) (a10 r) (a11 r) (u r)) :=
  ⟨matrixCoefficient_action_smooth _ _ _ _ _ h00.1 h01.1 h10.1 h11.1 hu.1,
    matrixCoefficient_action_conormal _ _ _ _ _ h00.2 h01.2 h10.2 h11.2 h00.1 h01.1 h10.1 h11.1 hu.2 hu.1⟩
end SourceSC

lemma rhoReciprocal_sourceSC (b : KN.Background) (a : ℝ) : SourceSC b.rPlus (rhoReciprocal a) :=
  ⟨(rhoReciprocal_smooth a).mono (fun _ hr => b.rPlus_pos.trans hr),rhoReciprocal_conormal a⟩

lemma horizonEvenL_sourceSC (b : KN.Background) (u : ℝ → AngularHilbert) (hu : SourceSC b.rPlus u) :
    SourceSC b.rPlus (fun r => horizonEvenL b r (u r)) :=
  SourceSC.matrix _ _ _ _ _ ((rhoReciprocal_sourceSC b (-b.a)).const_smul (2*(b.Q:ℂ)))
    (SourceSC.const 0) (SourceSC.const 0) ((rhoReciprocal_sourceSC b b.a).const_smul (2*(b.Q:ℂ))) hu

lemma horizonOddL_sourceSC (b : KN.Background) (u : ℝ → AngularHilbert) (hu : SourceSC b.rPlus u) :
    SourceSC b.rPlus (fun r => horizonOddL b r (u r)) :=
  SourceSC.matrix _ _ _ _ _
    (((SourceSC.const angularSine).mul (rhoReciprocal_sourceSC b (-b.a))).const_smul (-2*(b.Q:ℂ)*b.a))
    (((SourceSC.const ((b.M:ℂ) • (1:AngularCoefficient))).sub
      ((rhoReciprocal_sourceSC b b.a).const_smul ((b.Q:ℂ)^2))).const_smul (2*Complex.I))
    (((SourceSC.const ((b.M:ℂ) • (1:AngularCoefficient))).sub
      ((rhoReciprocal_sourceSC b (-b.a)).const_smul ((b.Q:ℂ)^2))).const_smul (-2*Complex.I))
    (((SourceSC.const angularSine).mul (rhoReciprocal_sourceSC b b.a)).const_smul (2*(b.Q:ℂ)*b.a)) hu

lemma deltaPower_sourceSC (b : KN.Background) (q : ℝ) :
    SourceSC b.rPlus (fun r => (Real.rpow (b.Delta r) q:ℂ)) :=
  ⟨delta_rpow_smooth b q,delta_rpow_conormal b q⟩

lemma deltaSqrt_sourceSC (b : KN.Background) : SourceSC b.rPlus (fun r => (Real.sqrt (b.Delta r):ℂ)) := by
  have he : (fun r => (Real.sqrt (b.Delta r):ℂ))=(fun r => (Real.rpow (b.Delta r) ((1:ℝ)/2):ℂ)) := by
    funext r
    exact congrArg Complex.ofReal (Real.sqrt_eq_rpow _)
  rw [he]
  exact deltaPower_sourceSC b (1/2)

lemma sourceAdjL_sourceSC (b : KN.Background) (u : ℝ → AngularHilbert) (hu : SourceSC b.rPlus u) :
    SourceSC b.rPlus (fun r => sourceAdjL b r (u r)) := by
  exact (((deltaSqrt_sourceSC b).smul (horizonEvenL_sourceSC b u hu)).add
    (horizonOddL_sourceSC b u hu)).const_smul (1/2)

lemma sourceStarL_sourceSC (b : KN.Background) (u : ℝ → AngularHilbert) (hu : SourceSC b.rPlus u) :
    SourceSC b.rPlus (fun r => sourceStarL b r (u r)) := by
  exact (((deltaSqrt_sourceSC b).smul (horizonEvenL_sourceSC b u hu)).sub
    (horizonOddL_sourceSC b u hu)).const_smul (1/2)

end KN.Physics
