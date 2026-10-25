import KN.Angular.MaximalDomain
import KN.Kerr.HilbertAngular
import KN.Boundary.Radial
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open MeasureTheory Set
open scoped ComplexInnerProductSpace
namespace KN.Physics
open KN.Angular

/-- Original two-component spin-section L² space, before source-matrix transport.
The spherical sin(theta) measure is the same one used in the Kerr branch. -/
abbrev SourceAngularHilbert := Lp AngularFiber 2 KN.Kerr.sphericalMeasure

lemma angularMeasure_ac_spherical : angularMeasure ≪ KN.Kerr.sphericalMeasure := by
  apply withDensity_absolutelyContinuous' (Real.continuous_sin.measurable.ennreal_ofReal.aemeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2))

lemma source_ae_to_angular {p : ℝ → Prop} (hp : ∀ᵐ t ∂KN.Kerr.sphericalMeasure, p t) :
    ∀ᵐ t ∂angularMeasure, p t := angularMeasure_ac_spherical.ae_le hp

def sqrtSinAction (u : SourceAngularHilbert) (t : ℝ) : AngularFiber :=
  (Real.sqrt (Real.sin t):ℂ) • u t

lemma sqrtSinAction_sq (u : SourceAngularHilbert) :
    (fun t => ‖sqrtSinAction u t‖^2) =ᵐ[angularMeasure]
      fun t => (ENNReal.ofReal (Real.sin t)).toReal*‖u t‖^2 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hs := le_of_lt (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
  simp only [sqrtSinAction,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hs,ENNReal.toReal_ofReal hs]

lemma sqrtSinAction_memLp (u : SourceAngularHilbert) : MemLp (sqrtSinAction u) 2 angularMeasure := by
  have hu : AEStronglyMeasurable (fun t => u t) angularMeasure :=
    (Lp.memLp u).aestronglyMeasurable.mono_ac angularMeasure_ac_spherical
  have hm : AEStronglyMeasurable (sqrtSinAction u) angularMeasure :=
    ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_sin)).aestronglyMeasurable).smul hu
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp u).aestronglyMeasurable).mp (Lp.memLp u)
  have hh := (integrable_withDensity_iff_integrable_smul'
    Real.continuous_sin.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top))).mp hi
  exact hh.congr (sqrtSinAction_sq u).symm

def sqrtSinLift (u : SourceAngularHilbert) : AngularHilbert :=
  (sqrtSinAction_memLp u).toLp (sqrtSinAction u)

lemma sqrtSinLift_ae (u : SourceAngularHilbert) :
    sqrtSinLift u =ᵐ[angularMeasure] sqrtSinAction u := (sqrtSinAction_memLp u).coeFn_toLp

lemma sqrtSinLift_add (u v : SourceAngularHilbert) : sqrtSinLift (u+v)=sqrtSinLift u+sqrtSinLift v := by
  apply Lp.ext
  filter_upwards [sqrtSinLift_ae (u+v),sqrtSinLift_ae u,sqrtSinLift_ae v,
    Lp.coeFn_add (sqrtSinLift u) (sqrtSinLift v),source_ae_to_angular (Lp.coeFn_add u v)] with t h1 h2 h3 h4 h5
  simp only [Pi.add_apply] at h4 h5
  rw [h1,h4,h2,h3]
  simp only [sqrtSinAction,h5,smul_add]

lemma sqrtSinLift_smul (c : ℂ) (u : SourceAngularHilbert) : sqrtSinLift (c • u)=c • sqrtSinLift u := by
  apply Lp.ext
  filter_upwards [sqrtSinLift_ae (c • u),sqrtSinLift_ae u,
    Lp.coeFn_smul c (sqrtSinLift u),source_ae_to_angular (Lp.coeFn_smul c u)] with t h1 h2 h3 h4
  simp only [Pi.smul_apply] at h3 h4
  rw [h1,h3,h2]
  simp only [sqrtSinAction,h4]
  exact smul_comm _ _ _

lemma sqrtSinLift_norm (u : SourceAngularHilbert) : ‖sqrtSinLift u‖=‖u‖ := by
  have hn {μ : Measure ℝ} (v : Lp AngularFiber 2 μ) : ∫ t, ‖v t‖^2 ∂μ = ‖v‖^2 := by
    have h := L2.inner_def (𝕜:=ℂ) v v
    simp only [inner_self_eq_norm_sq_to_K] at h
    exact_mod_cast h.symm
  have hh : ‖sqrtSinLift u‖^2=‖u‖^2 := by
    rw [← hn (sqrtSinLift u), ← hn u]
    have he : (fun t => ‖sqrtSinLift u t‖^2) =ᵐ[angularMeasure]
        fun t => (ENNReal.ofReal (Real.sin t)).toReal*‖u t‖^2 :=
      (sqrtSinLift_ae u).fun_comp (fun z => ‖z‖^2) |>.trans (sqrtSinAction_sq u)
    rw [integral_congr_ae he]
    symm
    exact integral_withDensity_eq_integral_toReal_smul
      Real.continuous_sin.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun t => ENNReal.ofReal_lt_top)) _
  nlinarith [norm_nonneg (sqrtSinLift u),norm_nonneg u]

/-- Fixed angular isometry from original spin sections to unweighted L².
It is independent of every radial source transformation. -/
def sourceAngularEmbedding : SourceAngularHilbert →ₗᵢ[ℂ] AngularHilbert where
  toFun := sqrtSinLift
  map_add' := sqrtSinLift_add
  map_smul' := sqrtSinLift_smul
  norm_map' := sqrtSinLift_norm

end KN.Physics
