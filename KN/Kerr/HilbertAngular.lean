import KN.Kerr.AngularDomain
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace KN.Kerr
noncomputable section
open MeasureTheory Set
open scoped ContDiff

/-- The fixed azimuthal spin-section Hilbert measure, with the spherical area
weight. Endpoints have zero measure but regularity is imposed by the graph core. -/
def sphericalMeasure : Measure ℝ :=
  (volume.restrict (Ioo 0 Real.pi)).withDensity (fun θ => ENNReal.ofReal (Real.sin θ))
abbrev AngularH := Lp ℂ 2 sphericalMeasure

/-- Actual smooth spin-bundle graph, with both pole powers fixed. -/
def sphericalCoreGraph (m s : ℤ) : Set (AngularH × AngularH) :=
  {p | ∃ (u : ℝ → ℂ) (hu : MemLp u 2 sphericalMeasure)
      (hv : MemLp (angularOperator 0 s m 0 u) 2 sphericalMeasure),
    CanonicalSmoothAngular m s u ∧ hu.toLp u = p.1 ∧
      hv.toLp (angularOperator 0 s m 0 u) = p.2}

/-- Canonical closed graph: closure of smooth spin sections, not an unrestricted
maximal scalar singular-endpoint domain. -/
def sphericalClosedGraph (m s : ℤ) : Set (AngularH × AngularH) :=
  closure (sphericalCoreGraph m s)

/-- Genuine bounded multiplication on the spherical Hilbert space. -/
def angularMultiplier (q : ℝ → ℂ) (hq : MemLp q ⊤ sphericalMeasure) :
    AngularH →L[ℂ] AngularH :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL sphericalMeasure ⊤ 2 2 (hq.toLp q)

/-- The bounded multiplier acts by pointwise multiplication almost everywhere. -/
theorem angularMultiplier_coeFn (q : ℝ → ℂ) (hq : MemLp q ⊤ sphericalMeasure)
    (u : AngularH) : angularMultiplier q hq u =ᵐ[sphericalMeasure] fun θ => q θ*u θ := by
  have h := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hq.toLp q) u
  filter_upwards [h,hq.coeFn_toLp] with θ hθ hqθ
  change (angularMultiplier q hq u) θ = (hq.toLp q) θ*u θ at hθ
  rw [hθ,hqθ]

/-- Frequency perturbation of the canonical spherical operator. -/
def frequencyPotential (a : ℝ) (s : ℤ) (omega : ℂ) (θ : ℝ) : ℂ :=
  -(a : ℂ)^2 * omega^2 * (Real.cos θ : ℂ)^2 +
    2 * (a : ℂ) * (s : ℂ) * omega * (Real.cos θ : ℂ)

lemma frequencyPotential_continuous (a : ℝ) (s : ℤ) (omega : ℂ) :
    Continuous (frequencyPotential a s omega) := by
  unfold frequencyPotential
  fun_prop

lemma frequencyPotential_bound (a : ℝ) (s : ℤ) (omega : ℂ) (θ : ℝ) :
    ‖frequencyPotential a s omega θ‖ ≤
      ‖(a : ℂ)‖^2 * ‖omega‖^2 + 2 * ‖(a : ℂ)‖ * ‖(s : ℂ)‖ * ‖omega‖ := by
  have hc : ‖(Real.cos θ : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one θ
  have hc2 : ‖(Real.cos θ : ℂ)‖^2 ≤ 1 := by nlinarith [norm_nonneg (Real.cos θ : ℂ)]
  unfold frequencyPotential
  calc
    _ ≤ ‖-(a : ℂ)^2 * omega^2 * (Real.cos θ : ℂ)^2‖ +
      ‖2 * (a : ℂ) * (s : ℂ) * omega * (Real.cos θ : ℂ)‖ := norm_add_le _ _
    _ = ‖(a : ℂ)‖^2 * ‖omega‖^2 * ‖(Real.cos θ : ℂ)‖^2 +
      2 * ‖(a : ℂ)‖ * ‖(s : ℂ)‖ * ‖omega‖ * ‖(Real.cos θ : ℂ)‖ := by
        simp only [norm_mul,norm_neg,norm_pow]; norm_num
    _ ≤ _ := add_le_add (mul_le_of_le_one_right (by positivity) hc2)
      (mul_le_of_le_one_right (by positivity) hc)

lemma frequencyPotential_memLp (a : ℝ) (s : ℤ) (omega : ℂ) :
    MemLp (frequencyPotential a s omega) ⊤ sphericalMeasure :=
  memLp_top_of_bound (frequencyPotential_continuous a s omega).aestronglyMeasurable
    _ (Filter.Eventually.of_forall (frequencyPotential_bound a s omega))

def frequencyMultiplier (a : ℝ) (s : ℤ) (omega : ℂ) : AngularH →L[ℂ] AngularH :=
  angularMultiplier _ (frequencyPotential_memLp a s omega)

end
end KN.Kerr
