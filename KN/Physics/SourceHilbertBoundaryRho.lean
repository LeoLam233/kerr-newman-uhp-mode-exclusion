import KN.Physics.SourceHilbertBoundaryMultiplier
import KN.Physics.SourceHorizonMatrices
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open scoped BoundedContinuousFunction
open Set
namespace KN.Physics

/-- Bounded continuous angular cosine, with its genuine supremum norm. -/
def angularCosine : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (Real.cos t:ℂ))
    (Complex.continuous_ofReal.comp Real.continuous_cos) 1 (fun t => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one t)

def angularSine : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (Real.sin t:ℂ))
    (Complex.continuous_ofReal.comp Real.continuous_sin) 1 (fun t => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one t)

/-- Both rho and its conjugate occur by choosing the sign of a. -/
def rhoCoefficient (a r : ℝ) : ℝ →ᵇ ℂ := r • (1 : ℝ →ᵇ ℂ)+(Complex.I*a) • angularCosine

lemma rhoCoefficient_apply (a r t : ℝ) :
    rhoCoefficient a r t=(r:ℂ)+Complex.I*a*Real.cos t := by
  simp [rhoCoefficient, angularCosine, Complex.real_smul]

lemma rhoCoefficient_norm_lower (a r t : ℝ) (hr : 0<r) : r ≤ ‖rhoCoefficient a r t‖ := by
  have h := Complex.abs_re_le_norm (rhoCoefficient a r t)
  rw [rhoCoefficient_apply] at h ⊢
  simpa [Complex.mul_re, Complex.mul_im, abs_of_pos hr] using h

lemma rhoCoefficient_ne_zero (a r t : ℝ) (hr : 0<r) : rhoCoefficient a r t ≠ 0 := by
  intro h
  have hh := rhoCoefficient_norm_lower a r t hr
  rw [h,norm_zero] at hh
  linarith

def rhoReciprocalAt (a r : ℝ) (hr : 0<r) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => (rhoCoefficient a r t)⁻¹)
    ((rhoCoefficient a r).continuous.inv₀ (fun t => rhoCoefficient_ne_zero a r t hr)) (r⁻¹)
    (fun t => by
      rw [norm_inv]
      exact inv_anti₀ hr (rhoCoefficient_norm_lower a r t hr))

lemma rhoCoefficient_isUnit (a r : ℝ) (hr : 0<r) : IsUnit (rhoCoefficient a r) := by
  refine ⟨⟨rhoCoefficient a r, rhoReciprocalAt a r hr, ?_, ?_⟩, rfl⟩
  · ext t
    exact mul_inv_cancel₀ (rhoCoefficient_ne_zero a r t hr)
  · ext t
    exact inv_mul_cancel₀ (rhoCoefficient_ne_zero a r t hr)

def rhoReciprocal (a r : ℝ) : ℝ →ᵇ ℂ := Ring.inverse (rhoCoefficient a r)

lemma rhoReciprocal_eq (a r : ℝ) (hr : 0<r) :
    rhoReciprocal a r=rhoReciprocalAt a r hr := by
  let u : (ℝ →ᵇ ℂ)ˣ := ⟨rhoCoefficient a r,rhoReciprocalAt a r hr,
    by ext t; exact mul_inv_cancel₀ (rhoCoefficient_ne_zero a r t hr),
    by ext t; exact inv_mul_cancel₀ (rhoCoefficient_ne_zero a r t hr)⟩
  exact Ring.inverse_unit u

lemma rhoReciprocal_apply (a r t : ℝ) (hr : 0<r) :
    rhoReciprocal a r t=((r:ℂ)+Complex.I*a*Real.cos t)⁻¹ := by
  rw [rhoReciprocal_eq a r hr]
  change (rhoCoefficient a r t)⁻¹=_
  rw [rhoCoefficient_apply]

lemma rhoReciprocal_norm_le (a r : ℝ) (hr : 0<r) : ‖rhoReciprocal a r‖ ≤ r⁻¹ := by
  rw [rhoReciprocal_eq a r hr]
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (le_of_lt (inv_pos.mpr hr)) _

lemma rhoCoefficient_smooth (a : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (rhoCoefficient a) := by
  unfold rhoCoefficient
  exact (contDiff_id.smul contDiff_const).add contDiff_const

lemma rhoReciprocal_smooth (a : ℝ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (rhoReciprocal a) (Ioi 0) := by
  intro r hr
  obtain ⟨u,hu⟩ := rhoCoefficient_isUnit a r hr
  have hi : ContDiffAt ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) Ring.inverse (rhoCoefficient a r) := by
    rw [← hu]
    exact contDiffAt_ringInverse ℝ u
  have hh := hi.comp r (rhoCoefficient_smooth a).contDiffAt
  exact hh.contDiffWithinAt

end KN.Physics
