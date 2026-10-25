import KN.Boundary.GaugeDerivative
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section
namespace KN.Boundary

def radialMultiplier (b : Background) (m : ℤ) (ω : ℂ) (q : ℝ) (r : ℝ) : ℂ :=
  (Real.rpow (b.Delta r) q : ℂ) * (gauge b m ω r)^2 *
    Complex.exp (-2*Complex.I*b.eta*ω*r)

theorem radialMultiplier_ne_zero (b : Background) (m : ℤ) (ω : ℂ) (q : ℝ)
    {r : ℝ} (hr : b.rPlus < r) : radialMultiplier b m ω q r ≠ 0 := by
  unfold radialMultiplier
  exact mul_ne_zero (mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (b.Delta_pos hr) q)))
    (pow_ne_zero _ (gauge_ne_zero b m ω r))) (Complex.exp_ne_zero _)

/-- Logarithmic derivative of the actual multiplier in (27), at any real exponent. -/
theorem radialMultiplier_hasDerivAt (b : Background) (m : ℤ) (ω : ℂ) (q : ℝ)
    {r : ℝ} (hr : b.rPlus < r) :
    HasDerivAt (radialMultiplier b m ω q)
      (radialMultiplier b m ω q r *
        ((q:ℂ)*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ) +
          2*Complex.I*b.frequencyK m ω r/(b.Delta r:ℂ) - 2*Complex.I*b.eta*ω)) r := by
  have hp := (delta_rpow_hasDerivAt b q hr).ofReal_comp
  have hg := (gauge_hasDerivAt b m ω hr).pow 2
  have he := ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul (-2*Complex.I*b.eta*ω)).cexp
  have hd := (hp.mul hg).mul he
  have hdelta : b.Delta r ≠ 0 := ne_of_gt (b.Delta_pos hr)
  convert hd using 1
  · rfl
  · simp [radialMultiplier, Real.rpow_sub_one hdelta]
    ring

/-- The exact multiplier annihilates Δ∂r+L on its own. -/
theorem radialMultiplier_balance (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ)
    {r : ℝ} (hr : b.rPlus < r) :
    (b.Delta r:ℂ) * deriv (radialMultiplier b m ω (-(1+3*σ)/2)) r +
      (((1+3*(σ:ℂ))/2)*(2*(r:ℂ)-2*b.M) -
        2*Complex.I*(b.frequencyK m ω r - (b.eta:ℂ)*ω*(b.Delta r:ℂ))) *
          radialMultiplier b m ω (-(1+3*σ)/2) r = 0 := by
  rw [(radialMultiplier_hasDerivAt b m ω (-(1+3*σ)/2) hr).deriv]
  have hd : (b.Delta r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (b.Delta_pos hr))
  push_cast
  field_simp
  ring

end KN.Boundary
