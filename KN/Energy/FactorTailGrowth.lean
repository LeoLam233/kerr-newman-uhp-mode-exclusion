import KN.Energy.PhysicalTailGrowth
import KN.Boundary.RegularSingularFactor

noncomputable section
open Filter Set Asymptotics
namespace KN.Energy
open KN.Boundary

theorem power_factor_derivative_identity (rp : ℝ) (α : ℂ) (f v : ℝ → ℂ)
    (hf : Differentiable ℝ f)
    (he : ∀ r ∈ Ioi rp, v r=((r-rp:ℝ):ℂ)^α*f r)
    {r : ℝ} (hr : rp < r) :
    ((r-rp:ℝ):ℂ)^(α+1)*deriv f r =
      ((r-rp:ℝ):ℂ)*deriv v r-α*v r := by
  have hp := positivePower_hasDerivAt rp r α hr
  have hd := hp.mul (hf r).hasDerivAt
  have hv : HasDerivAt v
      (positivePower rp α r*(α/((r-rp:ℝ):ℂ))*f r+
        positivePower rp α r*deriv f r) r := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with x hx
    simp only [Pi.mul_apply]
    rw [he x hx,positivePower_eq_cpow rp x α hx]
  rw [hv.deriv, he r hr, positivePower_eq_cpow rp r α hr,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hr))),
    Complex.cpow_one]
  have ht : ((r-rp:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hr))
  simp only [div_eq_mul_inv]
  linear_combination -(((r-rp:ℝ):ℂ)^α*α*f r) * (mul_inv_cancel₀ ht)

theorem power_factor_expPolyGrowth (rp k : ℝ) (α : ℂ) (f v : ℝ → ℂ)
    (hf : Differentiable ℝ f)
    (he : ∀ r ∈ Ioi rp, v r=((r-rp:ℝ):ℂ)^α*f r)
    (hv : ExpPolyGrowth k v) (hd : ExpPolyGrowth k (deriv v)) :
    ExpPolyGrowth k (fun r => ((r-rp:ℝ):ℂ)^(α+1)*f r) ∧
    ExpPolyGrowth k (fun r => ((r-rp:ℝ):ℂ)^(α+1)*deriv f r) := by
  have ht : PolyBound (fun r : ℝ => ((r-rp:ℝ):ℂ)) := by
    have hp := polynomialConormal_polynomial (Polynomial.X-Polynomial.C (rp:ℂ))
    simpa [PolyBound] using hp 0
  constructor
  · apply (hv.mul_poly ht).congr
    filter_upwards [eventually_gt_atTop rp] with r hr
    rw [he r hr, Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hr))),Complex.cpow_one]
    ring
  · apply ((hd.mul_poly ht).add (hv.mul_poly (polyBound_const (-α)))).congr
    filter_upwards [eventually_gt_atTop rp] with r hr
    rw [power_factor_derivative_identity rp α f v hf he hr]
    ring

/-- Every fixed polynomial moment of both finite-part representatives satisfies
the exact exponential decay required for L1 and the differentiated transform. -/
theorem power_factor_damped_moments (rp k β : ℝ) (hb : β+k < 0) (α : ℂ)
    (f v : ℝ → ℂ) (hf : Differentiable ℝ f)
    (he : ∀ r ∈ Ioi rp, v r=((r-rp:ℝ):ℂ)^α*f r)
    (hv : ExpPolyGrowth k v) (hd : ExpPolyGrowth k (deriv v)) (j : ℕ) :
    (fun r : ℝ => (Real.exp (β*r):ℂ)*(((r-rp:ℝ):ℂ)^(α+1)*f r*(r:ℂ)^j))
      =O[atTop] (fun r : ℝ => Real.exp (((β+k)/2)*r)) ∧
    (fun r : ℝ => (Real.exp (β*r):ℂ)*(((r-rp:ℝ):ℂ)^(α+1)*deriv f r*(r:ℂ)^j))
      =O[atTop] (fun r : ℝ => Real.exp (((β+k)/2)*r)) := by
  have hm : PolyBound (fun r : ℝ => (r:ℂ)^j) :=
    (polynomialConormal_pow 0 (fun r : ℝ => (r:ℂ))
      Complex.ofRealCLM.contDiff.contDiffOn polynomialConormal_coordinate j) 0
  have hh := power_factor_expPolyGrowth rp k α f v hf he hv hd
  exact ⟨expPolyGrowth_damping (hh.1.mul_poly hm) β hb,
    expPolyGrowth_damping (hh.2.mul_poly hm) β hb⟩

end KN.Energy
