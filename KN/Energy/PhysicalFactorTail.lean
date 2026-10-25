import KN.Energy.FactorTailGrowth
import KN.Boundary.RescaleFactor

noncomputable section
open Filter Set Asymptotics
namespace KN.Energy
open KN.Boundary

theorem multiplier_rescaled_damped_moments (b : Background) (m : ℤ) (ω : ℂ)
    (q e : ℝ) (hq : q+e ≤ 1) (w z f : ℝ → ℂ) (α : ℂ)
    (hf : Differentiable ℝ f)
    (hw : ∀ r ∈ Ioi b.rPlus, w r=rescaleFactor b m ω e r*z r)
    (he : ∀ r ∈ Ioi b.rPlus,
      radialMultiplier b m ω q r*w r=((r-b.rPlus:ℝ):ℂ)^α*f r)
    (hs : ExteriorSmooth b.rPlus (fun r => gauge b m ω r*z r))
    (hout : PolynomialConormal (fun r => gauge b m ω r*z r))
    (β : ℝ) (hb : β < -(b.eta*ω.im)) (j : ℕ) :
    (fun r : ℝ => (Real.exp (β*r):ℂ)*(((r-b.rPlus:ℝ):ℂ)^(α+1)*f r*(r:ℂ)^j))
      =O[atTop] (fun r : ℝ => Real.exp (((β+b.eta*ω.im)/2)*r)) ∧
    (fun r : ℝ => (Real.exp (β*r):ℂ)*(((r-b.rPlus:ℝ):ℂ)^(α+1)*deriv f r*(r:ℂ)^j))
      =O[atTop] (fun r : ℝ => Real.exp (((β+b.eta*ω.im)/2)*r)) := by
  let U := fun r => gauge b m ω r*z r
  let v := fun r => radialMultiplier b m ω q r*w r
  have heq : EqOn (outgoingTail b ω (q+e) U) v (Ioi b.rPlus) := by
    intro r hr
    dsimp [v,outgoingTail,U]
    rw [hw r hr]
    simp only [← mul_assoc]
    rw [multiplier_rescale_identity b m ω q e hr]
    rfl
  have hve : outgoingTail b ω (q+e) U =ᶠ[atTop] v := by
    filter_upwards [eventually_gt_atTop b.rPlus] with r hr
    exact heq hr
  have hde : deriv (outgoingTail b ω (q+e) U) =ᶠ[atTop] deriv v := by
    filter_upwards [eventually_gt_atTop b.rPlus] with r hr
    exact heq.deriv isOpen_Ioi hr
  exact power_factor_damped_moments b.rPlus (b.eta*ω.im) β (by linarith) α f v hf he
    ((outgoingTail_expPolyGrowth b ω (q+e) hq U hout).congr hve)
    ((outgoingTail_deriv_expPolyGrowth b ω (q+e) hq U hs hout).congr hde) j

end KN.Energy
