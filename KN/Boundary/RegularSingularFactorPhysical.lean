import KN.Boundary.RegularSingularFactor

noncomputable section
open Set
namespace KN.Boundary

def multiplierRegularPart (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ) (r : ℝ) : ℂ :=
  (-(1+3*(σ:ℂ))/2 - 2*Complex.I*ω*((r:ℂ)+b.rPlus) -
    Complex.I*b.frequencyK m ω b.rPlus/(b.delta:ℂ))/((r-b.rMinus:ℝ):ℂ) -
    2*Complex.I*b.eta*ω

theorem multiplierRegularPart_smooth (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (multiplierRegularPart b m ω σ) (Ioi b.rMinus) := by
  have hr : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ => (r:ℂ)) (Ioi b.rMinus) := Complex.ofRealCLM.contDiff.contDiffOn
  have hi : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (fun r : ℝ => ((r-b.rMinus:ℝ):ℂ)⁻¹) (Ioi b.rMinus) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const)).inv
      (fun r hr => Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hr)))
  unfold multiplierRegularPart
  simp only [div_eq_mul_inv]
  exact ((contDiffOn_const.sub (contDiffOn_const.mul (hr.add contDiffOn_const))).sub
    contDiffOn_const).mul hi |>.sub contDiffOn_const

theorem multiplier_logarithmic_split (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ)
    {r : ℝ} (hr : b.rPlus < r) :
    ((-(1+3*σ)/2:ℝ):ℂ)*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ) +
      2*Complex.I*b.frequencyK m ω r/(b.Delta r:ℂ) - 2*Complex.I*b.eta*ω =
    horizonAlpha b m ω σ/((r-b.rPlus:ℝ):ℂ) + multiplierRegularPart b m ω σ r := by
  have hgap : b.rMinus < b.rPlus := by linarith [b.horizon_gap,b.delta_pos]
  have hp : ((r-b.rPlus:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr hr))
  have hm : ((r-b.rMinus:ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (sub_pos.mpr (hgap.trans hr)))
  have hd : (b.delta:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt b.delta_pos)
  have hs : (b.rPlus:ℂ)+(b.rMinus:ℂ)=2*(b.M:ℂ) := by
    simp [Background.rPlus,Background.rMinus]
    ring
  have hg : (b.rPlus:ℂ)-(b.rMinus:ℂ)=2*(b.delta:ℂ) := by
    exact_mod_cast b.horizon_gap
  rw [b.delta_factor]
  unfold horizonAlpha multiplierRegularPart Background.frequencyK
  push_cast at *
  have hmEq : (b.rMinus:ℂ) = (b.rPlus:ℂ)-2*b.delta := by linear_combination -hg
  have hMEq : (b.M:ℂ) = (b.rPlus:ℂ)-b.delta := by linear_combination -(hs+hg)/2
  rw [hmEq, hMEq]
  rw [hmEq] at hm
  field_simp [hp, hm, hd]
  ring

theorem radialMultiplier_horizon_factor (b : Background) (m : ℤ) (ω : ℂ) (σ : ℝ) :
    ∃ f : ℝ → ℂ,
      ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f (Ioi b.rMinus) ∧
      (∀ r, f r ≠ 0) ∧
      ∀ r ∈ Ioi b.rPlus,
        radialMultiplier b m ω (-(1+3*σ)/2) r =
          ((r-b.rPlus:ℝ):ℂ)^(horizonAlpha b m ω σ)*f r := by
  apply factor_of_logarithmic_derivative b.rMinus b.rPlus
    (by linarith [b.horizon_gap,b.delta_pos]) (horizonAlpha b m ω σ)
    (radialMultiplier b m ω (-(1+3*σ)/2)) (multiplierRegularPart b m ω σ)
    (multiplierRegularPart_smooth b m ω σ)
    (fun _ hr => radialMultiplier_ne_zero b m ω _ hr)
  intro r hr
  convert radialMultiplier_hasDerivAt b m ω (-(1+3*σ)/2) hr using 1
  rw [multiplier_logarithmic_split b m ω σ hr]

end KN.Boundary
