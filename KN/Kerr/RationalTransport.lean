import KN.Background.Parameters

namespace KN.Kerr

/-- The affine remainder when dividing K by Δ. -/
noncomputable def frequencyRemainder (b : KN.Background) (m : ℤ) (omega : ℂ) (r : ℝ) : ℂ :=
  -2 * b.M * omega * r + (b.Q : ℂ)^2 * omega + b.a * m

noncomputable def transportResiduePlus (b : KN.Background) (m : ℤ) (omega : ℂ) : ℂ :=
  frequencyRemainder b m omega b.rPlus / (b.rPlus - b.rMinus : ℝ)
noncomputable def transportResidueMinus (b : KN.Background) (m : ℤ) (omega : ℂ) : ℂ :=
  -frequencyRemainder b m omega b.rMinus / (b.rPlus - b.rMinus : ℝ)

/-- Exact partial fractions for H'/H, valid for either sign of a and Q. -/
theorem frequencyK_partial_fractions (b : KN.Background) (m : ℤ) (omega : ℂ)
    {r : ℝ} (hr : b.rPlus < r) :
    b.frequencyK m omega r / (b.Delta r : ℂ) = -omega +
      transportResiduePlus b m omega / (r - b.rPlus : ℝ) +
      transportResidueMinus b m omega / (r - b.rMinus : ℝ) := by
  have hgap : b.rPlus - b.rMinus ≠ 0 := by
    rw [b.horizon_gap]
    exact mul_ne_zero (by norm_num) (ne_of_gt b.delta_pos)
  have hm : b.rMinus < b.rPlus := by linarith [b.horizon_gap, b.delta_pos]
  have hp : (r - b.rPlus : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  have hn : (r - b.rMinus : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hm hr))
  have hcGap : ((b.rPlus - b.rMinus : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgap
  have hcP : ((r - b.rPlus : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp
  have hcN : ((r - b.rMinus : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hrem : b.frequencyK m omega r = -omega * (b.Delta r : ℂ) + frequencyRemainder b m omega r := by
    unfold Background.frequencyK Background.Delta frequencyRemainder
    push_cast
    ring
  rw [hrem, b.delta_factor]
  unfold transportResiduePlus transportResidueMinus frequencyRemainder
  push_cast at *
  field_simp
  ring

end KN.Kerr
