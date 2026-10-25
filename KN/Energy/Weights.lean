import Mathlib.Tactic

namespace KN.Energy
/-- The integer-power expression (40); spelling out the two signs removes
all real-power branch ambiguities on the negative x axis. -/
noncomputable def Pplus (η x : ℝ) := (x+η+2)/(x*(x+η)^2)
noncomputable def Wplus (η x : ℝ) := 1/(x*(x+η)^3)
noncomputable def Pminus (η x : ℝ) := (x+η+2)*(x+η)^4/x
noncomputable def Wminus (η x : ℝ) := (x+η)^3/x

theorem weights_positive (η x : ℝ) (hη : 0 ≤ η) (hx : x < -(η+2)) :
    0 < Pplus η x ∧ 0 < Wplus η x ∧ 0 < Pminus η x ∧ 0 < Wminus η x := by
  have hx0 : x < 0 := by linarith
  have hxe : x+η < 0 := by linarith
  have hxh : x+η+2 < 0 := by linarith
  have h2 : 0 < (x+η)^2 := sq_pos_of_ne_zero (ne_of_lt hxe)
  have h3 : (x+η)^3 < 0 := by nlinarith [mul_neg_of_neg_of_pos hxe h2]
  have h4 : 0 < (x+η)^4 := pow_pos (neg_pos.mpr hxe) 4 |>.trans_eq (by ring)
  refine ⟨div_pos_of_neg_of_neg hxh (mul_neg_of_neg_of_pos hx0 h2),
    div_pos zero_lt_one (mul_pos_of_neg_of_neg hx0 h3),
    div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hxh h4) hx0,
    div_pos_of_neg_of_neg h3 hx0⟩
end KN.Energy
