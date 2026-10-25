import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section
namespace KN.ChargedRadial

def muPlus (eta x : ℝ) := 1/(x^2*(x+eta)^3)
def muMinus (eta x : ℝ) := (x+eta)^3/x^2
def weightPPlus (eta h x : ℝ) := (x+h)/(x*(x+eta)^2)
def weightPMinus (eta h x : ℝ) := (x+h)*(x+eta)^4/x
def weightWPlus (eta x : ℝ) := 1/(x*(x+eta)^3)
def weightWMinus (eta x : ℝ) := (x+eta)^3/x
def weightQPlus (M eta x : ℝ) := M/(x*(x+eta))
def weightQMinus (M eta x : ℝ) := M*(x+eta)^5/x

theorem weightPPlus_hasDerivAt (eta h x : ℝ) (hx : x ≠ 0) (he : x+eta ≠ 0) :
    HasDerivAt (weightPPlus eta h)
      (muPlus eta x*(x^2-eta*h-3*x*(x+h))) x := by
  convert ((hasDerivAt_id x).add_const h).div
    ((hasDerivAt_id x).mul (((hasDerivAt_id x).add_const eta).pow 2))
    (mul_ne_zero hx (pow_ne_zero 2 he)) using 1
  · rfl
  · dsimp [muPlus]
    field_simp
    all_goals ring

theorem weightPMinus_hasDerivAt (eta h x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (weightPMinus eta h)
      (muMinus eta x*(x^2-eta*h+3*x*(x+h))) x := by
  convert (((hasDerivAt_id x).add_const h).mul
    (((hasDerivAt_id x).add_const eta).pow 4)).div (hasDerivAt_id x) hx using 1
  · rfl
  · dsimp [muMinus]
    field_simp
    all_goals ring

theorem weightQPlus_hasDerivAt (M eta x : ℝ) (hx : x ≠ 0) (he : x+eta ≠ 0) :
    HasDerivAt (weightQPlus M eta)
      (muPlus eta x*(M*(x+eta)*(x-eta-3*x))) x := by
  convert (hasDerivAt_const x M).div
    ((hasDerivAt_id x).mul ((hasDerivAt_id x).add_const eta))
    (mul_ne_zero hx he) using 1
  · rfl
  · dsimp [muPlus]
    field_simp
    all_goals ring

theorem weightQMinus_hasDerivAt (M eta x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (weightQMinus M eta)
      (muMinus eta x*(M*(x+eta)*(x-eta+3*x))) x := by
  convert ((((hasDerivAt_id x).add_const eta).pow 5).const_mul M).div
    (hasDerivAt_id x) hx using 1
  · rfl
  · dsimp [muMinus]
    field_simp
    all_goals ring

/-- Both positive integration weights, with no assumption that spin or charge is positive. -/
theorem weight_signs (eta x : ℝ) (he : 0 ≤ eta) (hx : x < -(eta+2)) :
    0 < weightPPlus eta (eta+2) x ∧ 0 < weightPMinus eta (eta+2) x ∧
    0 < weightWPlus eta x ∧ 0 < weightWMinus eta x := by
  have hxn : x < 0 := by linarith
  have hen : x+eta < 0 := by linarith
  have hhn : x+(eta+2) < 0 := by linarith
  have he2 : 0 < (x+eta)^2 := sq_pos_of_ne_zero (ne_of_lt hen)
  have he4 : 0 < (x+eta)^4 := pow_pos (neg_pos.mpr hen) 4 |>.trans_eq (by ring)
  have he3 : (x+eta)^3 < 0 := by nlinarith [mul_neg_of_pos_of_neg he2 hen]
  dsimp [weightPPlus, weightPMinus, weightWPlus, weightWMinus]
  exact ⟨div_pos_of_neg_of_neg hhn (mul_neg_of_neg_of_pos hxn he2),
    div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hhn he4) hxn,
    div_pos (by norm_num) (mul_pos_of_neg_of_neg hxn he3),
    div_pos_of_neg_of_neg he3 hxn⟩

theorem weight_algebra_plus (M eta h x : ℝ) (hx : x ≠ 0) (he : x+eta ≠ 0)
    (hh : x+h ≠ 0) :
    muPlus eta x*(x*(x+eta)*(x+h)) = weightPPlus eta h x ∧
    muPlus eta x*x = weightWPlus eta x ∧
    muPlus eta x*(2*M*x*(x+eta)^2) = 2*weightQPlus M eta x ∧
    weightQPlus M eta x/weightPPlus eta h x = M*(x+eta)/(x+h) := by
  dsimp [muPlus, weightPPlus, weightWPlus, weightQPlus]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp

theorem weight_algebra_minus (M eta h x : ℝ) (hx : x ≠ 0) (he : x+eta ≠ 0)
    (hh : x+h ≠ 0) :
    muMinus eta x*(x*(x+eta)*(x+h)) = weightPMinus eta h x ∧
    muMinus eta x*x = weightWMinus eta x ∧
    muMinus eta x*(2*M*x*(x+eta)^2) = 2*weightQMinus M eta x ∧
    weightQMinus M eta x/weightPMinus eta h x = M*(x+eta)/(x+h) := by
  dsimp [muMinus, weightPMinus, weightWMinus, weightQMinus]
  constructor
  · field_simp
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp

/-- The real gauge primitive has the precise logarithmic coefficient 2M. -/
def gaugePhase (M eta x : ℝ) := M*(x-2*Real.log (-x-(eta+2)))

theorem gaugePhase_hasDerivAt (M eta x : ℝ) (hx : x < -(eta+2)) :
    HasDerivAt (gaugePhase M eta) (M*(x+eta)/(x+eta+2)) x := by
  have hn : -x-(eta+2) ≠ 0 := by linarith
  convert ((hasDerivAt_id x).sub
    ((((hasDerivAt_id x).neg.sub_const (eta+2)).log hn).const_mul 2)).const_mul M using 1
  · rfl
  · dsimp
    field_simp [hn, show x+eta+2 ≠ 0 by linarith]
    all_goals ring

/-- Completion of the gauge square gives the exact potential R in (44). -/
theorem gauge_potential_identity (M a Q eta x : ℝ) (hx : x+eta+2 ≠ 0) :
    -(2*a^2+(a^2+Q^2)*(x+2*eta))*x-Q^2*eta^2+
      M^2*(x+eta)^3/(x+eta+2) =
    (x+eta)^2*(M^2-a^2-Q^2-2*M^2/(x+eta+2))+a^2*eta^2-2*a^2*x := by
  field_simp
  ring

end KN.ChargedRadial
