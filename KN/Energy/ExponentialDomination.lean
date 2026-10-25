import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter Asymptotics
namespace KN.Energy

/-- Polynomial factors in (48) are absorbed by spending half of the strictly
positive exponential decay rate. This includes arbitrary polynomial degree. -/
theorem polynomial_exponential_domination (N : ℕ) (k : ℝ) (hk : 0 < k) :
    (fun x : ℝ => (1+|x|)^N * Real.exp (2*k*x)) =O[atBot]
      (fun x : ℝ => Real.exp (k*x)) := by
  have ht : Tendsto (fun x : ℝ => 1-x) atBot atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_lt_atBot (1-b)] with x hx
    linarith
  have ho := (isLittleO_exp_mul_rpow_of_lt (N:ℝ)
    (show -2*k < -k by linarith)).comp_tendsto ht
  have heq : (fun x : ℝ => Real.exp (-2*k*(1-x)) * (1-x)^(N:ℝ)) =
      (fun x : ℝ => Real.exp (-2*k) * ((1-x)^N * Real.exp (2*k*x))) := by
    funext x
    rw [show -2*k*(1-x) = -2*k+2*k*x by ring, Real.exp_add, Real.rpow_natCast]
    ring
  have heq' : (fun x : ℝ => Real.exp (-k*(1-x))) =
      (fun x : ℝ => Real.exp (-k)*Real.exp (k*x)) := by
    funext x
    rw [show -k*(1-x) = -k+k*x by ring, Real.exp_add]
  change (fun x : ℝ => Real.exp (-2*k*(1-x)) * (1-x)^(N:ℝ)) =o[atBot]
    (fun x : ℝ => Real.exp (-k*(1-x))) at ho
  rw [heq, heq'] at ho
  have ho' := (isLittleO_const_mul_left_iff (Real.exp_ne_zero (-2*k))).mp ho
  have hb := ho'.of_const_mul_right.isBigO
  refine hb.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
  rw [abs_of_nonpos hx]
  rfl
end KN.Energy
