import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace KN

/-- All signed, strictly subextremal Kerr–Newman backgrounds. -/
structure Background where
  M : ℝ
  a : ℝ
  Q : ℝ
  mass_pos : 0 < M
  subextremal : a ^ 2 + Q ^ 2 < M ^ 2

namespace Background
noncomputable def delta (b : Background) : ℝ := Real.sqrt (b.M ^ 2 - b.a ^ 2 - b.Q ^ 2)
def d (b : Background) : ℝ := b.M ^ 2 - b.Q ^ 2
noncomputable def rPlus (b : Background) : ℝ := b.M + b.delta
noncomputable def rMinus (b : Background) : ℝ := b.M - b.delta
def Delta (b : Background) (r : ℝ) : ℝ := r ^ 2 - 2 * b.M * r + b.a ^ 2 + b.Q ^ 2
def eta (b : Background) : ℝ := 2 * b.Q ^ 2 / b.d
def h (b : Background) : ℝ := b.eta + 2
def kappa (b : Background) : ℝ := b.eta + 1
def c (b : Background) : ℝ := 2 * b.M * b.Q / b.d
def beta (b : Background) : ℝ := 3 * b.M / (2 * b.Q)

theorem discriminant_pos (b : Background) : 0 < b.M ^ 2 - b.a ^ 2 - b.Q ^ 2 := by
  linarith [b.subextremal]
theorem delta_pos (b : Background) : 0 < b.delta := Real.sqrt_pos.2 b.discriminant_pos
theorem delta_sq (b : Background) : b.delta ^ 2 = b.M ^ 2 - b.a ^ 2 - b.Q ^ 2 :=
  Real.sq_sqrt (le_of_lt b.discriminant_pos)
theorem d_pos (b : Background) : 0 < b.d := by
  dsimp [d]; nlinarith [b.subextremal, sq_nonneg b.a]
theorem d_ne (b : Background) : b.d ≠ 0 := ne_of_gt b.d_pos
theorem rPlus_pos (b : Background) : 0 < b.rPlus := add_pos b.mass_pos b.delta_pos
theorem horizon_gap (b : Background) : b.rPlus - b.rMinus = 2 * b.delta := by
  simp [rPlus, rMinus]; ring
theorem delta_factor (b : Background) (r : ℝ) :
    b.Delta r = (r - b.rPlus) * (r - b.rMinus) := by
  dsimp [Delta, rPlus, rMinus]; nlinarith [b.delta_sq]
theorem Delta_pos (b : Background) {r : ℝ} (hr : b.rPlus < r) : 0 < b.Delta r := by
  rw [b.delta_factor]
  have hm : b.rMinus < b.rPlus := by
    have := b.horizon_gap; linarith [b.delta_pos]
  exact mul_pos (sub_pos.2 hr) (sub_pos.2 (lt_trans hm hr))
theorem eta_nonneg (b : Background) : 0 ≤ b.eta := by
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (le_of_lt b.d_pos)
theorem h_pos (b : Background) : 0 < b.h := by
  dsimp [h]; linarith [b.eta_nonneg]
theorem h_eq (b : Background) : b.h = 2 * b.M ^ 2 / b.d := by
  dsimp [h, eta]; field_simp [b.d_ne]; dsimp [d]; ring
theorem kappa_eq (b : Background) : b.kappa = (b.M ^ 2 + b.Q ^ 2) / b.d := by
  dsimp [kappa, eta]; field_simp [b.d_ne]; dsimp [d]; ring
/-- Equation (1), with no sign restriction on the charge. -/
theorem kappa_sq_sub_c_sq (b : Background) : b.kappa ^ 2 - b.c ^ 2 = 1 := by
  rw [b.kappa_eq]; dsimp [c]; field_simp [b.d_ne]; dsimp [d]; ring
theorem beta_mul_c (b : Background) (hQ : b.Q ≠ 0) : b.beta * b.c = 3 * b.h / 2 := by
  rw [b.h_eq]; dsimp [beta, c]; field_simp [hQ, b.d_ne]

def frequencyK (b : Background) (m : ℤ) (ω : ℂ) (r : ℝ) : ℂ :=
  -((r : ℂ) ^ 2 + (b.a : ℂ) ^ 2) * ω + (b.a : ℂ) * m

theorem uhpfrequency_ne_zero {ω : ℂ} (hω : 0 < ω.im) : ω ≠ 0 := by
  intro he; subst ω; simp at hω

end Background
end KN
