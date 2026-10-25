import KN.Background.Parameters
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
namespace KN.ChargedRadial
open KN

def horizonBPlus (b : Background) : ℝ := b.rPlus^2+b.a^2
def horizonG (b : Background) : ℝ := 2*b.Q*(b.M*b.rPlus-b.Q^2)/b.d

theorem horizonBPlus_pos (b : Background) : 0 < horizonBPlus b := by
  dsimp [horizonBPlus]
  nlinarith [b.rPlus_pos, sq_nonneg b.a]

theorem horizon_square_identity (b : Background) :
    horizonG b ^ 2 + b.a^2*b.kappa^2 = b.a^2+4*b.Q^2*horizonBPlus b/b.d := by
  rw [b.kappa_eq]
  unfold horizonG horizonBPlus Background.rPlus
  field_simp [b.d_ne]
  ring_nf
  rw [b.delta_sq]
  dsimp [Background.d]
  ring

/-- Exact exceptional-horizon identity (34), valid for either sign of charge. -/
theorem horizon_gap_identity (b : Background) (hQ : b.Q ≠ 0) :
    2*b.beta*horizonG b - (b.delta/horizonBPlus b)*
      (horizonG b^2+b.a^2*b.kappa^2) =
    6*b.M+b.delta*((6*b.M^2-4*b.Q^2)/b.d-b.a^2/horizonBPlus b) := by
  rw [horizon_square_identity]
  unfold horizonG Background.beta Background.rPlus
  field_simp [b.d_ne, ne_of_gt (horizonBPlus_pos b), hQ]
  dsimp [Background.d]
  ring

theorem horizon_gap_pos (b : Background) (hQ : b.Q ≠ 0) :
    0 < 2*b.beta*horizonG b - (b.delta/horizonBPlus b)*
      (horizonG b^2+b.a^2*b.kappa^2) := by
  rw [horizon_gap_identity b hQ]
  have hr : b.a^2 / horizonBPlus b < 1 := by
    apply (div_lt_one (horizonBPlus_pos b)).2
    dsimp [horizonBPlus]
    nlinarith [b.rPlus_pos]
  have hd : 6 ≤ (6*b.M^2-4*b.Q^2)/b.d := by
    apply (le_div_iff₀ b.d_pos).2
    dsimp [Background.d]
    nlinarith [sq_nonneg b.Q]
  have hp : 0 < (6*b.M^2-4*b.Q^2)/b.d-b.a^2/horizonBPlus b := by linarith
  exact add_pos (by linarith [b.mass_pos]) (mul_pos b.delta_pos hp)

/-- Algebraic contradiction underlying (33). It uses both genuine angular
identities and a strictly positive exceptional-horizon gap, without assuming λ real. -/
theorem exceptional_angular_contradiction
    (omega lam : ℂ) (beta G T C D Dmax : ℝ)
    (hw : 0 < omega.im) (hT : 0 ≤ T) (hD : D ≤ Dmax)
    (hgap : 0 < 2*beta*G-omega.im*(G^2+Dmax))
    (hlam : lam = (beta:ℂ)+Complex.I*(G:ℂ)*omega)
    (hangular : lam^2 = (beta:ℂ)^2+(T:ℂ)+omega*(C:ℂ)+omega^2*(D:ℂ)) : False := by
  have he : (T:ℂ)+omega*(C:ℂ)+omega^2*((D:ℂ)+(G:ℂ)^2)-
      2*Complex.I*(beta:ℂ)*(G:ℂ)*omega = 0 := by
    rw [hlam] at hangular
    linear_combination -hangular + omega^2*(G:ℂ)^2*Complex.I_sq
  have hi := congrArg Complex.im (congrArg (fun z : ℂ => star omega*z) he)
  simp only [Complex.star_def] at hi
  norm_num [Complex.mul_im, Complex.mul_re, pow_two] at hi
  have hn : 0 < omega.re^2+omega.im^2 := by nlinarith [sq_nonneg omega.re]
  have hstrict : omega.im*(G^2+D)-2*beta*G < 0 := by
    nlinarith [mul_nonneg (le_of_lt hw) (sub_nonneg.mpr hD)]
  have hprod := mul_neg_of_pos_of_neg hn hstrict
  have hnonneg := mul_nonneg (le_of_lt hw) hT
  nlinarith [hi]

/-- Nonvanishing of the horizon coupling at the exceptional positive-spin
frequency, derived from the actual angular identities and background, equation (33). -/
theorem exceptional_coupling_nonzero
    (b : Background) (hQ : b.Q ≠ 0) (omega lam : ℂ) (T C D : ℝ)
    (him : omega.im = b.delta / horizonBPlus b)
    (hT : 0 ≤ T) (hD : D ≤ b.a^2*b.kappa^2)
    (hangular : lam^2 = (b.beta:ℂ)^2+(T:ℂ)+omega*(C:ℂ)+omega^2*(D:ℂ)) :
    -(horizonG b:ℂ)*omega+Complex.I*(b.beta:ℂ)-Complex.I*lam ≠ 0 := by
  intro hzero
  have hlam : lam = (b.beta:ℂ)+Complex.I*(horizonG b:ℂ)*omega := by
    linear_combination (norm := ring_nf) Complex.I*hzero
    simp [Complex.I_sq]
  have hw : 0 < omega.im := by
    rw [him]
    exact div_pos b.delta_pos (horizonBPlus_pos b)
  have hgap : 0 < 2*b.beta*horizonG b-omega.im*(horizonG b^2+b.a^2*b.kappa^2) := by
    rw [him]
    exact horizon_gap_pos b hQ
  exact exceptional_angular_contradiction omega lam b.beta (horizonG b) T C D
    (b.a^2*b.kappa^2) hw hT hD hgap hlam hangular

end KN.ChargedRadial
