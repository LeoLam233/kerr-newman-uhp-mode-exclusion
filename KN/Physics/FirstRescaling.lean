import KN.Boundary.RescaleFactor

noncomputable section
namespace KN.Physics

/-- Differential cancellation underlying both signs of (24)→(26). -/
theorem first_rescaling_algebra (F G t q d IK A B y z : ℂ) (ht : t ≠ 0) (hF : F=t*G) :
    (F*(q*d/t^2-IK/t^2))*y + F*((-q*d/t^2+IK/t^2)*y+A/t*z) = A*(G*z) ∧
    t^2*((G*((q-1/2)*d/t^2-IK/t^2))*z + G*((q*d/t^2-IK/t^2)*z+B/t*y)) +
      ((1/2-2*q)*d+2*IK)*(G*z) = B*(F*y) := by
  rw [hF]
  constructor <;> field_simp <;> ring

/-- Actual derivative version, with coefficients constrained only by their actual derivatives. -/
theorem first_rescaling_differential (F G y z : ℝ → ℂ) (t q d IK A B : ℂ) {r : ℝ}
    (ht : t ≠ 0) (hFG : F r=t*G r)
    (hF : HasDerivAt F (F r*(q*d/t^2-IK/t^2)) r)
    (hG : HasDerivAt G (G r*((q-1/2)*d/t^2-IK/t^2)) r)
    (hy : HasDerivAt y ((-q*d/t^2+IK/t^2)*y r+A/t*z r) r)
    (hz : HasDerivAt z ((q*d/t^2-IK/t^2)*z r+B/t*y r) r) :
    deriv (fun x => F x*y x) r = A*(G r*z r) ∧
    t^2*deriv (fun x => G x*z x) r + ((1/2-2*q)*d+2*IK)*(G r*z r) = B*(F r*y r) := by
  rw [(hF.fun_mul hy).deriv, (hG.fun_mul hz).deriv]
  exact first_rescaling_algebra (F r) (G r) t q d IK A B (y r) (z r) ht hFG

/-- Specialization to the actual C002 radial factors and selected two-component pair.
The displayed source equations are the two cases of (24) in the selected component order. -/
theorem actual_first_rescaling (b : KN.Background) (m : ℤ) (ω : ℂ) (σ : ℝ)
    (y z : ℝ → ℂ) {r : ℝ} (hr : b.rPlus < r) (A B : ℂ)
    (hy : HasDerivAt y
      ((-(3*(σ:ℂ)/4)*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ) +
        Complex.I*(b.frequencyK m ω r-(b.eta:ℂ)*ω*(b.Delta r:ℂ))/(b.Delta r:ℂ))*y r +
        A/(Real.sqrt (b.Delta r):ℂ)*z r) r)
    (hz : HasDerivAt z
      (((3*(σ:ℂ)/4)*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ) -
        Complex.I*(b.frequencyK m ω r-(b.eta:ℂ)*ω*(b.Delta r:ℂ))/(b.Delta r:ℂ))*z r +
        B/(Real.sqrt (b.Delta r):ℂ)*y r) r) :
    let F := KN.Boundary.rescaleFactor b m ω (3*σ/4)
    let G := KN.Boundary.rescaleFactor b m ω (3*σ/4-1/2)
    deriv (fun x => F x*y x) r = A*(G r*z r) ∧
    (b.Delta r:ℂ)*deriv (fun x => G x*z x) r +
      (((1-3*(σ:ℂ))/2)*(2*(r:ℂ)-2*b.M) +
        2*Complex.I*(b.frequencyK m ω r-(b.eta:ℂ)*ω*(b.Delta r:ℂ)))*(G r*z r) =
      B*(F r*y r) := by
  let F := KN.Boundary.rescaleFactor b m ω (3*σ/4)
  let G := KN.Boundary.rescaleFactor b m ω (3*σ/4-1/2)
  let t : ℂ := Real.sqrt (b.Delta r)
  let IK : ℂ := Complex.I*(b.frequencyK m ω r-(b.eta:ℂ)*ω*(b.Delta r:ℂ))
  have ht : t ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  have ht2 : t^2=(b.Delta r:ℂ) := by
    dsimp [t]; norm_cast; exact Real.sq_sqrt (le_of_lt (b.Delta_pos hr))
  have hd : (b.Delta r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (b.Delta_pos hr))
  have hFG : F r=t*G r := by
    have hh := KN.Boundary.rescaleFactor_sqrt_shift b m ω (3*σ/4) hr
    change F r/t=G r at hh
    exact (div_eq_iff ht).mp hh |>.trans (mul_comm _ _)
  have hF : HasDerivAt F (F r*((3*(σ:ℂ)/4)*(2*(r:ℂ)-2*b.M)/t^2-IK/t^2)) r := by
    convert KN.Boundary.rescaleFactor_hasDerivAt b m ω (3*σ/4) hr using 1
    rw [ht2]; dsimp [IK,F]; push_cast; field_simp; ring
  have hG : HasDerivAt G (G r*((3*(σ:ℂ)/4-1/2)*(2*(r:ℂ)-2*b.M)/t^2-IK/t^2)) r := by
    convert KN.Boundary.rescaleFactor_hasDerivAt b m ω (3*σ/4-1/2) hr using 1
    rw [ht2]; dsimp [IK,G]; push_cast; field_simp; ring
  have hy' : HasDerivAt y ((-(3*(σ:ℂ)/4)*(2*(r:ℂ)-2*b.M)/t^2+IK/t^2)*y r+A/t*z r) r := by
    simpa only [ht2] using hy
  have hz' : HasDerivAt z (((3*(σ:ℂ)/4)*(2*(r:ℂ)-2*b.M)/t^2-IK/t^2)*z r+B/t*y r) r := by
    simpa only [ht2] using hz
  have hh := first_rescaling_differential F G y z t (3*(σ:ℂ)/4)
    (2*(r:ℂ)-2*b.M) IK A B ht hFG hF hG hy' hz'
  rw [ht2] at hh
  have hc : (1/2-2*(3*(σ:ℂ)/4))=(1-3*(σ:ℂ))/2 := by ring
  rw [hc] at hh
  simpa only [IK, mul_assoc] using hh

end KN.Physics
