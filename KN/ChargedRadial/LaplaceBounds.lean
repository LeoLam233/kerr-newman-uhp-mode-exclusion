import KN.ChargedRadial.LaplaceAdmissibility

noncomputable section
open Set MeasureTheory
namespace KN.ChargedRadial

/-- Ordinary right-sided Laplace integral, with the manuscript's Fourier sign. -/
def laplaceIntegral (r : ℝ) (h : ℝ → ℂ) (xi : ℂ) : ℂ :=
  ∫ t in Ioi r, Complex.exp (-Complex.I*xi*t)*h t

lemma laplaceKernel_norm (xi : ℂ) (t : ℝ) :
    ‖Complex.exp (-Complex.I*xi*t)‖ = Real.exp (xi.im*t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- Explicit support-edge bound from a single exponentially damped L¹ norm.
This is an integral estimate, not a presumed support-edge distribution theorem. -/
theorem laplaceIntegral_norm_bound (r beta : ℝ) (h : ℝ → ℂ) (xi : ℂ)
    (hxi : xi.im ≤ beta)
    (hi : IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*h t) (Ioi r)) :
    ‖laplaceIntegral r h xi‖ ≤ Real.exp ((xi.im-beta)*r)*
      ∫ t in Ioi r, ‖(Real.exp (beta*t):ℂ)*h t‖ := by
  have hbound : ∀ t ∈ Ioi r,
      ‖Complex.exp (-Complex.I*xi*t)*h t‖ ≤
        Real.exp ((xi.im-beta)*r)*‖(Real.exp (beta*t):ℂ)*h t‖ := by
    intro t ht
    rw [norm_mul, laplaceKernel_norm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (xi.im*t) ≤ Real.exp ((xi.im-beta)*r)*Real.exp (beta*t) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxi)
        (le_of_lt (sub_pos.mpr (show r < t from ht)))
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right he (norm_nonneg (h t))]
  have hh := norm_integral_le_of_norm_le (f := fun t : ℝ => Complex.exp (-Complex.I*xi*t)*h t) (hi.norm.const_mul (Real.exp ((xi.im-beta)*r)))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hbound))
  simpa only [laplaceIntegral, integral_const_mul] using hh

/-- Restricting ξ=ωx extracts exactly the desired e^(γ r₊ x) factor. -/
theorem laplace_ray_norm_bound (r beta : ℝ) (h : ℝ → ℂ) (omega : ℂ)
    (x : ℝ) (hx : omega.im*x ≤ beta)
    (hi : IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*h t) (Ioi r)) :
    ‖laplaceIntegral r h (omega*x)‖ ≤
      (Real.exp (-beta*r)*(∫ t in Ioi r, ‖(Real.exp (beta*t):ℂ)*h t‖))*
        Real.exp (omega.im*r*x) := by
  have hh := laplaceIntegral_norm_bound r beta h (omega*x) (by simpa using hx) hi
  convert hh using 1
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have he : Real.exp (-beta*r)*Real.exp (omega.im*r*x) =
      Real.exp ((omega.im*x-beta)*r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← he]
  ring

def laplaceNormConstant (r beta : ℝ) (h : ℝ → ℂ) : ℝ :=
  Real.exp (-beta*r)*(∫ t in Ioi r, ‖(Real.exp (beta*t):ℂ)*h t‖)

lemma laplaceNormConstant_nonneg (r beta : ℝ) (h : ℝ → ℂ) :
    0 ≤ laplaceNormConstant r beta h := by
  apply mul_nonneg (Real.exp_pos _).le
  exact integral_nonneg (fun _ => norm_nonneg _)

/-- The explicit transform expression dictated by the finite-part formula (48a). -/
def finitePartLaplace (r : ℝ) (alpha : ℂ) (h k : ℝ → ℂ) (xi : ℂ) : ℂ :=
  (alpha+1)⁻¹*(Complex.I*xi*laplaceIntegral r h xi-laplaceIntegral r k xi)

/-- A fixed exponentially damped L¹ norm gives a degree-one polynomial bound.
This proves the required support-edge estimate directly, including the singular
positive-spin finite part, without a Watson asymptotic or coefficient. -/
theorem finitePartLaplace_ray_bound (r beta : ℝ) (alpha omega : ℂ)
    (h k : ℝ → ℂ)
    (hi : IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*h t) (Ioi r))
    (ki : IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*k t) (Ioi r))
    (x : ℝ) (hx : omega.im*x ≤ beta) :
    ‖finitePartLaplace r alpha h k (omega*x)‖ ≤
      (‖(alpha+1)⁻¹‖*(‖omega‖*laplaceNormConstant r beta h+laplaceNormConstant r beta k))*
        (1+|x|)*Real.exp (omega.im*r*x) := by
  have hh := laplace_ray_norm_bound r beta h omega x hx hi
  have hk := laplace_ray_norm_bound r beta k omega x hx ki
  change ‖laplaceIntegral r h (omega*x)‖ ≤ laplaceNormConstant r beta h*Real.exp (omega.im*r*x) at hh
  change ‖laplaceIntegral r k (omega*x)‖ ≤ laplaceNormConstant r beta k*Real.exp (omega.im*r*x) at hk
  have hh0 := laplaceNormConstant_nonneg r beta h
  have hk0 := laplaceNormConstant_nonneg r beta k
  unfold finitePartLaplace
  rw [norm_mul]
  apply le_trans (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _))
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hprod := mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg omega) (abs_nonneg x))
  have he := Real.exp_pos (omega.im*r*x)
  have hn := norm_nonneg ((alpha+1)⁻¹)
  have hmain : ‖omega‖*|x| *‖laplaceIntegral r h (omega*x)‖+
      ‖laplaceIntegral r k (omega*x)‖ ≤
      (‖omega‖*laplaceNormConstant r beta h+laplaceNormConstant r beta k)*(1+|x|)*
        Real.exp (omega.im*r*x) := by
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg omega) hh0) he.le,
      mul_nonneg hk0 (mul_nonneg (abs_nonneg x) he.le)]
  nlinarith [mul_le_mul_of_nonneg_left hmain hn]

theorem finitePartLaplace_isBigO (r beta : ℝ) (alpha omega : ℂ)
    (hw : 0 < omega.im) (h k : ℝ → ℂ)
    (hi : IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*h t) (Ioi r))
    (ki : IntegrableOn (fun t : ℝ => (Real.exp (beta*t):ℂ)*k t) (Ioi r)) :
    (fun x : ℝ => finitePartLaplace r alpha h k (omega*x)) =O[Filter.atBot]
      (fun x : ℝ => (1+|x|)*Real.exp (omega.im*r*x)) := by
  apply Asymptotics.IsBigO.of_bound
    (‖(alpha+1)⁻¹‖*(‖omega‖*laplaceNormConstant r beta h+laplaceNormConstant r beta k))
  filter_upwards [Filter.eventually_le_atBot (beta/omega.im)] with x hx
  have hxi : omega.im*x ≤ beta := by
    have hh := (le_div_iff₀ hw).mp hx
    linarith
  have hh := finitePartLaplace_ray_bound r beta alpha omega h k hi ki x hxi
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)]
  simpa only [mul_assoc] using hh

end KN.ChargedRadial
