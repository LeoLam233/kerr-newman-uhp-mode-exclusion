import KN.Energy.Gauge
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Filter Set Asymptotics
open scoped Topology
namespace KN.Energy
noncomputable def inverseGauge (ω : ℂ) (M b x : ℝ) : ℂ :=
  Complex.exp (Complex.I*ω*(M*(x-2*Real.log (b-x)) : ℝ))

/-- Exact modulus of the gauge in (42), the source of the positive horizon
power. The sign of Im ω has not been specialized in this identity. -/
theorem inverseGauge_norm (ω : ℂ) (M b x : ℝ) (hx : x < b) :
    ‖inverseGauge ω M b x‖ = Real.exp (-ω.im*M*x)*(b-x)^(2*M*ω.im) := by
  rw [inverseGauge, Complex.norm_exp, Real.rpow_def_of_pos (sub_pos.mpr hx), ← Real.exp_add]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The gauge has precisely the order in (47) at the finite endpoint. -/
theorem inverseGauge_isBigO (ω : ℂ) (M b : ℝ) :
    (inverseGauge ω M b) =O[𝓝[<] b] (fun x : ℝ => (b-x)^(2*M*ω.im)) := by
  have hc : ContinuousAt (fun x : ℝ => Real.exp (-ω.im*M*x)) b := by fun_prop
  have he : (fun x : ℝ => Real.exp (-ω.im*M*x)) =O[𝓝[<] b] (fun _ => (1:ℝ)) :=
    hc.isBigO.mono nhdsWithin_le_nhds
  have ht := he.mul (isBigO_refl (fun x : ℝ => (b-x)^(2*M*ω.im)) (𝓝[<] b))
  have ht' : (fun x : ℝ => ‖inverseGauge ω M b x‖) =O[𝓝[<] b]
      (fun x : ℝ => (b-x)^(2*M*ω.im)) := by
    refine ht.congr' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (inverseGauge_norm ω M b x hx).symm
    · exact Filter.Eventually.of_forall (fun _ => one_mul _)
  exact ht'.of_norm_left

/-- Analytic continuation of Y to the endpoint supplies continuity, hence
the first bound of (47), without any nonzero leading Taylor coefficient. -/
theorem gauged_endpoint_bound (ω : ℂ) (M b : ℝ) (Y : ℝ → ℂ)
    (hY : ContinuousAt Y b) :
    (fun x => inverseGauge ω M b x*Y x) =O[𝓝[<] b]
      (fun x : ℝ => (b-x)^(2*M*ω.im)) := by
  have hy : Y =O[𝓝[<] b] (fun _ => (1:ℝ)) := hY.isBigO.mono nhdsWithin_le_nhds
  simpa only [mul_one] using (inverseGauge_isBigO ω M b).mul hy

/-- The precise derivative of the inverse real gauge. -/
theorem inverseGauge_hasDerivAt (ω : ℂ) (M b x : ℝ) (hx : x < b) :
    HasDerivAt (inverseGauge ω M b)
      (Complex.I*ω*(M*(1+2/(b-x)) : ℝ)*inverseGauge ω M b x) x := by
  have hs : HasDerivAt (fun y : ℝ => M*(y-2*Real.log (b-y))) (M*(1+2/(b-x))) x := by
    convert ((hasDerivAt_id x).sub
      (((hasDerivAt_const x b).sub (hasDerivAt_id x)).log (ne_of_gt (sub_pos.mpr hx)) |>.const_mul 2)).const_mul M using 1
    dsimp
    simp only [Pi.sub_apply, id_eq]
    ring
  have he := (Complex.hasDerivAt_exp _).comp x (hs.ofReal_comp.const_mul (Complex.I*ω))
  convert he using 1
  · rfl
  · dsimp [inverseGauge]; ring
/-- A bounded coefficient is dominated by the simple horizon pole. -/
theorem one_isBigO_horizon_pole (b : ℝ) :
    (fun _ : ℝ => (1:ℝ)) =O[𝓝[<] b] (fun x : ℝ => 1/(b-x)) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (show b-1 < b by linarith)] with x hx
  have ht : 0 < b-x := by linarith [hx.2]
  have ht1 : b-x ≤ 1 := by linarith [hx.1]
  simpa [Real.norm_eq_abs, abs_of_pos ht] using one_le_one_div ht ht1

/-- The derivative coefficient S'=M(1+2/t) has at worst a simple pole. -/
theorem phase_derivative_isBigO (M b : ℝ) :
    (fun x : ℝ => M*(1+2/(b-x))) =O[𝓝[<] b] (fun x : ℝ => 1/(b-x)) := by
  have ht := ((one_isBigO_horizon_pole b).add
    ((isBigO_refl (fun x : ℝ => 1/(b-x)) (𝓝[<] b)).const_mul_left 2)).const_mul_left M
  convert ht using 1
  ext x
  ring

/-- The second bound of (47). Y and Y' may have vanishing endpoint Taylor
coefficients; only continuity at the endpoint is used. -/
theorem gauged_derivative_endpoint_bound (ω : ℂ) (M b : ℝ) (Y Yp : ℝ → ℂ)
    (hY : ContinuousAt Y b) (hYp : ContinuousAt Yp b) :
    (fun x => inverseGauge ω M b x *
      (Yp x+Complex.I*ω*(M*(1+2/(b-x)) : ℝ)*Y x)) =O[𝓝[<] b]
      (fun x : ℝ => (b-x)^(2*M*ω.im-1)) := by
  have hy : Y =O[𝓝[<] b] (fun _ => (1:ℝ)) := hY.isBigO.mono nhdsWithin_le_nhds
  have hyp : Yp =O[𝓝[<] b] (fun _ => (1:ℝ)) := hYp.isBigO.mono nhdsWithin_le_nhds
  have hs : (fun x : ℝ => ((M*(1+2/(b-x)):ℝ):ℂ)) =O[𝓝[<] b]
      (fun x : ℝ => 1/(b-x)) := by
    apply IsBigO.of_norm_left
    simpa only [Complex.norm_real] using (phase_derivative_isBigO M b).norm_left
  have hsy : (fun x : ℝ => Complex.I*ω*(M*(1+2/(b-x)) : ℝ)*Y x) =O[𝓝[<] b]
      (fun x : ℝ => 1/(b-x)) := by
    simpa only [mul_one] using (hs.const_mul_left (Complex.I*ω)).mul hy
  have hh := (hyp.trans (one_isBigO_horizon_pole b)).add hsy
  have h := (inverseGauge_isBigO ω M b).mul hh
  refine h.congr' Filter.EventuallyEq.rfl ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.rpow_sub (sub_pos.mpr hx), Real.rpow_one]
  ring

/-- The function estimated in the derivative bound is the actual derivative
of U = exp(iωS)Y at every point of the physical interval. -/
theorem gauged_hasDerivAt (ω : ℂ) (M b x : ℝ) (Y : ℝ → ℂ) (Yp : ℂ)
    (hx : x < b) (hY : HasDerivAt Y Yp x) :
    HasDerivAt (fun y => inverseGauge ω M b y*Y y)
      (inverseGauge ω M b x*(Yp+Complex.I*ω*(M*(1+2/(b-x)):ℝ)*Y x)) x := by
  convert (inverseGauge_hasDerivAt ω M b x hx).mul hY using 1
  ring

end KN.Energy
