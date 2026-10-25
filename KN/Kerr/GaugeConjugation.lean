import KN.Boundary.GaugeDerivative
import KN.Kerr.Conjugation

set_option linter.unusedSimpArgs false

namespace KN.Kerr
open Set

/-- Actual ingoing conjugating factor of (53), with the manuscript's fixed gauge. -/
noncomputable def ingoingFactor (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) (r : ℝ) : ℂ :=
  KN.Boundary.gauge b m omega r * (Real.rpow (b.Delta r) (-s) : ℂ)

theorem ingoingFactor_nonzero (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) {r : ℝ} (hr : b.rPlus < r) : ingoingFactor b m omega s r ≠ 0 := by
  apply mul_ne_zero (KN.Boundary.gauge_ne_zero b m omega r)
  exact_mod_cast ne_of_gt (Real.rpow_pos_of_pos (b.Delta_pos hr) (-s))

/-- Differentiation of the actual gauge and real power gives ψ in (53). -/
theorem ingoingFactor_hasDerivAt (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) {r : ℝ} (hr : b.rPlus < r) :
    HasDerivAt (ingoingFactor b m omega s)
      (logarithmicDerivative (b.Delta r) (2 * ((r : ℂ) - b.M))
        (-b.frequencyK m omega r) s * ingoingFactor b m omega s r) r := by
  have hh := KN.Boundary.gauge_hasDerivAt b m omega hr
  have hp := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r
    (KN.Boundary.delta_rpow_hasDerivAt b (-s) hr)
  have hdn : b.Delta r ≠ 0 := ne_of_gt (b.Delta_pos hr)
  have hpow : Real.rpow (b.Delta r) (-1 - s) = Real.rpow (b.Delta r) (-s) / b.Delta r := by
    change b.Delta r ^ (-1 - s) = b.Delta r ^ (-s) / b.Delta r
    rw [show -1 - s = -s - 1 by ring, Real.rpow_sub_one hdn]
  have hpow' : Real.rpow (b.Delta r) (-s - 1) = Real.rpow (b.Delta r) (-s) / b.Delta r := by
    change b.Delta r ^ (-s - 1) = b.Delta r ^ (-s) / b.Delta r
    exact Real.rpow_sub_one hdn (-s)
  convert hh.mul hp using 1
  · rfl
  · simp only [ingoingFactor, logarithmicDerivative, Complex.ofRealCLM_apply,
      Function.comp_apply, hpow, hpow', Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_ofNat]
    ring

end KN.Kerr

namespace KN.Kerr
open Set

/-- The logarithmic derivative as an actual exterior function. -/
noncomputable def psiFunction (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) (r : ℝ) : ℂ :=
  logarithmicDerivative (b.Delta r) (2 * ((r : ℂ) - b.M))
    (-b.frequencyK m omega r) s

/-- Its derivative is the quotient-rule expression used in the exact cancellation. -/
theorem psiFunction_hasDerivAt (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) {r : ℝ} (hr : b.rPlus < r) :
    HasDerivAt (psiFunction b m omega s)
      (logarithmicDerivativePrime (b.Delta r) (2 * ((r : ℂ) - b.M))
        (-b.frequencyK m omega r) s omega r) r := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r
    (KN.Boundary.delta_hasDerivAt b r)
  have hdp : HasDerivAt (fun x : ℝ => 2 * ((x : ℂ) - b.M)) 2 r := by
    convert (Complex.ofRealCLM.hasDerivAt.sub_const (b.M : ℂ)).const_mul 2 using 1 <;> simp
  have hk : HasDerivAt (fun x => -b.frequencyK m omega x) (2 * omega * r) r := by
    convert ((((Complex.ofRealCLM.hasDerivAt (x := r)).pow 2).add_const ((b.a : ℂ)^2)).mul_const omega).sub_const
      ((b.a : ℂ) * m) using 1
    · funext x
      simp [Background.frequencyK]
      ring
    · simp
      ring
  have hdn : (b.Delta r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (b.Delta_pos hr)
  convert (((hk.const_mul Complex.I).add (hdp.const_mul (s : ℂ))).neg).div hd hdn using 1
  · rfl
  · simp only [logarithmicDerivativePrime, Complex.ofRealCLM_apply, Function.comp_apply,
      Pi.add_apply, Pi.neg_apply, Pi.mul_apply,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp
    ring

/-- The second derivative law for the actual ingoing gauge factor. -/
theorem ingoingFactor_deriv_two (b : KN.Background) (m : ℤ) (omega : ℂ)
    (s : ℝ) {r : ℝ} (hr : b.rPlus < r) :
    deriv (deriv (ingoingFactor b m omega s)) r =
      (logarithmicDerivativePrime (b.Delta r) (2 * ((r : ℂ) - b.M))
        (-b.frequencyK m omega r) s omega r +
        psiFunction b m omega s r ^ 2) * ingoingFactor b m omega s r := by
  have hlocal : deriv (ingoingFactor b m omega s) =ᶠ[nhds r]
      fun x => psiFunction b m omega s x * ingoingFactor b m omega s x := by
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact (ingoingFactor_hasDerivAt b m omega s hx).deriv
  rw [hlocal.deriv_eq]
  rw [deriv_fun_mul (psiFunction_hasDerivAt b m omega s hr).differentiableAt
    (ingoingFactor_hasDerivAt b m omega s hr).differentiableAt]
  rw [(psiFunction_hasDerivAt b m omega s hr).deriv,
    (ingoingFactor_hasDerivAt b m omega s hr).deriv]
  unfold psiFunction
  ring

end KN.Kerr
