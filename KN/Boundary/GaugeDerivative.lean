import KN.Boundary.Radial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

noncomputable section
open Set MeasureTheory
namespace KN.Boundary

def gaugeIntegrand (b : Background) (m : ℤ) (ω : ℂ) (r : ℝ) : ℂ :=
  b.frequencyK m ω r / (b.Delta r : ℂ)

theorem gaugeIntegrand_continuousOn (b : Background) (m : ℤ) (ω : ℂ) :
    ContinuousOn (gaugeIntegrand b m ω) (Ioi b.rPlus) := by
  unfold gaugeIntegrand
  apply ContinuousOn.div
  · unfold Background.frequencyK; fun_prop
  · unfold Background.Delta; fun_prop
  · intro r hr
    exact_mod_cast ne_of_gt (b.Delta_pos hr)

theorem gauge_hasDerivAt (b : Background) (m : ℤ) (ω : ℂ) {r : ℝ}
    (hr : b.rPlus < r) :
    HasDerivAt (gauge b m ω)
      (gauge b m ω r * (Complex.I * b.frequencyK m ω r / (b.Delta r : ℂ))) r := by
  have hsub : uIcc (2*b.rPlus) r ⊆ Ioi b.rPlus := by
    intro x hx
    change min (2*b.rPlus) r ≤ x ∧ x ≤ max (2*b.rPlus) r at hx
    have hmin : b.rPlus < min (2*b.rPlus) r := lt_min (by linarith [b.rPlus_pos]) hr
    exact lt_of_lt_of_le hmin hx.1
  have hc := gaugeIntegrand_continuousOn b m ω
  have hi : IntervalIntegrable (gaugeIntegrand b m ω) volume (2*b.rPlus) r :=
    (hc.mono hsub).intervalIntegrable
  have ha : ContinuousAt (gaugeIntegrand b m ω) r := hc.continuousAt (Ioi_mem_nhds hr)
  have hm : Measurable (gaugeIntegrand b m ω) := by
    unfold gaugeIntegrand Background.frequencyK Background.Delta
    fun_prop
  have hd := intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurable.stronglyMeasurableAtFilter ha
  convert (hd.const_mul Complex.I).cexp using 1 <;> simp only [gauge, gaugeIntegrand, mul_div_assoc]; rfl

 theorem delta_hasDerivAt (b : Background) (r : ℝ) :
    HasDerivAt b.Delta (2*r-2*b.M) r := by
  convert ((((hasDerivAt_id r).pow 2).sub ((hasDerivAt_id r).const_mul (2*b.M))).add_const
    (b.a^2)).add_const (b.Q^2) using 1
  · funext x; dsimp [Background.Delta]
  · simp

theorem delta_rpow_hasDerivAt (b : Background) (q : ℝ) {r : ℝ} (hr : b.rPlus < r) :
    HasDerivAt (fun x => Real.rpow (b.Delta x) q)
      (q * Real.rpow (b.Delta r) (q-1) * (2*r-2*b.M)) r := by
  change HasDerivAt (fun x => b.Delta x ^ q)
    (q * b.Delta r ^ (q-1) * (2*r-2*b.M)) r
  convert (delta_hasDerivAt b r).rpow_const (p := q) (Or.inl (ne_of_gt (b.Delta_pos hr))) using 1; ring

end KN.Boundary
