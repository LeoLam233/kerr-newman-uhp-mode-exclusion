import KN.Energy.TailGrowth
import KN.Boundary.GaugeDerivative

noncomputable section
open Filter Set Asymptotics
namespace KN.Energy
open KN.Boundary

def outgoingTail (b : Background) (ω : ℂ) (q : ℝ) (U : ℝ → ℂ) (r : ℝ) : ℂ :=
  Complex.exp (-Complex.I*b.eta*ω*r)*(Real.rpow (b.Delta r) q:ℂ)*U r

def outgoingTailAmplitudeDeriv (b : Background) (ω : ℂ) (q : ℝ) (U : ℝ → ℂ) (r : ℝ) : ℂ :=
  (-Complex.I*b.eta*ω)*(Real.rpow (b.Delta r) q:ℂ)*U r +
    (q:ℂ)*(Real.rpow (b.Delta r) (q-1):ℂ)*(2*(r:ℂ)-2*b.M)*U r +
      (Real.rpow (b.Delta r) q:ℂ)*deriv U r

theorem outgoingTail_hasDerivAt (b : Background) (ω : ℂ) (q : ℝ) (U : ℝ → ℂ)
    (hs : ExteriorSmooth b.rPlus U) {r : ℝ} (hr : b.rPlus < r) :
    HasDerivAt (outgoingTail b ω q U)
      (Complex.exp (-Complex.I*b.eta*ω*r)*outgoingTailAmplitudeDeriv b ω q U r) r := by
  have he := ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul (-Complex.I*b.eta*ω)).cexp
  have hd := (delta_rpow_hasDerivAt b q hr).ofReal_comp
  have hu := (hs.differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hr)
  convert (he.mul hd).mul hu.hasDerivAt using 1
  · rfl
  · dsimp [outgoingTailAmplitudeDeriv]
    push_cast
    ring

theorem outgoingTail_norm (b : Background) (ω : ℂ) (q : ℝ) (U : ℝ → ℂ) (r : ℝ) :
    ‖outgoingTail b ω q U r‖ =
      Real.exp ((b.eta*ω.im)*r)*‖(Real.rpow (b.Delta r) q:ℂ)*U r‖ := by
  simp only [outgoingTail, norm_mul,Complex.norm_exp]
  have he : (-Complex.I*b.eta*ω*r).re = (b.eta*ω.im)*r := by
    simp [Complex.mul_re,Complex.mul_im]
  rw [he]
  ring

theorem outgoingTail_expPolyGrowth (b : Background) (ω : ℂ) (q : ℝ) (hq : q ≤ 1)
    (U : ℝ → ℂ) (hU : PolynomialConormal U) :
    ExpPolyGrowth (b.eta*ω.im) (outgoingTail b ω q U) := by
  apply expPolyGrowth_of_norm_exp_mul _ _ _
    (polyBound_mul (delta_rpow_polyBound b q hq) (hU 0))
  exact Filter.Eventually.of_forall (outgoingTail_norm b ω q U)

theorem outgoingTailAmplitudeDeriv_polyBound (b : Background) (ω : ℂ) (q : ℝ) (hq : q ≤ 1)
    (U : ℝ → ℂ) (hs : ExteriorSmooth b.rPlus U) (hU : PolynomialConormal U) :
    PolyBound (outgoingTailAmplitudeDeriv b ω q U) := by
  have hd := delta_rpow_polyBound b q hq
  have hd' := delta_rpow_polyBound b (q-1) (by linarith)
  have hu : PolyBound U := hU 0
  have hu' : PolyBound (deriv U) := (polynomialConormal_deriv b.rPlus U hs hU) 0
  have hlin : PolyBound (fun r : ℝ => 2*(r:ℂ)-2*b.M) := by
    have hp := polynomialConormal_polynomial (2*Polynomial.X-Polynomial.C (2*(b.M:ℂ)))
    simpa [PolyBound] using hp 0
  exact polyBound_add
    (polyBound_add (polyBound_mul (polyBound_mul (polyBound_const _) hd) hu)
      (polyBound_mul (polyBound_mul (polyBound_mul (polyBound_const _) hd') hlin) hu))
    (polyBound_mul hd hu')

theorem outgoingTail_deriv_expPolyGrowth (b : Background) (ω : ℂ) (q : ℝ) (hq : q ≤ 1)
    (U : ℝ → ℂ) (hs : ExteriorSmooth b.rPlus U) (hU : PolynomialConormal U) :
    ExpPolyGrowth (b.eta*ω.im) (deriv (outgoingTail b ω q U)) := by
  apply expPolyGrowth_of_norm_exp_mul _ _ _
    (outgoingTailAmplitudeDeriv_polyBound b ω q hq U hs hU)
  filter_upwards [eventually_gt_atTop b.rPlus] with r hr
  rw [(outgoingTail_hasDerivAt b ω q U hs hr).deriv,norm_mul,Complex.norm_exp]
  congr 2
  simp [Complex.mul_re,Complex.mul_im]

end KN.Energy
