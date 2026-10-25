import KN.Energy.Current
import KN.Energy.Integral

open MeasureTheory Filter Set
open scoped Topology
namespace KN.Energy

noncomputable def density (ω : ℂ) (P W k B : ℝ → ℝ) (U V : ℝ → ℂ) (x : ℝ) : ℝ :=
  P x*Complex.normSq (V x) + W x*k x*Complex.normSq (U x) +
    Complex.normSq ω*W x*B x*Complex.normSq (U x)

/-- The analytic energy argument on the actual half-line. No integrated
identity or exclusion hypothesis is assumed: differentiation and improper
integration establish the identity, and strict positivity gives pointwise
vanishing. Endpoint estimates must supply the three explicit analytic inputs
`hi`, `hb`, `hbot`; these are not hidden inside a mode definition. -/
theorem divergence_ODE_vanishes (ω : ℂ) (hω : 0 < ω.im)
    (P W k l B : ℝ → ℝ) (U V : ℝ → ℂ) (b : ℝ)
    (hU : ∀ x < b, HasDerivAt U (V x) x)
    (hV : ∀ x < b, HasDerivAt (fun y => (P y : ℂ)*V y)
      ((W x : ℂ)*(k x-ω*l x-ω^2*B x)*U x) x)
    (hP : ∀ x < b, 0 ≤ P x) (hW : ∀ x < b, 0 < W x)
    (hk : ∀ x < b, 0 ≤ k x) (hB : ∀ x < b, 0 < B x)
    (hi : IntegrableOn (density ω P W k B U V) (Iio b))
    (hb : Tendsto (current ω P U V) (𝓝[<] b) (𝓝 0))
    (hbot : Tendsto (current ω P U V) atBot (𝓝 0)) :
    ∀ x < b, U x = 0 := by
  have hd : ∀ x < b, HasDerivAt (current ω P U V)
      (-ω.im * density ω P W k B U V x) x := by
    intro x hx
    exact current_hasDerivAt ω P W k l B U V x (hU x hx) (hV x hx)
  have hz := integral_Iio_derivative_zero hd (hi.const_mul (-ω.im)) hb hbot
  rw [integral_const_mul] at hz
  have hz' : ∫ x in Iio b, density ω P W k B U V x = 0 :=
    (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr (ne_of_gt hω))
  have hp : 0 ≤ᵐ[volume.restrict (Iio b)] density ω P W k B U V := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
    dsimp [density]
    positivity [hP x hx, hW x hx, hk x hx, hB x hx, Complex.normSq_nonneg (V x),
      Complex.normSq_nonneg (U x), Complex.normSq_nonneg ω]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hp hi).mp hz'
  have hωn : 0 < Complex.normSq ω := Complex.normSq_pos.mpr (by
    intro he
    simp [he] at hω)
  have hu : U =ᵐ[volume.restrict (Iio b)] 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Iio] with x hx hxb
    have hpv := mul_nonneg (hP x hxb) (Complex.normSq_nonneg (V x))
    have hku := mul_nonneg (mul_nonneg (hW x hxb).le (hk x hxb)) (Complex.normSq_nonneg (U x))
    have hbw : 0 < Complex.normSq ω * W x * B x := mul_pos (mul_pos hωn (hW x hxb)) (hB x hxb)
    have hnu := Complex.normSq_nonneg (U x)
    have hn : Complex.normSq (U x) = 0 := by
      dsimp [density] at hx
      nlinarith
    exact Complex.normSq_eq_zero.mp hn
  exact Measure.eqOn_open_of_ae_eq hu isOpen_Iio
    (fun x hx => (hU x hx).continuousAt.continuousWithinAt) continuousOn_const

end KN.Energy
