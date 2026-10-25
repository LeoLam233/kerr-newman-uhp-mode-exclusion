import KN.Energy.Vanishing
import KN.Energy.Injectivity
import KN.Background.Parameters

open MeasureTheory Filter Set
open scoped Topology
namespace KN.Energy

/-- The ray (37) is strictly inside the Fourier--Laplace half-plane (36). -/
theorem physical_ray_in_halfplane (b : KN.Background) (ω : ℂ) (hω : 0 < ω.im)
    (x : ℝ) (hx : x < -b.h) : (ω*(x:ℂ)).im < -b.eta*ω.im := by
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hxη : x < -b.eta := by dsimp [KN.Background.h] at hx; linarith
  nlinarith

/-- The energy argument and holomorphic uniqueness, with the actual
Fourier--Laplace ray and KN half-plane. Gauge matching is stated as an
identity, rather than presuming nonzero values of a transformed solution. -/
theorem transformed_field_zero (bg : KN.Background) (ω : ℂ) (hω : 0 < ω.im)
    (P W k l B : ℝ → ℝ) (U V gauge : ℝ → ℂ) (F : ℂ → ℂ)
    (hU : ∀ x < -bg.h, HasDerivAt U (V x) x)
    (hV : ∀ x < -bg.h, HasDerivAt (fun y => (P y : ℂ)*V y)
      ((W x : ℂ)*(k x-ω*l x-ω^2*B x)*U x) x)
    (hP : ∀ x < -bg.h, 0 ≤ P x) (hW : ∀ x < -bg.h, 0 < W x)
    (hk : ∀ x < -bg.h, 0 ≤ k x) (hB : ∀ x < -bg.h, 0 < B x)
    (hi : IntegrableOn (density ω P W k B U V) (Iio (-bg.h)))
    (hb : Tendsto (current ω P U V) (𝓝[<] (-bg.h)) (𝓝 0))
    (hbot : Tendsto (current ω P U V) atBot (𝓝 0))
    (hF : AnalyticOnNhd ℂ F {z | z.im < -bg.eta*ω.im})
    (hmatch : ∀ x < -bg.h, F (ω*(x:ℂ)) = gauge x * U x) :
    ∀ z : ℂ, z.im < -bg.eta*ω.im → F z = 0 := by
  have hzero := divergence_ODE_vanishes ω hω P W k l B U V (-bg.h)
    hU hV hP hW hk hB hi hb hbot
  apply holomorphic_zero_of_ray F ω (-bg.h) (-bg.eta*ω.im)
    (KN.Background.uhpfrequency_ne_zero hω) hF (physical_ray_in_halfplane bg ω hω)
  intro x hx
  rw [hmatch x hx, hzero x hx, mul_zero]
end KN.Energy
