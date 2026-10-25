import KN.Analysis.WeylTransform
import KN.ChargedRadial.OrderedSubstitution
import KN.ChargedRadial.TransformEndpointBounds

noncomputable section
open Set Filter Topology
namespace KN.Energy
open KN.ChargedRadial

theorem fourier_linear_factor_derivative_at (F : ℂ → ℂ) (xi : ℂ)
    (hF : DifferentiableAt ℂ F xi) :
    deriv (fun t => Complex.I*t*F t) xi = Complex.I*(F xi+xi*deriv F xi) := by
  have hh := ((hasDerivAt_id xi).const_mul Complex.I).mul hF.hasDerivAt
  change deriv ((fun y => Complex.I*id y)*F) xi = _
  rw [hh.deriv]
  dsimp
  ring

theorem fourier_linear_factor_second_derivative_local (F : ℂ → ℂ) (c : ℝ)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z.im<c}) (xi : ℂ) (hx : xi.im<c) :
    deriv (deriv (fun t => Complex.I*t*F t)) xi =
      Complex.I*(2*deriv F xi+xi*deriv (deriv F) xi) := by
  have he : deriv (fun t => Complex.I*t*F t) =ᶠ[𝓝 xi]
      fun t => Complex.I*(F t+t*deriv F t) := by
    filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hx] with t ht
    exact fourier_linear_factor_derivative_at F t (hF t ht).differentiableAt
  rw [he.deriv_eq]
  have hh := ((hF xi hx).differentiableAt.hasDerivAt.add
    ((hasDerivAt_id xi).mul (hF.deriv xi hx).differentiableAt.hasDerivAt)).const_mul Complex.I
  convert hh.deriv using 1
  · rfl
  · dsimp
    ring

theorem ray_second_derivative (F : ℂ → ℂ) (c : ℝ)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z.im<c}) (omega : ℂ) (x : ℝ)
    (hx : (omega*x).im<c) :
    deriv (deriv (fun t : ℝ => F (omega*t))) x=omega^2*deriv (deriv F) (omega*x) := by
  have he : deriv (fun t : ℝ => F (omega*t)) =ᶠ[𝓝 x]
      fun t => omega*deriv F (omega*t) := by
    have hc : Continuous (fun t : ℝ => (omega*t).im) := by fun_prop
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hx] with t ht
    exact (laplace_ray_hasDerivAt c F hF omega t ht).deriv
  rw [he.deriv_eq]
  have hh := (laplace_ray_hasDerivAt c (deriv F) hF.deriv omega x hx).const_mul omega
  rw [hh.deriv]
  ring

end KN.Energy
