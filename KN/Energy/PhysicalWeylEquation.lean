import KN.Energy.PhysicalWeylEquationDist
import KN.Energy.PhysicalWeylEquationFun
import KN.Energy.RawEnergyExclusion
import KN.ChargedRadial.RayRegularity

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KN.Energy
open KN.Analysis KN.ChargedRadial

/-- The actual supported distribution equation implies the physical transformed
ODE. Only holomorphy on its natural lower half-plane is used. -/
theorem physical_supported_pair_transformedEquation
    (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ) (sigma omega lam : ℂ)
    (hs : sigma=1 ∨ sigma = -1) (hw : 0<omega.im)
    (pair : SupportedPair b.rPlus (fun r => (b.Delta r:ℂ)) (physicalL b m sigma omega)
      (fun r => physicalR1 b sigma omega r+Complex.I*sigma*lam)
      (fun r => physicalR1 b sigma omega r-Complex.I*sigma*lam)
      (physicalDelta_smooth b) (physicalL_smooth b m sigma omega)
      ((physicalR1_smooth b sigma omega).add contDiff_const)
      ((physicalR1_smooth b sigma omega).sub contDiff_const))
    (F : ℂ → ℂ) (hF : IsFourierLaplaceTransform pair.v (-(b.eta*omega.im)) F)
    (ha : AnalyticOnNhd ℂ F {z : ℂ | z.im < -(b.eta*omega.im)}) :
    TransformedEquation b (backgroundPolynomialData b m sigma omega lam)
      (fun x : ℝ => F (omega*x)) (deriv (fun x : ℝ => F (omega*x))) := by
  intro x hx
  have hxc : (omega*(x:ℂ)).im < -(b.eta*omega.im) := by
    apply physical_ray_mem b omega hw
    change x < -(b.eta+2) at hx
    linarith
  have he := (radialWeyl (backgroundPolynomialData b m sigma omega lam)).equation
    pair.v (-(b.eta*omega.im)) F hF ha
    (physical_radialWeyl_zero b m sigma omega lam hs pair) (omega*x) hxc
  rw [radialWeyl_evalFun _ F _ ha _ hxc, orderedFourierJet_coefficients] at he
  obtain ⟨h2,h1,h0⟩ := physical_fourier_coefficients b hQ m sigma omega lam (x:ℂ) hs
  rw [h2,h1,h0] at he
  rw [(laplace_ray_hasDerivAt _ F ha omega x hxc).deriv,
    ray_second_derivative F _ ha omega x hxc]
  have hw0 : omega ≠ 0 := by intro h; simp [h] at hw
  apply (mul_eq_zero.mp (show Complex.I*omega *
    (transformA (backgroundPolynomialData b m sigma omega lam) x*
        (omega^2*deriv (deriv F) (omega*x))+
      (transformB (backgroundPolynomialData b m sigma omega lam) x+
        Complex.I*omega*transformC (backgroundPolynomialData b m sigma omega lam) x)*
          (omega*deriv F (omega*x))+
      (transformD0 (backgroundPolynomialData b m sigma omega lam) x+
        omega*transformD1 (backgroundPolynomialData b m sigma omega lam) x+
        omega^2*transformD2 (backgroundPolynomialData b m sigma omega lam) x+
        Complex.I*omega*transformE (backgroundPolynomialData b m sigma omega lam) x)*F (omega*x))=0
    from (by linear_combination he))).resolve_left
  exact mul_ne_zero Complex.I_ne_zero hw0

end KN.Energy
