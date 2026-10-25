import KN.Energy.PhysicalWeylEquationAlgebra
import KN.Energy.PhysicalWeylEquationLocal
noncomputable section
namespace KN.Energy
open KN.Analysis KN.ChargedRadial

theorem quadraticWeyl_evalFun (a2 a1 a0 : ℂ) (e : WeylExpr) (F : ℂ → ℂ) (z : ℂ) :
    (quadraticWeyl a2 a1 a0 e).evalFun F z =
    -a2*deriv (deriv (e.evalFun F)) z+Complex.I*a1*deriv (e.evalFun F) z+a0*e.evalFun F z := by
  simp only [quadraticWeyl, WeylExpr.evalFun, deriv_const_mul_field]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem radialWeyl_evalFun (p : RadialPolynomialData) (F : ℂ → ℂ) (c : ℝ)
    (hF : AnalyticOnNhd ℂ F {z : ℂ | z.im<c}) (z : ℂ) (hz : z.im<c) :
    (radialWeyl p).evalFun F z=orderedFourierJet p z (F z) (deriv F z) (deriv (deriv F) z) := by
  change Complex.I*z*(Complex.I*z*((quadraticWeyl 1 (-2*p.M) (p.a^2+p.Q^2) (.diff .id)).evalFun F z+
    (quadraticWeyl p.L2 p.L1 p.L0 .id).evalFun F z))+
    (-1)*(quadraticWeyl (p.u^2) (2*p.u*p.b) (p.b^2+p.lam^2) (.diff .id)).evalFun F z+
    (-1)*(quadraticWeyl 0 (3*p.u^2) ((3*p.b-Complex.I*p.sigma*p.lam)*p.u) .id).evalFun F z = _
  simp only [quadraticWeyl_evalFun, WeylExpr.evalFun]
  rw [fourier_linear_factor_derivative_at F z (hF z hz).differentiableAt,
    fourier_linear_factor_second_derivative_local F c hF z hz]
  have h3 : Complex.I^3 = -Complex.I := by norm_num [pow_succ, Complex.I_mul_I]
  have h4 : Complex.I^4 = 1 := by norm_num [pow_succ, Complex.I_mul_I]
  unfold orderedFourierJet
  ring_nf
  simp only [Complex.I_sq, h3, h4]
  ring

end KN.Energy
