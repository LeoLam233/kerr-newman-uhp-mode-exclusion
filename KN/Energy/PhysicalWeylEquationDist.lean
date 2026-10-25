import KN.Energy.PhysicalWeylEquationAlgebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Distributions ContDiff
namespace KN.Energy
open KN.Analysis KN.ChargedRadial

theorem quadraticWeyl_evalDist_congr (a2 a1 a0 : ℂ) (e : WeylExpr) (T : CDist)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g)
    (he : ∀ r : ℝ, a2*(r:ℂ)^2+a1*(r:ℂ)+a0=g r) :
    (quadraticWeyl a2 a1 a0 e).evalDist T=mulComplexDist g hg (e.evalDist T) := by
  rw [quadraticWeyl_evalDist,
    mulComplexDist_congr _ g _ hg (funext he)]

theorem physical_radialWeyl_zero
    (b : KN.Background) (m : ℤ) (sigma omega lam : ℂ) (hs : sigma=1 ∨ sigma = -1)
    (pair : SupportedPair b.rPlus (fun r => (b.Delta r:ℂ)) (physicalL b m sigma omega)
      (fun r => physicalR1 b sigma omega r+Complex.I*sigma*lam)
      (fun r => physicalR1 b sigma omega r-Complex.I*sigma*lam)
      (physicalDelta_smooth b) (physicalL_smooth b m sigma omega)
      ((physicalR1_smooth b sigma omega).add contDiff_const)
      ((physicalR1_smooth b sigma omega).sub contDiff_const)) :
    (radialWeyl (backgroundPolynomialData b m sigma omega lam)).evalDist pair.v=0 := by
  let p := backgroundPolynomialData b m sigma omega lam
  have hD := quadraticWeyl_evalDist_congr 1 (-2*p.M) (p.a^2+p.Q^2) (.diff .id) pair.v
    (fun r => (b.Delta r:ℂ)) (physicalDelta_smooth b) (by
      intro r
      dsimp [p, backgroundPolynomialData, KN.Background.Delta]
      push_cast
      ring)
  have hL := quadraticWeyl_evalDist_congr p.L2 p.L1 p.L0 .id pair.v
    (physicalL b m sigma omega) (physicalL_smooth b m sigma omega)
    (fun r => (physicalL_polynomial b m sigma omega lam r).symm)
  have hR := quadraticWeyl_evalDist_congr (p.u^2) (2*p.u*p.b) (p.b^2+p.lam^2) (.diff .id) pair.v
    (fun r => physicalR1 b sigma omega r^2+lam^2)
    ((physicalR1_smooth b sigma omega).pow 2 |>.add contDiff_const) (by
      intro r
      rw [physicalR1_affine b m sigma omega lam]
      dsimp [radialAffine, p, backgroundPolynomialData]
      ring)
  have hC := quadraticWeyl_evalDist_congr 0 (3*p.u^2) ((3*p.b-Complex.I*p.sigma*p.lam)*p.u) .id pair.v
    (fun r => (3*physicalR1 b sigma omega r-Complex.I*sigma*lam)*(-sigma*b.c*omega))
    ((contDiff_const.mul (physicalR1_smooth b sigma omega)).sub contDiff_const |>.mul contDiff_const) (by
      intro r
      rw [physicalR1_affine b m sigma omega lam]
      dsimp [radialAffine, p, backgroundPolynomialData, RadialPolynomialData.u]
      ring)
  have h := physical_supported_pair_elimination b m sigma omega lam hs pair
  change (Distribution.lineDerivCLM (1:ℝ)) ((Distribution.lineDerivCLM (1:ℝ))
    ((quadraticWeyl 1 (-2*p.M) (p.a^2+p.Q^2) (.diff .id)).evalDist pair.v+
      (quadraticWeyl p.L2 p.L1 p.L0 .id).evalDist pair.v))+
    (-1:ℂ) • (quadraticWeyl (p.u^2) (2*p.u*p.b) (p.b^2+p.lam^2) (.diff .id)).evalDist pair.v+
    (-1:ℂ) • (quadraticWeyl 0 (3*p.u^2) ((3*p.b-Complex.I*p.sigma*p.lam)*p.u) .id).evalDist pair.v=0
  rw [hD,hL,hR,hC]
  have hn (T : CDist) : (-1:ℂ) • T = -T := by
    ext phi
    change (-1:ℂ)*T phi= -T phi
    ring
  simp only [hn, ← sub_eq_add_neg]
  exact h

end KN.Energy
