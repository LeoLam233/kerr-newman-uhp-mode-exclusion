import KN.Analysis.WeylTransform
import KN.ChargedRadial.PhysicalElimination
import KN.ChargedRadial.DistributionAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open Set TopologicalSpace
open scoped Distributions ContDiff
namespace KN.Energy
open KN.Analysis KN.ChargedRadial

theorem realCast_smooth : ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff

def quadraticWeyl (a2 a1 a0 : ℂ) (e : WeylExpr) : WeylExpr :=
  .add (.add (.smul a2 (.coord (.coord e))) (.smul a1 (.coord e))) (.smul a0 e)

def radialWeyl (p : RadialPolynomialData) : WeylExpr :=
  .add (.add
    (.diff (.diff (.add
      (quadraticWeyl 1 (-2*p.M) (p.a^2+p.Q^2) (.diff .id))
      (quadraticWeyl p.L2 p.L1 p.L0 .id))))
    (.smul (-1) (quadraticWeyl (p.u^2) (2*p.u*p.b) (p.b^2+p.lam^2) (.diff .id))))
    (.smul (-1) (quadraticWeyl 0 (3*p.u^2) ((3*p.b-Complex.I*p.sigma*p.lam)*p.u) .id))

theorem coordinateMultiply_complex (T : CDist) :
    coordinateMultiply T=mulComplexDist (fun r : ℝ => (r:ℂ)) realCast_smooth T := by
  change mulDist (fun r : ℝ => r) contDiff_id T =
    mulDist (fun r : ℝ => r) contDiff_id T +
      Complex.I • mulDist (fun _ : ℝ => 0) contDiff_const T
  rw [mulDist_const]
  change mulDist (fun r : ℝ => r) contDiff_id T =
    mulDist (fun r : ℝ => r) contDiff_id T + Complex.I • ((0:ℝ) • T)
  have hz : Complex.I • (0:CDist)=0 := by
    ext phi
    change Complex.I*(0:ℂ)=0
    exact mul_zero _
  exact (add_zero _).symm.trans (congrArg (fun X : CDist => mulDist (fun r : ℝ => r) contDiff_id T + X)
    ((congrArg (fun X : CDist => Complex.I • X) (zero_smul ℝ T)).trans hz).symm)

theorem quadraticWeyl_evalDist (a2 a1 a0 : ℂ) (e : WeylExpr) (T : CDist) :
    (quadraticWeyl a2 a1 a0 e).evalDist T =
      mulComplexDist (fun r : ℝ => a2*(r:ℂ)^2+a1*(r:ℂ)+a0)
        ((contDiff_const.mul (realCast_smooth.pow 2) |>.add
          (contDiff_const.mul realCast_smooth)).add contDiff_const) (e.evalDist T) := by
  change a2 • coordinateMultiply (coordinateMultiply (e.evalDist T))+
    a1 • coordinateMultiply (e.evalDist T)+a0 • e.evalDist T = _
  simp only [coordinateMultiply_complex]
  rw [mulComplexDist_comp]
  rw [mulComplexDist_add_fun _ _
    ((contDiff_const.mul (realCast_smooth.pow 2)).add (contDiff_const.mul realCast_smooth)) contDiff_const,
    mulComplexDist_add_fun _ _ (contDiff_const.mul (realCast_smooth.pow 2))
      (contDiff_const.mul realCast_smooth),
    mulComplexDist_const_mul a2 _ (realCast_smooth.pow 2),
    mulComplexDist_const_mul a1 _ realCast_smooth, mulComplexDist_const]
  rw [mulComplexDist_congr (fun r : ℝ => (r:ℂ)*(r:ℂ)) (fun r : ℝ => (r:ℂ)^2)
    (realCast_smooth.mul realCast_smooth) (realCast_smooth.pow 2)
    (funext (fun r => (pow_two (r:ℂ)).symm))]

end KN.Energy
