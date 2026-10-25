import KN.Analysis.LaplaceCalculus
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
open Set MeasureTheory TopologicalSpace
namespace KN.Analysis
open KN.ChargedRadial

/-- Finite ordered polynomial differential expressions. Order is part of the syntax. -/
inductive WeylExpr where
  | id
  | add (a b : WeylExpr)
  | smul (c : ℂ) (a : WeylExpr)
  | diff (a : WeylExpr)
  | coord (a : WeylExpr)

def WeylExpr.evalDist : WeylExpr → CDist → CDist
  | .id,T => T
  | .add a b,T => a.evalDist T+b.evalDist T
  | .smul c a,T => c • a.evalDist T
  | .diff a,T => Distribution.lineDerivCLM (1:ℝ) (a.evalDist T)
  | .coord a,T => coordinateMultiply (a.evalDist T)

def WeylExpr.evalFun : WeylExpr → (ℂ → ℂ) → (ℂ → ℂ)
  | .id,F => F
  | .add a b,F => fun z => a.evalFun F z+b.evalFun F z
  | .smul c a,F => fun z => c*a.evalFun F z
  | .diff a,F => fun z => Complex.I*z*a.evalFun F z
  | .coord a,F => fun z => Complex.I*deriv (a.evalFun F) z

/-- Ordered Fourier substitution is proved for every expression from actual distribution transforms. -/
theorem WeylExpr.transform (e : WeylExpr) (T : CDist) (c : ℝ) (F : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F)
    (ha : AnalyticOnNhd ℂ F {z : ℂ | z.im<c}) :
    IsFourierLaplaceTransform (e.evalDist T) c (e.evalFun F) ∧
      AnalyticOnNhd ℂ (e.evalFun F) {z : ℂ | z.im<c} := by
  induction e with
  | id => exact ⟨hF,ha⟩
  | add a b ha' hb' => exact ⟨ha'.1.add hb'.1, ha'.2.add hb'.2⟩
  | smul z a ha' => exact ⟨ha'.1.smul z, analyticOnNhd_const.mul ha'.2⟩
  | diff a ha' =>
    exact ⟨External.fourier_laplace_derivative _ _ _ ha'.1,
      (analyticOnNhd_const.mul analyticOnNhd_id).mul ha'.2⟩
  | coord a ha' =>
    exact ⟨External.fourier_laplace_coordinate _ _ _ ha'.1 ha'.2,
      analyticOnNhd_const.mul ha'.2.deriv⟩

/-- A zero distributional polynomial equation yields its actual analytic transformed equation. -/
theorem WeylExpr.equation (e : WeylExpr) (T : CDist) (c : ℝ) (F : ℂ → ℂ)
    (hF : IsFourierLaplaceTransform T c F)
    (ha : AnalyticOnNhd ℂ F {z : ℂ | z.im<c}) (hE : e.evalDist T=0) :
    ∀ z : ℂ, z.im<c → e.evalFun F z=0 := by
  obtain ⟨he,heh⟩ := e.transform T c F hF ha
  exact transform_zero_of_distribution_zero he heh hE

end KN.Analysis
