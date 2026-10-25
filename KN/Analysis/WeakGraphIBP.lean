import KN.Angular.MaximalDomain
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Module

noncomputable section
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology
namespace KN.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma compact_smul_contDiff {s : Set ℝ} (hs : IsOpen s) (phi : ℝ → ℂ) (u : ℝ → E)
    (hp : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) phi)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) u s) (hsub : tsupport phi ⊆ s) :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun x => phi x • u x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ s
  · exact hp.contDiffAt.smul (hu.contDiffAt (hs.mem_nhds hx))
  · have hn : x ∉ tsupport phi := fun h => hx (hsub h)
    have he := (notMem_tsupport_iff_eventuallyEq).mp hn
    apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

omit [CompleteSpace E] in
lemma compact_smul_continuous {s : Set ℝ} (hs : IsOpen s) (phi : ℝ → ℂ) (u : ℝ → E)
    (hp : Continuous phi) (hu : ContinuousOn u s) (hsub : tsupport phi ⊆ s) :
    Continuous (fun x => phi x • u x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ s
  · exact hp.continuousAt.smul (hu.continuousAt (hs.mem_nhds hx))
  · have hn : x ∉ tsupport phi := fun h => hx (hsub h)
    have he := (notMem_tsupport_iff_eventuallyEq).mp hn
    apply (continuousAt_const (y := (0:E))).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    simp [hy]

lemma compact_derivative_integral_zero {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ioo 0 Real.pi) :
    (∫ x in Ioo (0:ℝ) Real.pi, deriv f x) = 0 := by
  have hd : tsupport (deriv f) ⊆ Ioo 0 Real.pi := tsupport_deriv_subset.trans hs
  have h0 : f 0 = 0 := image_eq_zero_of_notMem_tsupport (by
    intro hh; have := (hs hh).1; linarith)
  have hi := hc.integral_Ioi_deriv_eq hf 0
  rw [h0, neg_zero] at hi
  have hio : (∫ x in Ioi (0:ℝ), deriv f x) = ∫ x : ℝ, deriv f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hd h).1))
  have hioo : (∫ x in Ioo (0:ℝ) Real.pi, deriv f x) = ∫ x : ℝ, deriv f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hd h)))
  rw [hio] at hi
  rw [hioo]
  exact hi

/-- A classical differential equation gives the actual weak graph. No domain membership
or integration-by-parts identity is assumed. Compact tests remove both angular endpoints. -/
theorem matrixWeakGraph_of_classical {N : ℕ}
    (D : Matrix (Fin N) (Fin N) ℂ) (W : ℝ → Matrix (Fin N) (Fin N) ℂ)
    (u v : ℝ → EuclideanSpace ℂ (Fin N))
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) u (Ioo 0 Real.pi))
    (hv : ContinuousOn v (Ioo 0 Real.pi))
    (heq : ∀ x ∈ Ioo 0 Real.pi,
      v x = D.toEuclideanLin (deriv u x) + (W x).toEuclideanLin (u x)) :
    KN.Angular.MatrixWeakGraph D W u v := by
  intro phi hphi
  obtain ⟨hp,hcompact,hsub⟩ := hphi
  let L : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
    D.toEuclideanLin.toContinuousLinearMap
  let f : ℝ → EuclideanSpace ℂ (Fin N) := fun x => phi x • L (u x)
  have hLu := (L.restrictScalars ℝ).contDiff.comp_contDiffOn hu
  have hf := compact_smul_contDiff isOpen_Ioo phi (fun x => L (u x)) hp hLu hsub
  have hfc : HasCompactSupport f := hcompact.smul_right
  have hfs : tsupport f ⊆ Ioo 0 Real.pi := (tsupport_smul_subset_left _ _).trans hsub
  have hzero := compact_derivative_integral_zero (hf.of_le (by simp)) hfc hfs
  have hd (x : ℝ) (hx : x ∈ Ioo 0 Real.pi) :
      deriv f x = deriv phi x • L (u x) + phi x • L (deriv u x) := by
    have hud := (hu.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by simp)
    have hld := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hud.hasDerivAt
    have hprod := ((hp.differentiable (by simp) x).hasDerivAt.smul hld).deriv
    change deriv f x = phi x • L (deriv u x) + deriv phi x • L (u x) at hprod
    exact hprod.trans (add_comm _ _)
  have hiv : IntegrableOn (fun x => phi x • v x) (Ioo 0 Real.pi) :=
    ((compact_smul_continuous isOpen_Ioo phi v hp.continuous hv hsub).integrable_of_hasCompactSupport hcompact.smul_right).integrableOn
  have hid : IntegrableOn (deriv f) (Ioo 0 Real.pi) :=
    ((hf.of_le (by simp) : ContDiff ℝ 1 f).continuous_deriv le_rfl).integrable_of_hasCompactSupport hfc.deriv |>.integrableOn
  change (∫ x in Ioo (0:ℝ) Real.pi, phi x • v x) = _
  calc
    _ = ∫ x in Ioo (0:ℝ) Real.pi, phi x • v x - deriv f x := by
      rw [integral_sub hiv hid, hzero, sub_zero]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      dsimp only
      rw [heq x hx, hd x hx]
      change phi x • (L (deriv u x)+(W x).toEuclideanLin (u x)) -
        (deriv phi x • L (u x)+phi x • L (deriv u x)) =
          -(deriv phi x) • L (u x) + phi x • (W x).toEuclideanLin (u x)
      module

end KN.Analysis
