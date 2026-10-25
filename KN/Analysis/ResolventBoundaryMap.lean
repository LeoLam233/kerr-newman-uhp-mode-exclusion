import KN.Boundary.GaugeSmooth
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace KN.Boundary
noncomputable section
open Set Filter
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem eulerDeriv_contDiffOn {rp : ℝ} {f : ℝ → E} (hf : ContDiffOn ℝ ∞ f (Ioi rp)) :
    ContDiffOn ℝ ∞ (eulerDeriv f) (Ioi rp) :=
  contDiffOn_id.smul (hf.deriv_of_isOpen isOpen_Ioi (by simp))

theorem eulerDeriv_iterate_contDiffOn {rp : ℝ} {f : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (Ioi rp)) (n : ℕ) :
    ContDiffOn ℝ ∞ ((eulerDeriv^[n]) f) (Ioi rp) := by
  induction n with
  | zero => exact hf
  | succ n ih => rw [Function.iterate_succ_apply']; exact eulerDeriv_contDiffOn ih

theorem deriv_clm_on {rp : ℝ} {f : ℝ → E} (hf : ContDiffOn ℝ ∞ f (Ioi rp))
    (L : E →L[ℂ] F) {r : ℝ} (hr : rp<r) : deriv (fun x => L (f x)) r=L (deriv f r) := by
  have hd := ((hf r hr).contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)
  exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hd.hasDerivAt).deriv

/-- Every radial Euler derivative commutes with a fixed bounded angular functional. -/
theorem eulerDeriv_iterate_clm_on {rp : ℝ} {f : ℝ → E}
    (hf : ContDiffOn ℝ ∞ f (Ioi rp)) (L : E →L[ℂ] F) (n : ℕ) :
    ∀ r>rp, (eulerDeriv^[n]) (fun x => L (f x)) r=L ((eulerDeriv^[n]) f r) := by
  induction n with
  | zero => intro r _; rfl
  | succ n ih =>
    intro r hr
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change r • deriv ((eulerDeriv^[n]) (fun x => L (f x))) r = L (r • deriv ((eulerDeriv^[n]) f) r)
    have he : (eulerDeriv^[n]) (fun x => L (f x)) =ᶠ[𝓝 r]
        (fun x => L ((eulerDeriv^[n]) f x)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
      exact ih x hx
    rw [he.deriv_eq,deriv_clm_on (eulerDeriv_iterate_contDiffOn hf n) L hr]
    exact ((L.restrictScalars ℝ).map_smul r _).symm

/-- Fixed bounded angular maps preserve the actual polynomial-conormal class. -/
theorem PolynomialConormal.map_on {rp : ℝ} {f : ℝ → E}
    (hf : PolynomialConormal f) (hs : ContDiffOn ℝ ∞ f (Ioi rp)) (L : E →L[ℂ] F) :
    PolynomialConormal (fun r => L (f r)) := by
  intro j
  obtain ⟨N,C,R,hC,hR,hbound⟩ := hf j
  refine ⟨N,‖L‖*C,max R (rp+1),mul_nonneg (norm_nonneg _) hC,le_trans hR (le_max_left _ _),?_⟩
  intro r hr
  have hrR := le_trans (le_max_left R (rp+1)) hr
  have hre : rp<r := by have := le_trans (le_max_right R (rp+1)) hr; linarith
  rw [eulerDeriv_iterate_clm_on hs L j r hre]
  calc
    _ ≤ ‖L‖*‖(eulerDeriv^[j]) f r‖ := L.le_opNorm _
    _ ≤ ‖L‖*(C*(1+|r|)^N) := mul_le_mul_of_nonneg_left (hbound r hrR) (norm_nonneg _)
    _ = _ := by ring

/-- Physical outgoing data descend to every fixed adjoint-chain coefficient. -/
theorem Outgoing.map {b : KN.Background} {m : ℤ} {omega : ℂ} {f : ℝ → E}
    (hout : Outgoing b m omega f) (hf : ContDiffOn ℝ ∞ f (Ioi b.rPlus))
    (L : E →L[ℂ] F) : Outgoing b m omega (fun r => L (f r)) := by
  have hs := (gauge_contDiffOn b m omega).smul hf
  have h := PolynomialConormal.map_on hout hs L
  simpa only [Outgoing, map_smul] using h

end
end KN.Boundary
