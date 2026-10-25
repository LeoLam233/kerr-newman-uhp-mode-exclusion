import KN.Energy.InfinityGauge
import KN.Energy.InfinityCoefficients

noncomputable section
open Filter Set Asymptotics
open ComplexConjugate
namespace KN.Energy

theorem ExpPolyGrowth.conj {k : ℝ} {f : ℝ → ℂ} (hf : ExpPolyGrowth k f) :
    ExpPolyGrowth k (fun r => conj (f r)) := by
  obtain ⟨N,hN⟩ := hf
  refine ⟨N,IsBigO.of_norm_left ?_⟩
  simpa only [Complex.norm_conj] using hN.norm_left

theorem ExpPolyGrowth.normSq {k : ℝ} {f : ℝ → ℂ} (hf : ExpPolyGrowth k f) :
    ExpPolyGrowth (k+k) (fun r => (Complex.normSq (f r):ℂ)) := by
  simpa only [Complex.mul_conj] using hf.mul hf.conj

theorem density_expPolyGrowth (ω : ℂ) (P W k B : ℝ → ℝ) (U V : ℝ → ℂ) (κ : ℝ)
    (hP : PolyBound (fun r => (P r:ℂ))) (hW : PolyBound (fun r => (W r:ℂ)))
    (hk : PolyBound (fun r => (k r:ℂ))) (hB : PolyBound (fun r => (B r:ℂ)))
    (hU : ExpPolyGrowth κ U) (hV : ExpPolyGrowth κ V) :
    ExpPolyGrowth (κ+κ) (fun r => (density ω P W k B U V r:ℂ)) := by
  have h1 := hV.normSq.mul_poly hP
  have h2 := hU.normSq.mul_poly (polyBound_mul hW hk)
  have h3 := hU.normSq.mul_poly (polyBound_mul
    (polyBound_mul (polyBound_const (Complex.normSq ω:ℂ)) hW) hB)
  convert (h1.add h2).add h3 using 1
  ext r
  dsimp [density]
  push_cast
  ring

theorem current_expPolyGrowth (ω : ℂ) (P : ℝ → ℝ) (U V : ℝ → ℂ) (κ : ℝ)
    (hP : PolyBound (fun r => (P r:ℂ)))
    (hU : ExpPolyGrowth κ U) (hV : ExpPolyGrowth κ V) :
    ExpPolyGrowth (κ+κ) (fun r => (current ω P U V r:ℂ)) := by
  have h := (hV.mul hU.conj).mul_poly (polyBound_mul (polyBound_const (conj ω)) hP)
  obtain ⟨N,hN⟩ := h
  refine ⟨N,?_⟩
  have hi : (fun r => (current ω P U V r:ℂ)) =O[atTop]
      (fun r => (V r*conj (U r))*(conj ω*(P r:ℂ))) := by
    refine isBigO_iff.mpr ⟨1,Filter.Eventually.of_forall (fun r => ?_)⟩
    simp only [one_mul,Complex.norm_real,Real.norm_eq_abs,current]
    convert Complex.abs_im_le_norm (conj ω*((P r:ℂ)*V r*conj (U r))) using 1
    congr 1
    ring
  exact hi.trans hN

/-- Returning from the reflected variable gives the exact decaying bound
used by the improper energy integral and both flux limits. -/
theorem reflected_growth_atBot (f : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hf : ExpPolyGrowth (-κ+-κ) (fun r => (f (-r):ℂ))) :
    f =O[atBot] (fun x : ℝ => Real.exp (κ*x)) := by
  have hh := expPolyGrowth_damping hf 0 (by linarith)
  simp only [zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul,zero_add] at hh
  have he : (-κ+-κ)/2 = -κ := by ring
  rw [he] at hh
  have h := hh.comp_tendsto tendsto_neg_atBot_atTop
  change (fun x : ℝ => (f (- -x):ℂ)) =O[atBot] (fun x : ℝ => Real.exp (-κ*(-x))) at h
  have h' : (fun x : ℝ => (f x:ℂ)) =O[atBot] (fun x : ℝ => Real.exp (κ*x)) := by
    simpa only [neg_neg,neg_mul_neg] using h
  apply IsBigO.of_norm_left
  simpa only [Complex.norm_real] using h'.norm_left

end KN.Energy
