import KN.ChargedRadial.DistributionLeibniz

noncomputable section
set_option backward.isDefEq.respectTransparency false
open TopologicalSpace
open scoped Distributions ContDiff
namespace KN.ChargedRadial

theorem mulDist_add_fun (g h : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (T : CDist) :
    mulDist (fun r => g r+h r) (hg.add hh) T = mulDist g hg T + mulDist h hh T := by
  ext phi
  change T (mulTest (fun r => g r+h r) (hg.add hh) phi) = T (mulTest g hg phi) + T (mulTest h hh phi)
  rw [← map_add]
  congr 1
  ext r
  change phi r*(g r+h r)=phi r*g r+phi r*h r
  ring

theorem mulDist_sub_fun (g h : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (T : CDist) :
    mulDist (fun r => g r-h r) (hg.sub hh) T = mulDist g hg T - mulDist h hh T := by
  ext phi
  change T (mulTest (fun r => g r-h r) (hg.sub hh) phi) = T (mulTest g hg phi) - T (mulTest h hh phi)
  rw [← map_sub]
  congr 1
  ext r
  change phi r*(g r-h r)=phi r*g r-phi r*h r
  ring

/-- Smooth multiplication is an algebra action on actual ordinary distributions. -/
theorem mulComplexDist_comp (g h : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (T : CDist) :
    mulComplexDist g hg (mulComplexDist h hh T) =
      mulComplexDist (fun r => g r*h r) (hg.mul hh) T := by
  simp only [mulComplexDist, add_apply, smul_apply,
    map_add, mulDist_complex_smul, mulDist_comp, smul_smul, Complex.I_mul_I]
  change _ = mulDist (fun r => (g r).re*(h r).re-(g r).im*(h r).im) _ T +
    Complex.I • mulDist (fun r => (g r).re*(h r).im+(g r).im*(h r).re) _ T
  erw [mulDist_sub_fun _ _ ((Complex.reCLM.contDiff.comp hg).mul (Complex.reCLM.contDiff.comp hh))
    ((Complex.imCLM.contDiff.comp hg).mul (Complex.imCLM.contDiff.comp hh)),
    mulDist_add_fun _ _ ((Complex.reCLM.contDiff.comp hg).mul (Complex.imCLM.contDiff.comp hh))
    ((Complex.imCLM.contDiff.comp hg).mul (Complex.reCLM.contDiff.comp hh))]
  simp only [smul_add, neg_one_smul]
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply]
  abel

theorem mulComplexDist_congr (g h : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h)
    (he : g = h) : mulComplexDist g hg = mulComplexDist h hh := by subst h; rfl

theorem mulComplexDist_complex_smul (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (c : ℂ) (T : CDist) :
    mulComplexDist g hg (c • T) = c • mulComplexDist g hg T := by
  simp only [mulComplexDist, add_apply, smul_apply, mulDist_complex_smul, smul_add, smul_smul]
  rw [mul_comm Complex.I c]

theorem mulDist_const (c : ℝ) (T : CDist) : mulDist (fun _ => c) contDiff_const T = c • T := by
  ext phi
  have ht : mulTest (fun _ => c) contDiff_const phi = c • phi := by
    ext r
    change phi r*c = c*phi r
    ring
  change T (mulTest (fun _ => c) contDiff_const phi) = c • T phi
  rw [ht, map_smul]

theorem mulComplexDist_const (c : ℂ) (T : CDist) :
    mulComplexDist (fun _ => c) contDiff_const T = c • T := by
  simp only [mulComplexDist, add_apply, smul_apply, mulDist_const]
  ext phi
  change (c.re:ℂ)*T phi+Complex.I*((c.im:ℂ)*T phi)=c*T phi
  calc
    _ = ((c.re:ℂ)+(c.im:ℂ)*Complex.I)*T phi := by ring
    _ = _ := by rw [Complex.re_add_im]

theorem mulComplexDist_add_fun (g h : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) (T : CDist) :
    mulComplexDist (fun r => g r+h r) (hg.add hh) T = mulComplexDist g hg T + mulComplexDist h hh T := by
  simp only [mulComplexDist, add_apply, smul_apply, Complex.add_re, Complex.add_im]
  erw [mulDist_add_fun _ _ (Complex.reCLM.contDiff.comp hg) (Complex.reCLM.contDiff.comp hh),
    mulDist_add_fun _ _ (Complex.imCLM.contDiff.comp hg) (Complex.imCLM.contDiff.comp hh)]
  simp only [smul_add]
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.imCLM_apply]
  abel

theorem mulComplexDist_const_mul (c : ℂ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (T : CDist) :
    mulComplexDist (fun r => c*g r) (contDiff_const.mul hg) T = c • mulComplexDist g hg T := by
  rw [← mulComplexDist_comp (fun _ => c) g contDiff_const hg, mulComplexDist_const]

theorem mulComplexDist_mul_const (c : ℂ) (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (T : CDist) :
    mulComplexDist (fun r => g r*c) (hg.mul contDiff_const) T = c • mulComplexDist g hg T := by
  rw [mulComplexDist_congr _ (fun r => c*g r) _ (contDiff_const.mul hg) (funext (fun _ => mul_comm _ _))]
  exact mulComplexDist_const_mul c g hg T

end KN.ChargedRadial
