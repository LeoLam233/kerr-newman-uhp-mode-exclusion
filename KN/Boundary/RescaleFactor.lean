import KN.Boundary.Multiplier
import KN.Boundary.Powers

noncomputable section
namespace KN.Boundary

def rescaleFactor (b : Background) (m : ℤ) (ω : ℂ) (q : ℝ) (r : ℝ) : ℂ :=
  (Real.rpow (b.Delta r) q : ℂ) / gauge b m ω r *
    Complex.exp (Complex.I*b.eta*ω*r)

theorem rescaleFactor_ne_zero (b : Background) (m : ℤ) (ω : ℂ) (q : ℝ)
    {r : ℝ} (hr : b.rPlus < r) : rescaleFactor b m ω q r ≠ 0 := by
  unfold rescaleFactor
  exact mul_ne_zero (div_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (b.Delta_pos hr) q)))
    (gauge_ne_zero b m ω r)) (Complex.exp_ne_zero _)

theorem rescaleFactor_hasDerivAt (b : Background) (m : ℤ) (ω : ℂ) (q : ℝ)
    {r : ℝ} (hr : b.rPlus < r) :
    HasDerivAt (rescaleFactor b m ω q)
      (rescaleFactor b m ω q r *
        ((q:ℂ)*(2*(r:ℂ)-2*b.M)/(b.Delta r:ℂ) -
          Complex.I*b.frequencyK m ω r/(b.Delta r:ℂ) + Complex.I*b.eta*ω)) r := by
  have hp := (delta_rpow_hasDerivAt b q hr).ofReal_comp
  have hg := gauge_hasDerivAt b m ω hr
  have he := ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul (Complex.I*b.eta*ω)).cexp
  have hd := (hp.div hg (gauge_ne_zero b m ω r)).mul he
  have hdelta : b.Delta r ≠ 0 := ne_of_gt (b.Delta_pos hr)
  have hH := gauge_ne_zero b m ω r
  convert hd using 1
  · rfl
  · simp [rescaleFactor, Real.rpow_sub_one hdelta]
    field_simp

theorem rescaleFactor_sqrt_shift (b : Background) (m : ℤ) (ω : ℂ) (q : ℝ)
    {r : ℝ} (hr : b.rPlus < r) :
    rescaleFactor b m ω q r / (Real.sqrt (b.Delta r):ℂ) =
      rescaleFactor b m ω (q-1/2) r := by
  have hs := sqrt_shift b hr (q-1/2)
  have he : q-1/2+1/2=q := by ring
  rw [he] at hs
  unfold rescaleFactor
  rw [← hs]
  have ht : (Real.sqrt (b.Delta r):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  field_simp

/-- Exact cancellation of the original horizon gauge in the outgoing radial variable. -/
theorem multiplier_rescale_identity (b : Background) (m : ℤ) (ω : ℂ) (q e : ℝ)
    {r : ℝ} (hr : b.rPlus < r) :
    radialMultiplier b m ω q r * rescaleFactor b m ω e r =
      Complex.exp (-Complex.I*b.eta*ω*r) * (Real.rpow (b.Delta r) (q+e):ℂ) * gauge b m ω r := by
  have hpow : (Real.rpow (b.Delta r) (q+e):ℂ) =
      (Real.rpow (b.Delta r) q:ℂ)*(Real.rpow (b.Delta r) e:ℂ) := by
    norm_cast; exact Real.rpow_add (b.Delta_pos hr) q e
  have hex : Complex.exp (-2*Complex.I*b.eta*ω*r)*Complex.exp (Complex.I*b.eta*ω*r) =
      Complex.exp (-Complex.I*b.eta*ω*r) := by
    rw [← Complex.exp_add]; congr 1; ring
  unfold radialMultiplier rescaleFactor
  rw [hpow, ← hex]
  have hH := gauge_ne_zero b m ω r
  field_simp

end KN.Boundary
