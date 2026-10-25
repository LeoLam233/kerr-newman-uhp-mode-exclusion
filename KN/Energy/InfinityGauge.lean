import KN.Energy.TailGrowth
import KN.Energy.PhysicalFiniteEndpoint

noncomputable section
open Filter Set Asymptotics
namespace KN.Energy
open KN.Boundary

theorem inverseGauge_expPolyGrowth (ω : ℂ) (M c : ℝ) :
    ExpPolyGrowth (ω.im*M) (fun r : ℝ => inverseGauge ω M (-c) (-r)) := by
  apply expPolyGrowth_of_norm_exp_mul _ _ _
    (shifted_rpow_polyBound c (2*M*ω.im))
  filter_upwards [eventually_gt_atTop c] with r hr
  rw [inverseGauge_norm ω M (-c) (-r) (by linarith)]
  have ht : -c- -r = r-c := by ring
  rw [ht]
  simp only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hr.le) _)]
  congr 2
  ring

theorem reflected_phase_polyBound (b : KN.Background) (ω : ℂ) :
    PolyBound (fun r : ℝ => Complex.I*ω*(b.M*(1+2/(-b.h- -r)):ℝ)) := by
  have hh := reciprocal_polyBound b.h
  have hsum := polyBound_add (polyBound_const (1:ℂ)) (polyBound_mul (polyBound_const (2:ℂ)) hh)
  have hmul := polyBound_mul (polyBound_const (Complex.I*ω*b.M)) hsum
  convert hmul using 1
  ext r
  dsimp [reciprocal]
  push_cast
  rw [show -(b.h:ℂ)- -(r:ℂ)=(r:ℂ)-b.h by ring]
  ring

theorem reflected_gauged_growth (b : KN.Background) (ω : ℂ) (Y Yp : ℝ → ℂ)
    (hY : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Y (-r)))
    (hYp : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Yp (-r))) :
    ExpPolyGrowth (-ω.im*b.delta) (fun r => gaugedU b ω Y (-r)) ∧
    ExpPolyGrowth (-ω.im*b.delta) (fun r => gaugedV b ω Y Yp (-r)) := by
  have hg := inverseGauge_expPolyGrowth ω b.M b.h
  have he : ω.im*b.M + -ω.im*b.rPlus = -ω.im*b.delta := by
    unfold KN.Background.rPlus
    ring
  constructor
  · simpa only [he, gaugedU] using hg.mul hY
  · have hh := hY.mul_poly (reflected_phase_polyBound b ω)
    have hsum := hYp.add hh
    have hmul := hg.mul hsum
    rw [he] at hmul
    convert hmul using 1
    ext r
    dsimp [gaugedV]
    ring

theorem reflected_growth_of_atBot_bound (Y : ℝ → ℂ) (k : ℝ) (N : ℕ)
    (hY : Y =O[atBot] (fun x : ℝ => (1+|x|)^N*Real.exp (k*x))) :
    ExpPolyGrowth (-k) (fun r => Y (-r)) := by
  have h := hY.comp_tendsto tendsto_neg_atTop_atBot
  refine ⟨N,?_⟩
  change (fun r : ℝ => Y (-r)) =O[atTop]
    (fun r : ℝ => (1+|-r|)^N*Real.exp (k*(-r))) at h
  simpa only [abs_neg,mul_neg,neg_mul] using h

end KN.Energy
