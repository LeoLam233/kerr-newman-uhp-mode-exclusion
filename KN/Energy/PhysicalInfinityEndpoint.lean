import KN.Energy.InfinityEnergy

noncomputable section
open Filter Set Asymptotics
namespace KN.Energy

theorem physical_infinity_energy_flux_bounds (positive : Bool) (b : KN.Background)
    (ω : ℂ) (hω : 0 < ω.im) (T L σ D : ℝ) (Y Yp : ℝ → ℂ)
    (hY : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Y (-r)))
    (hYp : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Yp (-r))) :
    density ω (systemP positive b) (systemW positive b) (angularK b T L σ)
      (fun x => radialR b x-D) (gaugedU b ω Y) (gaugedV b ω Y Yp)
        =O[atBot] (fun x : ℝ => Real.exp ((ω.im*b.delta)*x)) ∧
    current ω (systemP positive b) (gaugedU b ω Y) (gaugedV b ω Y Yp)
        =O[atBot] (fun x : ℝ => Real.exp ((ω.im*b.delta)*x)) := by
  obtain ⟨hU,hV⟩ := reflected_gauged_growth b ω Y Yp hY hYp
  obtain ⟨hP,hW,hk,hB⟩ := physical_reflected_coefficients positive b T L σ D
  constructor
  · apply reflected_growth_atBot _ (ω.im*b.delta) (mul_pos hω b.delta_pos)
    have hd := density_expPolyGrowth ω (fun r => systemP positive b (-r))
      (fun r => systemW positive b (-r)) (fun r => angularK b T L σ (-r))
      (fun r => radialR b (-r)-D) (fun r => gaugedU b ω Y (-r))
      (fun r => gaugedV b ω Y Yp (-r)) (-ω.im*b.delta) hP hW hk hB hU hV
    simpa only [neg_mul,density] using hd
  · apply reflected_growth_atBot _ (ω.im*b.delta) (mul_pos hω b.delta_pos)
    have hc := current_expPolyGrowth ω (fun r => systemP positive b (-r))
      (fun r => gaugedU b ω Y (-r)) (fun r => gaugedV b ω Y Yp (-r))
      (-ω.im*b.delta) hP hU hV
    simpa only [neg_mul,current] using hc

theorem physical_infinity_flux_zero (positive : Bool) (b : KN.Background)
    (ω : ℂ) (hω : 0 < ω.im) (Y Yp : ℝ → ℂ)
    (hY : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Y (-r)))
    (hYp : ExpPolyGrowth (-ω.im*b.rPlus) (fun r => Yp (-r))) :
    Tendsto (current ω (systemP positive b) (gaugedU b ω Y) (gaugedV b ω Y Yp))
      atBot (nhds 0) := by
  exact infinity_flux_zero _ ω.im b.delta hω b.delta_pos
    (physical_infinity_energy_flux_bounds positive b ω hω 0 0 0 0 Y Yp hY hYp).2

end KN.Energy
