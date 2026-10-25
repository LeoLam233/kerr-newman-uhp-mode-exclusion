import KN.Energy.WeightAsymptotics
import KN.Energy.EnergyAsymptotics
import KN.Energy.Endpoints

open Filter Set Asymptotics
open scoped Topology
namespace KN.Energy
noncomputable def systemP (positive : Bool) (b : KN.Background) : ℝ → ℝ :=
  if positive then Pplus b.eta else Pminus b.eta
noncomputable def systemW (positive : Bool) (b : KN.Background) : ℝ → ℝ :=
  if positive then Wplus b.eta else Wminus b.eta
noncomputable def angularK (b : KN.Background) (T L σ : ℝ) (x : ℝ) :=
  T+b.c/x*(L-σ*b.beta)
noncomputable def gaugedU (b : KN.Background) (ω : ℂ) (Y : ℝ → ℂ) (x : ℝ) :=
  inverseGauge ω b.M (-b.h) x*Y x
noncomputable def gaugedV (b : KN.Background) (ω : ℂ) (Y Yp : ℝ → ℂ) (x : ℝ) :=
  inverseGauge ω b.M (-b.h) x*(Yp x+Complex.I*ω*(b.M*(1+2/(-b.h-x)):ℝ)*Y x)

theorem systemP_horizon_order (positive : Bool) (b : KN.Background) :
    systemP positive b =O[𝓝[<] (-b.h)] (fun x => -b.h-x) := by
  cases positive
  · exact (P_horizon_orders b).2
  · exact (P_horizon_orders b).1

theorem systemW_continuous_at_horizon (positive : Bool) (b : KN.Background) :
    ContinuousAt (systemW positive b) (-b.h) := by
  cases positive
  · exact (W_continuous_at_horizon b).2
  · exact (W_continuous_at_horizon b).1

theorem angularK_continuous_at_horizon (b : KN.Background) (T L σ : ℝ) :
    ContinuousAt (angularK b T L σ) (-b.h) := by
  have hn : -b.h ≠ 0 := neg_ne_zero.mpr (ne_of_gt b.h_pos)
  change ContinuousAt (fun x : ℝ => T+b.c/x*(L-σ*b.beta)) (-b.h)
  fun_prop

/-- All three physical energy terms have the correct finite-endpoint order.
The only field hypotheses here are Y,Y' continuous across the endpoint,
as supplied by the interior holomorphy of the Laplace transform. -/
theorem physical_finite_energy_order (positive : Bool) (b : KN.Background) (ω : ℂ)
    (T L σ D : ℝ) (Y Yp : ℝ → ℂ)
    (hY : ContinuousAt Y (-b.h)) (hYp : ContinuousAt Yp (-b.h)) :
    density ω (systemP positive b) (systemW positive b) (angularK b T L σ)
      (fun x => radialR b x-D) (gaugedU b ω Y) (gaugedV b ω Y Yp) =O[𝓝[<] (-b.h)]
      (fun x : ℝ => (-b.h-x)^(4*b.M*ω.im-1)) := by
  have hw : systemW positive b =O[𝓝[<] (-b.h)] (fun _ => (1:ℝ)) :=
    (systemW_continuous_at_horizon positive b).isBigO.mono nhdsWithin_le_nhds
  have hkc : ContinuousAt (fun x => systemW positive b x*angularK b T L σ x) (-b.h) :=
    (systemW_continuous_at_horizon positive b).mul (angularK_continuous_at_horizon b T L σ)
  have hk : (fun x => systemW positive b x*angularK b T L σ x) =O[𝓝[<] (-b.h)]
      (fun x => 1/(-b.h-x)) :=
    (hkc.isBigO.mono nhdsWithin_le_nhds).trans (one_isBigO_horizon_pole (-b.h))
  have hB : (fun x => systemW positive b x*(radialR b x-D)) =O[𝓝[<] (-b.h)]
      (fun x => 1/(-b.h-x)) := by simpa only [one_mul] using hw.mul (B_horizon_order b D)
  have h := density_horizon_order ω (systemP positive b) (systemW positive b)
    (angularK b T L σ) (fun x => radialR b x-D) (gaugedU b ω Y) (gaugedV b ω Y Yp)
    (-b.h) (2*b.M*ω.im) (systemP_horizon_order positive b) hk hB
    (gauged_endpoint_bound ω b.M (-b.h) Y hY)
    (gauged_derivative_endpoint_bound ω b.M (-b.h) Y Yp hY hYp)
  convert h using 1
  ext x
  congr 1
  ring

/-- The exact physical boundary current tends to zero at x=-h, for either
system and every positive imaginary frequency. -/
theorem physical_finite_flux_zero (positive : Bool) (b : KN.Background) (ω : ℂ)
    (hω : 0 < ω.im) (Y Yp : ℝ → ℂ)
    (hY : ContinuousAt Y (-b.h)) (hYp : ContinuousAt Yp (-b.h)) :
    Tendsto (current ω (systemP positive b) (gaugedU b ω Y) (gaugedV b ω Y Yp))
      (𝓝[<] (-b.h)) (𝓝 0) := by
  apply horizon_flux_zero _ (-b.h) b.M ω.im b.mass_pos hω
  have h := current_horizon_order ω (systemP positive b) (gaugedU b ω Y) (gaugedV b ω Y Yp)
    (-b.h) (2*b.M*ω.im) (systemP_horizon_order positive b)
    (gauged_endpoint_bound ω b.M (-b.h) Y hY)
    (gauged_derivative_endpoint_bound ω b.M (-b.h) Y Yp hY hYp)
  convert h using 1
  ext x
  congr 1
  ring
end KN.Energy
