import KN.Energy.HorizonGauge
import KN.Energy.PhysicalSigns

open Filter Set Asymptotics
open scoped Topology
namespace KN.Energy

theorem simple_pole_isBigO (f g : ℝ → ℝ) (b : ℝ)
    (hf : ContinuousAt f b) (hg : ContinuousAt g b) :
    (fun x => f x+g x/(b-x)) =O[𝓝[<] b] (fun x => 1/(b-x)) := by
  have hfo : f =O[𝓝[<] b] (fun _ => (1:ℝ)) := hf.isBigO.mono nhdsWithin_le_nhds
  have hgo : g =O[𝓝[<] b] (fun _ => (1:ℝ)) := hg.isBigO.mono nhdsWithin_le_nhds
  have hgp : (fun x => g x/(b-x)) =O[𝓝[<] b] (fun x => 1/(b-x)) := by
    simpa only [one_mul, mul_one_div] using hgo.mul
      (isBigO_refl (fun x : ℝ => 1/(b-x)) (𝓝[<] b))
  exact (hfo.trans (one_isBigO_horizon_pole b)).add hgp

/-- P has a simple zero at the finite endpoint for each system sign. -/
theorem P_horizon_orders (b : KN.Background) :
    Pplus b.eta =O[𝓝[<] (-b.h)] (fun x => -b.h-x) ∧
    Pminus b.eta =O[𝓝[<] (-b.h)] (fun x => -b.h-x) := by
  have hn : -b.h ≠ 0 := neg_ne_zero.mpr (ne_of_gt b.h_pos)
  have he : -b.h+b.eta ≠ 0 := by dsimp [KN.Background.h]; linarith
  have hd : -b.h*(-b.h+b.eta)^2 ≠ 0 := mul_ne_zero hn (pow_ne_zero 2 he)
  have hp : ContinuousAt (fun x : ℝ => -1/(x*(x+b.eta)^2)) (-b.h) := by fun_prop
  have hm : ContinuousAt (fun x : ℝ => -(x+b.eta)^4/x) (-b.h) := by fun_prop
  constructor
  · have ho : (fun x : ℝ => -1/(x*(x+b.eta)^2)) =O[𝓝[<] (-b.h)] (fun _ => (1:ℝ)) :=
      hp.isBigO.mono nhdsWithin_le_nhds
    convert ho.mul (isBigO_refl (fun x : ℝ => -b.h-x) (𝓝[<] (-b.h))) using 1
    · ext x
      dsimp [Pplus, KN.Background.h]
      ring
    · simp only [one_mul]
  · have ho : (fun x : ℝ => -(x+b.eta)^4/x) =O[𝓝[<] (-b.h)] (fun _ => (1:ℝ)) :=
      hm.isBigO.mono nhdsWithin_le_nhds
    convert ho.mul (isBigO_refl (fun x : ℝ => -b.h-x) (𝓝[<] (-b.h))) using 1
    · ext x
      dsimp [Pminus, KN.Background.h]
      ring
    · simp only [one_mul]

/-- W has no finite-endpoint pole for either sign. -/
theorem W_continuous_at_horizon (b : KN.Background) :
    ContinuousAt (Wplus b.eta) (-b.h) ∧ ContinuousAt (Wminus b.eta) (-b.h) := by
  have hn : -b.h ≠ 0 := neg_ne_zero.mpr (ne_of_gt b.h_pos)
  have he : -b.h+b.eta ≠ 0 := by dsimp [KN.Background.h]; linarith
  have hd : -b.h*(-b.h+b.eta)^3 ≠ 0 := mul_ne_zero hn (pow_ne_zero 3 he)
  change ContinuousAt (fun x : ℝ => 1/(x*(x+b.eta)^3)) (-b.h) ∧
    ContinuousAt (fun x : ℝ => (x+b.eta)^3/x) (-b.h)
  constructor <;> fun_prop

/-- The actual B=R-D has at most a simple pole at x=-h. -/
theorem B_horizon_order (b : KN.Background) (D : ℝ) :
    (fun x => radialR b x-D) =O[𝓝[<] (-b.h)] (fun x => 1/(-b.h-x)) := by
  have ho := simple_pole_isBigO
    (fun x : ℝ => (x+b.eta)^2*b.delta^2+b.a^2*b.eta^2-2*b.a^2*x-D)
    (fun x : ℝ => 2*b.M^2*(x+b.eta)^2) (-b.h) (by fun_prop) (by fun_prop)
  refine ho.congr_left ?_
  intro x
  dsimp [radialR]
  have he : -b.h-x = -(x+b.h) := by ring
  rw [he, div_neg]
  ring
end KN.Energy
