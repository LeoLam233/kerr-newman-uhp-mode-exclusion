import KN.Background.Parameters
import KN.Energy.Coercivity
import KN.Energy.Weights

namespace KN.Energy
noncomputable def radialR (b : KN.Background) (x : ℝ) : ℝ :=
  (x+b.eta)^2*(b.delta^2-2*b.M^2/(x+b.h))+b.a^2*b.eta^2-2*b.a^2*x

/-- Instantiates (46) in every actual signed subextremal KN background. -/
theorem physical_B_positive (b : KN.Background) (x q : ℝ)
    (hx : x < -b.h) (hq : q ≤ 1) :
    0 < radialR b x - b.a^2*(b.c^2+q) := by
  have hc : b.c^2 = b.eta^2+2*b.eta := by
    have hk := b.kappa_sq_sub_c_sq
    dsimp [KN.Background.kappa] at hk
    nlinarith
  dsimp [radialR, KN.Background.h]
  rw [← add_assoc x b.eta 2]
  rw [B_exact b.M b.a b.delta b.eta b.c x q hc]
  apply B_strict_positive b.M b.a b.delta (-x-b.eta) q b.delta_pos
  · dsimp [KN.Background.h] at hx
    linarith
  · exact hq

theorem physical_weights_positive (b : KN.Background) (x : ℝ) (hx : x < -b.h) :
    0 < Pplus b.eta x ∧ 0 < Wplus b.eta x ∧
      0 < Pminus b.eta x ∧ 0 < Wminus b.eta x :=
  weights_positive b.eta x b.eta_nonneg hx
end KN.Energy
