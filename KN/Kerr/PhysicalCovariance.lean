import KN.Kerr.LocalCovariance
import KN.Kerr.OutgoingDecay
import KN.Kerr.HorizonPreservation
import KN.Boundary.GaugeSmooth

namespace KN.Kerr
open Set
open scoped ContDiff

noncomputable def outgoingConnection (b : KN.Background) (m : ℤ) (omega : ℂ) (r : ℝ) : ℂ :=
  2 * Complex.I * b.frequencyK m omega r / (b.Delta r : ℂ)

/-- The inverse-square gauge has exactly the connection required by (58). -/
theorem inverse_square_gauge_hasDerivAt (b : KN.Background) (m : ℤ) (omega : ℂ)
    {r : ℝ} (hr : b.rPlus < r) :
    HasDerivAt (fun x => (KN.Boundary.gauge b m omega x ^ 2)⁻¹)
      (-outgoingConnection b m omega r * (KN.Boundary.gauge b m omega r ^ 2)⁻¹) r := by
  have hn := KN.Boundary.gauge_ne_zero b m omega r
  convert ((KN.Boundary.gauge_hasDerivAt b m omega hr).pow 2).inv (pow_ne_zero 2 hn) using 1
  dsimp [outgoingConnection]
  field_simp

/-- Actual outgoing-weighted field expressed through rational covariant derivatives. -/
theorem outgoing_reversal_identity
    (b : KN.Background) (m : ℤ) (omega : ℂ) (k n : ℕ) (R f : ℝ → ℂ)
    (hf : ContDiffOn ℝ ∞ f (Ici b.rPlus))
    (hrep : ∀ r ∈ Ioi b.rPlus, R r = ingoingFactor b m omega (k : ℝ) r * f r)
    (hp : ContDiffOn ℝ ∞ (outgoingConnection b m omega) (Ioi b.rPlus))
    (hv : ContDiffOn ℝ ∞ (fun r => (b.Delta r : ℂ)^k *
      (KN.Boundary.gauge b m omega r * R r)) (Ioi b.rPlus)) :
    ∀ r ∈ Ioi b.rPlus,
      KN.Boundary.gauge b m omega r * reversedRadial b m omega k n f r =
        (b.Delta r : ℂ)^k * ((radialCovariant (outgoingConnection b m omega))^[n]
          (fun x => (b.Delta x : ℂ)^k * (KN.Boundary.gauge b m omega x * R x))) r := by
  let v := fun x => (b.Delta x : ℂ)^k * (KN.Boundary.gauge b m omega x * R x)
  let qInv := fun x => (KN.Boundary.gauge b m omega x ^ 2)⁻¹
  have hfg : ∀ r > b.rPlus, f r = qInv r * v r := by
    intro r hr
    have hd := b.Delta_pos hr
    have hn := KN.Boundary.gauge_ne_zero b m omega r
    dsimp [v, qInv]
    rw [hrep r hr]
    dsimp [ingoingFactor]
    change f r = _ * ((b.Delta r : ℂ)^k * (_ * (_ * ((b.Delta r ^ (-(k:ℝ)) : ℝ):ℂ) * f r)))
    rw [Real.rpow_neg (le_of_lt hd), Real.rpow_natCast]
    push_cast
    have hdc : (b.Delta r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
    field_simp [hn, hdc]
  have hiter : ∀ j r, b.rPlus < r → iteratedDeriv j f r =
      iteratedDeriv j (fun x => qInv x * v x) r := by
    intro j
    induction j with
    | zero => exact hfg
    | succ j ih =>
      intro r hr
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact deriv_congr_exterior ih hr
  intro r hr
  unfold reversedRadial
  rw [horizon_coefficient_derivatives_exterior hf n hr]
  rw [hiter n r hr, local_gauge_covariance b.rPlus (outgoingConnection b m omega) qInv v hp hv
    (fun _ hx => inverse_square_gauge_hasDerivAt b m omega hx) n r hr]
  change _ * (_ * ((b.Delta r ^ (k:ℝ) : ℝ):ℂ) * (qInv r * _)) = _
  rw [Real.rpow_natCast]
  push_cast
  dsimp [qInv, v]
  simp only [mul_assoc]
  have hn := KN.Boundary.gauge_ne_zero b m omega r
  field_simp

end KN.Kerr
