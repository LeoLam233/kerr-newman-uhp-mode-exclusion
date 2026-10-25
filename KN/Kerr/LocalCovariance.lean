import KN.Kerr.ExteriorIntertwiner

namespace KN.Kerr
open Set Filter
open scoped ContDiff Topology

noncomputable def radialCovariant (p v : ℝ → ℂ) : ℝ → ℂ :=
  fun r => deriv v r - p r * v r

theorem radialCovariant_smooth {rp : ℝ} {p v : ℝ → ℂ}
    (hp : ContDiffOn ℝ ∞ p (Ioi rp)) (hv : ContDiffOn ℝ ∞ v (Ioi rp)) :
    ContDiffOn ℝ ∞ (radialCovariant p v) (Ioi rp) :=
  (hv.deriv_of_isOpen isOpen_Ioi (by simp)).sub (hp.mul hv)

theorem radialCovariant_iterate_smooth {rp : ℝ} {p v : ℝ → ℂ}
    (hp : ContDiffOn ℝ ∞ p (Ioi rp)) (hv : ContDiffOn ℝ ∞ v (Ioi rp)) (n : ℕ) :
    ContDiffOn ℝ ∞ ((radialCovariant p)^[n] v) (Ioi rp) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact radialCovariant_smooth hp ih

theorem deriv_congr_exterior {rp : ℝ} {f g : ℝ → ℂ}
    (h : ∀ r > rp, f r = g r) {r : ℝ} (hr : rp < r) : deriv f r = deriv g r := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioi.mem_nhds hr] with x hx
  exact h x hx

/-- Local gauge covariance for actual derivatives on an open half-line. -/
theorem local_gauge_covariance (rp : ℝ) (p qInv v : ℝ → ℂ)
    (hp : ContDiffOn ℝ ∞ p (Ioi rp))
    (hv : ContDiffOn ℝ ∞ v (Ioi rp))
    (hq : ∀ r > rp, HasDerivAt qInv (-p r * qInv r) r) (n : ℕ) :
    ∀ r > rp, iteratedDeriv n (fun x => qInv x * v x) r =
      qInv r * ((radialCovariant p)^[n] v) r := by
  induction n with
  | zero => intro r _; rfl
  | succ n ih =>
    intro r hr
    rw [iteratedDeriv_succ]
    rw [deriv_congr_exterior ih hr]
    have hd := ((radialCovariant_iterate_smooth hp hv n r hr).contDiffAt
      (isOpen_Ioi.mem_nhds hr)).differentiableAt (by simp)
    rw [((hq r hr).fun_mul hd.hasDerivAt).deriv, Function.iterate_succ_apply']
    dsimp [radialCovariant]
    ring

end KN.Kerr
