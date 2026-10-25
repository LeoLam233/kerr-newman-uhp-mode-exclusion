import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact scalar algebra in C002 (45)--(49). These statements do not assume
self-adjointness at complex frequency, and the indefinite real coefficient
is retained throughout. Analytic integration is a separate obligation. -/
namespace KN.Energy

/-- The imaginary part after multiplying the integrated equation by conjugate ω.
The real linear coefficient cancels identically, without any sign assumption. -/
theorem imaginary_energy_identity (ω : ℂ) (A K L B : ℝ) :
    (star ω * (-(A : ℂ) - K + ω * L + ω ^ 2 * B)).im =
      ω.im * (A + K + Complex.normSq ω * B) := by
  simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply, pow_two]
  ring

/-- Upper-half-plane coercivity forces the positive mass energy to vanish. -/
theorem mass_energy_eq_zero (ω : ℂ) (A K L B : ℝ)
    (hω : 0 < ω.im) (hA : 0 ≤ A) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (heq : -(A : ℂ) - K + ω * L + ω ^ 2 * B = 0) : B = 0 := by
  have hi := imaginary_energy_identity ω A K L B
  rw [heq, mul_zero, Complex.zero_im] at hi
  have hn : 0 < Complex.normSq ω := Complex.normSq_pos.mpr (by
    intro hz
    simp [hz] at hω)
  have hs : A + K + Complex.normSq ω * B = 0 := by nlinarith
  nlinarith

/-- Exact form of (46), after substituting y = -x-η and h=η+2.
The angular expectation is q=⟨sin²θ⟩, and η²+2η=c². -/
theorem B_exact (M a δ η c x q : ℝ) (hc : c ^ 2 = η ^ 2 + 2 * η) :
    (x + η)^2 * (δ^2 - 2*M^2/(x+η+2)) + a^2*η^2 - 2*a^2*x -
      a^2 * (c^2 + q) =
    (-x-η)^2 * (δ^2 + 2*M^2/(-x-η-2)) + 2*a^2*(-x-η) - a^2*q := by
  have hd : -x-η-2 = -(x+η+2) := by ring
  rw [hd, div_neg, hc]
  ring

/-- Strict positivity in (46), including a=0 and either sign of spin/charge. -/
theorem B_strict_positive (M a δ y q : ℝ) (hδ : 0 < δ)
    (hy : 2 < y) (hq : q ≤ 1) :
    0 < y^2 * (δ^2 + 2*M^2/(y-2)) + 2*a^2*y - a^2*q := by
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  have hy2 : 0 < y^2 := sq_pos_of_pos (by linarith)
  have hd : 0 ≤ 2*M^2/(y-2) := div_nonneg (by positivity) (by linarith)
  have hp : 0 < y^2 * (δ^2 + 2*M^2/(y-2)) := mul_pos hy2 (by linarith)
  have ha : 0 ≤ a^2 := sq_nonneg a
  have hq' : 0 ≤ a^2*(2*y-q) := mul_nonneg ha (by linarith)
  nlinarith

/-- Substitution of the two genuinely complex angular identities (18) into (43). -/
theorem angular_bracket_identity (ω lam : ℂ) (β T L v C D c σ h x am R : ℝ)
    (hlam : lam = L + ω*v)
    (hlam2 : lam^2 = β^2 + T + ω*C + ω^2*D)
    (hβ : β*c = 3*h/2) :
    (β:ℂ)^2 - lam^2 + (3*σ*h/2-c*lam)/x + 2*am*ω*x + ω^2*R =
      -((T:ℂ) + c/x*(L-σ*β)) + ω*(2*am*x-C-c/x*v) + ω^2*(R-D) := by
  have hb : (β:ℂ)*c = 3*h/2 := by exact_mod_cast hβ
  rw [hlam2, hlam]
  calc
    _ = -(T:ℂ) + (3*σ*h/2-c*L)/x + ω*(2*am*x-C-c/x*v) + ω^2*(R-D) := by ring
    _ = _ := by rw [show (3:ℂ)*σ*h/2 = σ*(β*c) by rw [hb]; ring]; ring

end KN.Energy
