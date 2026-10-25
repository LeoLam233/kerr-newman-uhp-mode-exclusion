import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! Division-free radial elimination, C002 equations (28)--(29).

This module uses actual derivatives of complex-valued functions on the real line.
It makes no claim about the analytic horizon continuation or Fourier transform.
-/
noncomputable section
namespace KN.ChargedRadial

/-- The affine `R₁` of the radial equation. Its slope and intercept are complex. -/
def radialAffine (slope intercept : ℂ) (r : ℝ) : ℂ := slope * (r : ℂ) + intercept

def couplingA (slope intercept sigma lam : ℂ) (r : ℝ) : ℂ :=
  radialAffine slope intercept r + Complex.I * sigma * lam

def couplingB (slope intercept sigma lam : ℂ) (r : ℝ) : ℂ :=
  radialAffine slope intercept r - Complex.I * sigma * lam

lemma radialAffine_hasDerivAt (u v : ℂ) (r : ℝ) :
    HasDerivAt (radialAffine u v) u r := by
  convert ((Complex.ofRealCLM.hasDerivAt (x := r)).const_mul u).add_const v using 1 <;>
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
  rfl

lemma couplingA_hasDerivAt (u v s l : ℂ) (r : ℝ) :
    HasDerivAt (couplingA u v s l) u r := by
  exact (radialAffine_hasDerivAt u v r).add_const _

lemma couplingB_hasDerivAt (u v s l : ℂ) (r : ℝ) :
    HasDerivAt (couplingB u v s l) u r := by
  exact (radialAffine_hasDerivAt u v r).sub_const _

lemma coupling_product (u v s l : ℂ) (hs : s = 1 ∨ s = -1) (r : ℝ) :
    couplingA u v s l r * couplingB u v s l r =
      radialAffine u v r ^ 2 + l ^ 2 := by
  rcases hs with rfl | rfl <;>
    simp only [couplingA, couplingB] <;> ring_nf <;> simp [Complex.I_sq]

/-- Actual double differentiation eliminates the second radial component without
    division by either coupling. Both spin signs are included. -/
theorem division_free_third_order
    (u b s lam : ℂ) (hs : s = 1 ∨ s = -1)
    (Delta L v z : ℝ → ℂ)
    (hv : Differentiable ℝ v)
    (hz : ∀ r, HasDerivAt z (couplingB u b s lam r * v r) r)
    (hfirst : ∀ r, Delta r * deriv v r + L r * v r = couplingA u b s lam r * z r)
    (r : ℝ) :
    deriv (deriv (fun t => Delta t * deriv v t + L t * v t)) r
      - (radialAffine u b r ^ 2 + lam ^ 2) * deriv v r
      - (3 * radialAffine u b r - Complex.I * s * lam) * u * v r = 0 := by
  let A := couplingA u b s lam
  let B := couplingB u b s lam
  have hT : (fun t => Delta t * deriv v t + L t * v t) = fun t => A t * z t :=
    funext hfirst
  have hD : deriv (fun t => A t * z t) = fun t => u * z t + A t * (B t * v t) := by
    funext t
    exact ((couplingA_hasDerivAt u b s lam t).mul (hz t)).deriv
  rw [hT, hD]
  have hh : HasDerivAt (fun t => u * z t + A t * (B t * v t))
      (u * (B r * v r) + (u * (B r * v r) + A r * (u * v r + B r * deriv v r))) r :=
    HasDerivAt.add ((hz r).const_mul u)
    ((couplingA_hasDerivAt u b s lam r).mul
      ((couplingB_hasDerivAt u b s lam r).mul (hv r).hasDerivAt))
  rw [hh.deriv]
  have hp := coupling_product u b s lam hs r
  change (u * (B r * v r) + (u * (B r * v r) + A r * (u * v r + B r * deriv v r))) - _ - _ = 0
  change A r * B r = _ at hp
  calc
    _ = (A r * B r - (radialAffine u b r ^ 2 + lam ^ 2)) * deriv v r +
      (2 * B r + A r - (3 * radialAffine u b r - Complex.I * s * lam)) * u * v r := by ring
    _ = 0 := by rw [hp]; dsimp [A, B, couplingA, couplingB]; ring

end KN.ChargedRadial
