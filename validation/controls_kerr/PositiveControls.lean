import KN.Kerr.FullFieldExclusion
import KN.Kerr.AsymptoticAlgebra
import KN.Kerr.SmoothRadial

open Set
open scoped ContDiff
namespace KN.Kerr.AuthorControls

/-- Schwarzschild M=1 has physical horizon angular velocity 0 and surface
 gravity 1/4. These positive-spin UHP frequencies have integral second roots. -/
example : (secondIndicialRoot 1 0 0 (1/4) (Complex.I/4)).re = 0 := by
  rw [secondIndicialRoot_re]
  norm_num
example : (secondIndicialRoot 2 0 0 (1/4) (Complex.I/4)).re = 1 := by
  rw [secondIndicialRoot_re]
  norm_num
example : (secondIndicialRoot 2 0 0 (1/4) (Complex.I/2)).re = 0 := by
  rw [secondIndicialRoot_re]
  norm_num
example : 0 < (Complex.I/4).im := by norm_num
example : (2*Complex.I*(Complex.I/4))^4 ≠ 0 :=
  outgoing_multiplier_nonzero _ (by norm_num) 4

/-- At the resonant UHP frequency the genuine spin-two differential identity
remains available with no non-special horizon premise. -/
example (f : SmoothRadial) (Λ : ℂ) :
    radialDerivation (radialDerivation (radialDerivation (radialDerivation
      (radialOperator radialDerivation radialCoordinate 1 0 0 (Complex.I/4) Λ 2 f)))) =
    radialOperator radialDerivation radialCoordinate 1 0 0 (Complex.I/4) Λ (-2)
      (radialDerivation (radialDerivation (radialDerivation (radialDerivation f)))) :=
  smooth_intertwiner_two 1 0 0 (Complex.I/4) Λ f

/-- Physical horizon preservation accepts every smooth coefficient, even one
whose differentiated leading coefficient vanishes. -/
example (b : KN.Background) :
    KN.Boundary.HorizonRegular b 0 (Complex.I/4) 2
      (reversedRadial b 0 (Complex.I/4) 2 4 (fun _ => 1)) :=
  reversedRadial_horizon_regular b 0 (Complex.I/4) 2 4 _ contDiffOn_const

/-- The final full-field theorem takes an actual Hilbert-valued field and no
chosen angular eigenfunction or separation constant. -/
example (b : KN.Background) (hQ : b.Q=0) (m s : ℤ) (omega : ℂ)
    (hs : s=1 ∨ s=2 ∨ s= -1 ∨ s= -2) (homega : 0<omega.im)
    (F : ℝ → AngularH) (hF : ContDiffOn ℝ ∞ F (Ioi b.rPlus))
    (heq : FullFieldEquation b m s omega F)
    (hh : KN.Boundary.HorizonRegular b m omega (-(s:ℝ)) F)
    (ho : KN.Boundary.Outgoing b m omega F) :
    ∀ r ∈ Ioi b.rPlus, F r=0 :=
  kerr_full_field_exclusion b hQ m s omega hs homega F hF heq hh ho

/-- If the strict indicial condition is removed, f(r)=r is a smooth solution
of r f''=0 whose horizon coefficient vanishes but which is not zero. -/
example : (ContDiff ℝ ∞ (fun r : ℝ => (r:ℂ))) ∧
    ((fun r : ℝ => (r:ℂ)) 0=0) ∧ ((fun r : ℝ => (r:ℂ)) 1≠0) ∧
    (∀ r : ℝ, (r:ℂ)*deriv (deriv (fun x : ℝ => (x:ℂ))) r=0) := by
  refine ⟨Complex.ofRealCLM.contDiff, by norm_num, by norm_num, ?_⟩
  intro r
  have hd : deriv (fun x : ℝ => (x:ℂ)) = fun _ => 1 := by
    funext x
    exact Complex.ofRealCLM.hasDerivAt.deriv
  rw [hd]
  simp

/-- The final positive-spin exclusion accepts the exceptional frequency with
physical smooth-horizon data, not an assumed non-special Frobenius branch. -/
example (b : KN.Background) (hQ : b.Q=0) (m : ℤ) (Λ : ℂ) (u R : ℝ → ℂ)
    (hu : RegularAngularEigenfunction b m 2 (Complex.I/4) Λ u)
    (hR : ContDiffOn ℝ ∞ R (Ioi b.rPlus))
    (heq : PhysicalRadialEquation b m (Complex.I/4) Λ 2 R)
    (hh : KN.Boundary.HorizonRegular b m (Complex.I/4) (-2) R)
    (ho : KN.Boundary.Outgoing b m (Complex.I/4) R) :
    ∀ r ∈ Ioi b.rPlus, R r=0 :=
  positive_spin_separated_exclusion b hQ m 2 (Complex.I/4) Λ
    (Or.inr rfl) (by norm_num) u R hu hR heq hh ho

end KN.Kerr.AuthorControls
