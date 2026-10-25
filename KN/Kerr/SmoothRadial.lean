import KN.Kerr.Intertwiner
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

import Mathlib.Analysis.Calculus.Deriv.Linear

open scoped ContDiff

namespace KN.Kerr

/-- Complex-valued infinitely differentiable functions of a real radial coordinate. -/
def smoothRadialAlgebra : Subalgebra ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ ∞ f}
  mul_mem' := by
    intro f g hf hg
    exact ContDiff.mul (show ContDiff ℝ ∞ f from hf) (show ContDiff ℝ ∞ g from hg)
  add_mem' := by
    intro f g hf hg
    exact ContDiff.add (show ContDiff ℝ ∞ f from hf) (show ContDiff ℝ ∞ g from hg)
  algebraMap_mem' := by
    intro c
    change ContDiff ℝ ∞ (fun _ : ℝ => c)
    exact contDiff_const

def SmoothRadial := smoothRadialAlgebra

instance : CommRing SmoothRadial := inferInstanceAs (CommRing smoothRadialAlgebra)
instance : Algebra ℂ SmoothRadial := inferInstanceAs (Algebra ℂ smoothRadialAlgebra)

noncomputable def radialDerivation : Derivation ℂ SmoothRadial SmoothRadial where
  toFun f := ⟨deriv f.val, (contDiff_infty_iff_deriv.mp f.property).2⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    exact deriv_add ((contDiff_infty_iff_deriv.mp f.property).1 x)
      ((contDiff_infty_iff_deriv.mp g.property).1 x)
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact deriv_const_smul c ((contDiff_infty_iff_deriv.mp f.property).1 x)
  map_one_eq_zero' := by
    apply Subtype.ext
    funext x
    exact deriv_const x (1 : ℂ)
  leibniz' f g := by
    apply Subtype.ext
    funext x
    change deriv (fun x => f.val x * g.val x) x =
      f.val x * deriv g.val x + g.val x * deriv f.val x
    rw [deriv_fun_mul ((contDiff_infty_iff_deriv.mp f.property).1 x)
      ((contDiff_infty_iff_deriv.mp g.property).1 x)]
    ring

noncomputable def radialCoordinate : SmoothRadial :=
  ⟨fun r : ℝ => (r : ℂ), by
    change ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ))
    exact Complex.ofRealCLM.contDiff⟩

@[simp] theorem radialDerivation_coordinate :
    radialDerivation radialCoordinate = 1 := by
  apply Subtype.ext
  funext x
  change deriv (fun r : ℝ => (r : ℂ)) x = 1
  exact Complex.ofRealCLM.hasDerivAt.deriv

/-- The spin-one identity acts on actual smooth radial functions. -/
theorem smooth_intertwiner_one (M a m omega Λ : ℂ) (f : SmoothRadial) :
    radialDerivation (radialDerivation
      (radialOperator radialDerivation radialCoordinate M a m omega Λ 1 f)) =
    radialOperator radialDerivation radialCoordinate M a m omega Λ (-1)
      (radialDerivation (radialDerivation f)) :=
  intertwiner_spin_one radialDerivation radialCoordinate M a m omega Λ
    radialDerivation_coordinate f

/-- The spin-two identity acts on actual smooth radial functions, without
excluding the exceptional frequency or requiring a horizon leading coefficient. -/
theorem smooth_intertwiner_two (M a m omega Λ : ℂ) (f : SmoothRadial) :
    radialDerivation (radialDerivation (radialDerivation (radialDerivation
      (radialOperator radialDerivation radialCoordinate M a m omega Λ 2 f)))) =
    radialOperator radialDerivation radialCoordinate M a m omega Λ (-2)
      (radialDerivation (radialDerivation (radialDerivation (radialDerivation f)))) :=
  intertwiner_spin_two radialDerivation radialCoordinate M a m omega Λ
    radialDerivation_coordinate f

end KN.Kerr
