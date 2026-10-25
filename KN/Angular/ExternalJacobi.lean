import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# General classical trigonometric Jacobi spectral interface

Source: G. Szegő, Orthogonal Polynomials, fourth edition, AMS Colloquium
Publications 23 (1975), Jacobi chapter; NIST DLMF Table 18.5.1 (Rodrigues),
Table 18.8.1 row 2 (trigonometric differential equation), and §18.2(viii)
(completeness on a bounded interval). URLs https://dlmf.nist.gov/18.5,
https://dlmf.nist.gov/18.8, https://dlmf.nist.gov/18.2.viii .

This is the general α,β≥0 scalar Jacobi theorem, not an angular Dirac or
Kerr–Newman spectrum assertion. The canonical regular solution has exponent
α+1/2 at zero and β+1/2 at pi; the logarithmic branch at α=0 or β=0 is not
included. Identification with a first-order square still has to be proved.
-/
namespace KN.Angular.Jacobi
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace

def intervalMeasure : Measure ℝ := volume.restrict (Set.Ioo 0 Real.pi)
abbrev H := Lp ℂ 2 intervalMeasure

/-- Classical Rodrigues normalization on -1<x<1. -/
def polynomial (α β : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ)^n / (2^n * (n.factorial : ℝ)) *
    Real.rpow (1-x) (-α) * Real.rpow (1+x) (-β) *
      iteratedDeriv n (fun t : ℝ =>
        Real.rpow (1-t) ((n : ℝ)+α) * Real.rpow (1+t) ((n : ℝ)+β)) x

/-- General trigonometric Jacobi functions, before L² normalization. -/
def regularFunction (α β : ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  Real.rpow (Real.sin (θ/2)) (α+1/2) *
    Real.rpow (Real.cos (θ/2)) (β+1/2) * polynomial α β n (Real.cos θ)

def potential (α β θ : ℝ) : ℝ :=
  (α^2-1/4)/(4*(Real.sin (θ/2))^2) +
    (β^2-1/4)/(4*(Real.cos (θ/2))^2)

/-- Named general classical L² fact, with no angular-background parameters. -/
axiom regular_memLp (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
  MemLp (fun θ => (regularFunction α β n θ : ℂ)) 2 intervalMeasure

def regularVector (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) : H :=
  (regular_memLp α β hα hβ n).toLp (fun θ => (regularFunction α β n θ : ℂ))

def normalizedVector (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) : H :=
  ((‖regularVector α β hα hβ n‖⁻¹ : ℝ) : ℂ) • regularVector α β hα hβ n

/-- Published general Jacobi completeness and normalization. -/
axiom orthonormal_complete (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
  Orthonormal ℂ (normalizedVector α β hα hβ) ∧
  Dense (Submodule.span ℂ (Set.range (normalizedVector α β hα hβ)) : Set H)

/-- Published general Jacobi differential equation, Table 18.8.1 row 2. -/
axiom regular_differential_equation (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (n : ℕ) (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
  -deriv (deriv (regularFunction α β n)) θ + potential α β θ*regularFunction α β n θ =
    ((n : ℝ)+(α+β+1)/2)^2*regularFunction α β n θ

/-- Published regularity away from the two regular-singular endpoints. -/
axiom regular_smooth (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (n : ℕ) :
  ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (regularFunction α β n) (Set.Ioo 0 Real.pi)

end
end KN.Angular.Jacobi
