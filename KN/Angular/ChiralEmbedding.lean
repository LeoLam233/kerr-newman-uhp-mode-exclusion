import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace KN.Angular
open Matrix
noncomputable section

/-- Combined +i-chiral identification and real Hadamard rotation. -/
def chiralEmbedding : Matrix (Fin 4) (Fin 2) ℂ :=
  !![Complex.I/2,Complex.I/2; 1/2,1/2; -Complex.I/2,Complex.I/2; 1/2,-1/2]

def fullPrincipal : Matrix (Fin 4) (Fin 4) ℂ :=
  !![Complex.I,0,0,0; 0,Complex.I,0,0; 0,0,-Complex.I,0; 0,0,0,-Complex.I]

def fullStaticPotential (g β : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,Complex.I*g,-Complex.I*β;
     0,0,-Complex.I*β,-Complex.I*g;
     -Complex.I*g,Complex.I*β,0,0;
     Complex.I*β,Complex.I*g,0,0]

def massPrincipal : Matrix (Fin 2) (Fin 2) ℂ := !![0,Complex.I;Complex.I,0]
def massPotential (g β : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-β,Complex.I*g;-Complex.I*g,β]

theorem chiral_isometry : chiralEmbedding.conjTranspose * chiralEmbedding = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chiralEmbedding, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      Complex.conj_I, Complex.I_sq, map_ofNat] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem chiral_principal : fullPrincipal * chiralEmbedding = chiralEmbedding * massPrincipal := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fullPrincipal,chiralEmbedding,massPrincipal,Matrix.mul_apply,Fin.sum_univ_succ,
      Complex.I_sq] <;> ring

theorem chiral_potential (g β : ℂ) :
    fullStaticPotential g β * chiralEmbedding = chiralEmbedding * massPotential g β := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fullStaticPotential,chiralEmbedding,massPotential,Matrix.mul_apply,Fin.sum_univ_succ]
      <;> ring_nf <;> simp [Complex.I_sq] <;> ring

open scoped ComplexInnerProductSpace

def chiralIsometry : EuclideanSpace ℂ (Fin 2) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 4) :=
  chiralEmbedding.toEuclideanLin.isometryOfInner (by
    intro x y
    rw [← LinearMap.adjoint_inner_right,
      ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change ⟪x, (chiralEmbedding.conjTranspose.toEuclideanLin.comp
      chiralEmbedding.toEuclideanLin) y⟫ = ⟪x,y⟫
    rw [← Matrix.toLpLin_mul 2 2 2, chiral_isometry, Matrix.toLpLin_one]
    rfl)

/-- Constant chiral embedding commutes with the actual Bochner test integrals,
including the zero-value convention for nonintegrable functions. -/
theorem chiral_integral {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (f : X → EuclideanSpace ℂ (Fin 2)) :
    (∫ x, chiralIsometry (f x) ∂μ) = chiralIsometry (∫ x, f x ∂μ) :=
  chiralIsometry.integral_comp_comm f

end
end KN.Angular
