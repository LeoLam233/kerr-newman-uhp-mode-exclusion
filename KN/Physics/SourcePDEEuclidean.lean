import KN.Physics.SourcePDEFour
import KN.Analysis.FullClassicalGraph
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace KN.Physics
noncomputable section
open Matrix
set_option backward.isDefEq.respectTransparency false

lemma sourceMulVec_differentiable (X : ℝ → ℝ → SourceMatrix)
    (y : ℝ → ℝ → Fin 2 → ℂ) {r θ : ℝ}
    (hX : ∀ i j, SourceDifferentiableAt (fun x t => X x t i j) r θ)
    (hy : ∀ i, SourceDifferentiableAt (fun x t => y x t i) r θ) (i : Fin 2) :
    SourceDifferentiableAt (fun x t => (X x t *ᵥ y x t) i) r θ := by
  simpa only [mulVec,dotProduct,Fin.sum_univ_two] using
    ((hX i 0).mul (hy 0)).add ((hX i 1).mul (hy 1))

lemma sourceFullVector_differentiable (positive : Bool) (b : Background)
    (u : ℝ → ℝ → Fin 4 → ℂ) {r θ : ℝ}
    (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi)
    (hu : ∀ i, SourceDifferentiableAt (fun x y => u x y i) r θ) (i : Fin 4) :
    SourceDifferentiableAt (fun x y => sourceFullVector positive b u x y i) r θ := by
  have hp := sourceMulVec_differentiable
    (fun x y => (physicalSourceMatrix b x y).adjugate) (sourceY positive 1 b u)
    (source_adjugate_differentiable b hr θ) (sourceY_differentiable positive b u hr hθ hπ hu 1)
  have hm := sourceMulVec_differentiable
    (fun x y => (physicalSourceMatrix b x y).conjTranspose) (sourceY positive (-1) b u)
    (source_star_differentiable b hr θ) (sourceY_differentiable positive b u hr hθ hπ hu (-1))
  fin_cases i
  · exact hp 0
  · exact hp 1
  · exact hm 0
  · exact hm 1

/-- The finite-dimensional Euclidean derivative is the vector of component derivatives. -/
lemma deriv_toLp_four (f : ℝ → Fin 4 → ℂ) {x : ℝ}
    (hf : ∀ i, DifferentiableAt ℝ (fun t => f t i) x) :
    deriv (fun t => WithLp.toLp 2 (f t)) x =
      WithLp.toLp 2 (fun i => deriv (fun t => f t i) x) := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℂ)).symm
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_pi.mpr (fun i => (hf i).hasDerivAt))
  exact h.deriv

/-- Genuine partial differentiability of the transformed Euclidean field,
derived solely from the original source components. -/
lemma sourceFullEuclidean_differentiable (positive : Bool) (b : Background)
    (u : ℝ → ℝ → Fin 4 → ℂ) {r θ : ℝ}
    (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi)
    (hu : ∀ i, SourceDifferentiableAt (fun x y => u x y i) r θ) :
    DifferentiableAt ℝ (fun x => WithLp.toLp 2 (sourceFullVector positive b u x θ)) r ∧
    DifferentiableAt ℝ (fun y => WithLp.toLp 2 (sourceFullVector positive b u r y)) θ := by
  have hd := sourceFullVector_differentiable positive b u hr hθ hπ hu
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℂ)).symm
  constructor
  · exact L.differentiableAt.comp r (differentiableAt_pi.mpr (fun i => (hd i).1))
  · exact L.differentiableAt.comp θ (differentiableAt_pi.mpr (fun i => (hd i).2))

/-- Euclidean-space form of the actual four-component transport identity. -/
theorem source_four_transport_euclidean (positive : Bool) (b : Background) (hQ : b.Q≠0)
    (m : ℤ) (omega : ℂ) (σ : ℝ) (hσ : (σ:ℂ)=sourceSign positive)
    (u : ℝ → ℝ → Fin 4 → ℂ)
    (hs : PublishedChiralSystem positive b m omega u)
    (hu : ∀ r θ, b.rPlus<r → 0<θ → θ<Real.pi →
      ∀ i, SourceDifferentiableAt (fun x y => u x y i) r θ)
    {r θ : ℝ} (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi) :
    (Real.sqrt (b.Delta r):ℂ) • deriv (fun x => WithLp.toLp 2 (sourceFullVector positive b u x θ)) r =
      derivativeMatrix.toEuclideanLin (deriv (fun y => WithLp.toLp 2 (sourceFullVector positive b u r y)) θ) +
      (angularMatrix (sourceAngularW b m omega σ θ) (sourceAngularT b omega σ θ)).toEuclideanLin
        (WithLp.toLp 2 (sourceFullVector positive b u r θ)) +
      KN.Angular.radialR0 b σ m omega r • I4.toEuclideanLin (WithLp.toLp 2 (sourceFullVector positive b u r θ)) +
      KN.Angular.radialR1 b σ omega r • J4.toEuclideanLin (WithLp.toLp 2 (sourceFullVector positive b u r θ)) := by
  have hd := sourceFullVector_differentiable positive b u hr hθ hπ (hu r θ hr hθ hπ)
  rw [deriv_toLp_four _ (fun i => (hd i).1), deriv_toLp_four _ (fun i => (hd i).2)]
  have h := source_four_transport positive b hQ m omega σ hσ u hs hu hr hθ hπ
  apply WithLp.ofLp_injective
  exact h

/-- Identification of the literal transformed angular coefficients with the
canonical static operator and its actual bounded complex-frequency potential. -/
lemma source_angular_matrix_identification (b : Background) (m : ℤ)
    (omega : ℂ) (σ θ : ℝ) :
    angularMatrix (sourceAngularW b m omega σ θ) (sourceAngularT b omega σ θ) =
      KN.Angular.fullStaticPotential (KN.Angular.staticCoefficient σ m θ : ℂ) (b.beta:ℂ) +
        omega • KN.Analysis.fullPerturbationMatrix b σ θ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [angularMatrix, sourceAngularW, sourceAngularT, KN.Angular.fullStaticPotential,
      KN.Angular.staticCoefficient, KN.Analysis.fullPerturbationMatrix] <;> ring

lemma source_angular_action_identification (b : Background) (m : ℤ)
    (omega : ℂ) (σ θ : ℝ) (v : EuclideanSpace ℂ (Fin 4)) :
    (angularMatrix (sourceAngularW b m omega σ θ) (sourceAngularT b omega σ θ)).toEuclideanLin v =
      (KN.Angular.fullStaticPotential (KN.Angular.staticCoefficient σ m θ : ℂ) (b.beta:ℂ)).toEuclideanLin v +
        omega • (KN.Analysis.fullPerturbationMatrix b σ θ).toEuclideanLin v := by
  rw [source_angular_matrix_identification]
  simp

end
end KN.Physics
