import KN.Analysis.WeakGraphIBP
import KN.Angular.FullMultiplier

namespace KN.Analysis
noncomputable section
open KN.Angular MeasureTheory Set
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The literal frequency coefficient in the full angular matrix. -/
def fullPerturbationMatrix (b : KN.Background) (σ : ℝ) (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  fullStaticPotential (-σ*b.a*b.kappa*Real.sin θ : ℂ) (σ*b.a*b.c*Real.cos θ : ℂ)

/-- Classical representatives of a full complex-frequency angular equation
belong to the actual maximal weak graph. The residual continuity is ordinary
interior regularity, not an operator-domain premise. -/
theorem fullFrequencyGraph_of_classical (b : KN.Background) (σ : ℝ) (m : ℤ) (omega : ℂ)
    (U V : FullAngularHilbert) (u v : ℝ → EuclideanSpace ℂ (Fin 4))
    (hU : U =ᵐ[angularMeasure] u) (hV : V =ᵐ[angularMeasure] v)
    (hu : ContDiffOn ℝ ∞ u (Ioo 0 Real.pi))
    (hv : ContinuousOn (fun θ => v θ-omega • (fullPerturbationMatrix b σ θ).toEuclideanLin (u θ)) (Ioo 0 Real.pi))
    (heq : ∀ θ ∈ Ioo 0 Real.pi,
      v θ=fullPrincipal.toEuclideanLin (deriv u θ)+
        (fullStaticPotential (staticCoefficient σ m θ : ℂ) (b.beta:ℂ)).toEuclideanLin (u θ)+
        omega • (fullPerturbationMatrix b σ θ).toEuclideanLin (u θ)) :
    FullFrequencyGraph b σ m omega U V := by
  have hres : (V-omega • fullFrequencyMultiplier b σ U : FullAngularHilbert) =ᵐ[angularMeasure]
      (fun θ => v θ-omega • (fullPerturbationMatrix b σ θ).toEuclideanLin (u θ)) := by
    filter_upwards [Lp.coeFn_sub V (omega • fullFrequencyMultiplier b σ U),
      Lp.coeFn_smul omega (fullFrequencyMultiplier b σ U),
      fullFrequencyMultiplier_ae b σ U,hU,hV] with θ hsub hsm hm hu hv
    rw [hsub]
    change V θ-(omega • fullFrequencyMultiplier b σ U) θ=_
    rw [hsm]
    change V θ-omega • (fullFrequencyMultiplier b σ U) θ=_
    rw [hm,hu,hv]
    rfl
  apply (MatrixWeakGraph.congr_ae _ _ hU hres).mpr
  apply matrixWeakGraph_of_classical _ _ u _ hu hv
  intro θ hθ
  rw [heq θ hθ]
  abel

/-- Explicit domain/action packaging for the canonical full operator. -/
theorem fullFrequencyOperator_of_classical (b : KN.Background) (hQ : b.Q≠0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (omega : ℂ)
    (U V : FullAngularHilbert) (u v : ℝ → EuclideanSpace ℂ (Fin 4))
    (hU : U =ᵐ[angularMeasure] u) (hV : V =ᵐ[angularMeasure] v)
    (hu : ContDiffOn ℝ ∞ u (Ioo 0 Real.pi))
    (hv : ContinuousOn (fun θ => v θ-omega • (fullPerturbationMatrix b σ θ).toEuclideanLin (u θ)) (Ioo 0 Real.pi))
    (heq : ∀ θ ∈ Ioo 0 Real.pi,
      v θ=fullPrincipal.toEuclideanLin (deriv u θ)+
        (fullStaticPotential (staticCoefficient σ m θ : ℂ) (b.beta:ℂ)).toEuclideanLin (u θ)+
        omega • (fullPerturbationMatrix b σ θ).toEuclideanLin (u θ)) :
    ∃ hmem : U ∈ (fullFrequencyOperator b hQ σ hσ m omega).domain,
      fullFrequencyOperator b hQ σ hσ m omega ⟨U,hmem⟩=V := by
  apply (fullFrequencyOperator_graph b hQ σ hσ m omega U V).mpr
  exact fullFrequencyGraph_of_classical b σ m omega U V u v hU hV hu hv heq

/-- Smooth interior representatives make the weak-graph residual continuous;
this is proved from the literal equation rather than supplied as source data. -/
theorem fullFrequencyOperator_of_smooth_classical (b : KN.Background) (hQ : b.Q≠0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (omega : ℂ)
    (U V : FullAngularHilbert) (u v : ℝ → EuclideanSpace ℂ (Fin 4))
    (hU : U =ᵐ[angularMeasure] u) (hV : V =ᵐ[angularMeasure] v)
    (hu : ContDiffOn ℝ ∞ u (Ioo 0 Real.pi))
    (heq : ∀ θ ∈ Ioo 0 Real.pi,
      v θ=fullPrincipal.toEuclideanLin (deriv u θ)+
        (fullStaticPotential (staticCoefficient σ m θ : ℂ) (b.beta:ℂ)).toEuclideanLin (u θ)+
        omega • (fullPerturbationMatrix b σ θ).toEuclideanLin (u θ)) :
    ∃ hmem : U ∈ (fullFrequencyOperator b hQ σ hσ m omega).domain,
      fullFrequencyOperator b hQ σ hσ m omega ⟨U,hmem⟩=V := by
  apply fullFrequencyOperator_of_classical b hQ σ hσ m omega U V u v hU hV hu ?_ heq
  have hg : ContinuousOn (fun θ => (staticCoefficient σ m θ : ℂ)) (Ioo 0 Real.pi) := by
    apply Complex.continuous_ofReal.comp_continuousOn
    unfold staticCoefficient
    apply ContinuousOn.add
    · exact (continuousOn_const.mul Real.continuous_cos.continuousOn).div
        Real.continuous_sin.continuousOn (fun θ hθ => (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne')
    · exact continuousOn_const.div Real.continuous_sin.continuousOn
        (fun θ hθ => (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne')
  have hd : ContinuousOn (deriv u) (Ioo 0 Real.pi) :=
    (hu.deriv_of_isOpen isOpen_Ioo (m := 0) (by simp)).continuousOn
  have hpot : ContinuousOn (fun θ =>
      (fullStaticPotential (staticCoefficient σ m θ : ℂ) (b.beta:ℂ)).toEuclideanLin (u θ))
      (Ioo 0 Real.pi) := by
    have hh := ((fullStaticPotential 1 0).toEuclideanLin.toContinuousLinearMap.continuous.comp_continuousOn
      (hg.smul hu.continuousOn)).add
      ((fullStaticPotential 0 1).toEuclideanLin.toContinuousLinearMap.continuous.comp_continuousOn
      ((continuousOn_const (c := (b.beta:ℂ))).smul hu.continuousOn : ContinuousOn (fun θ => (b.beta:ℂ) • u θ) _))
    apply hh.congr
    intro θ _
    simpa using (fullStaticPotential_sin_cos 1 1 (staticCoefficient σ m θ : ℂ) (b.beta:ℂ) (u θ)).symm
  apply (fullPrincipal.toEuclideanLin.toContinuousLinearMap.continuous.comp_continuousOn hd |>.add hpot).congr
  intro θ hθ
  change v θ - omega • _ = fullPrincipal.toEuclideanLin (deriv u θ) + _
  rw [heq θ hθ]
  abel

end
end KN.Analysis
