import KN.Analysis.FullClassicalGraph
import KN.Analysis.FullChiralAlgebra
import KN.Angular.FullField

namespace KN.Angular
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ContDiff

/-- Radial residual whose actual L² class is the angular operator image. -/
def fullRadialResidual (b : KN.Background) (σ : ℝ) (m : ℤ) (omega : ℂ)
    (F : ℝ → FullAngularHilbert) (r : ℝ) : FullAngularHilbert :=
  (Real.sqrt (b.Delta r) : ℂ) • deriv F r - radialR0 b σ m omega r • fullI (F r) -
    radialR1 b σ omega r • fullJ (F r)

theorem fullRadialResidual_ae (b : KN.Background) (σ : ℝ) (m : ℤ) (omega : ℂ)
    (F : ℝ → FullAngularHilbert) (f fr : ℝ → EuclideanSpace ℂ (Fin 4)) (r : ℝ)
    (hf : F r =ᵐ[angularMeasure] f) (hfr : deriv F r =ᵐ[angularMeasure] fr) :
    fullRadialResidual b σ m omega F r =ᵐ[angularMeasure] fun θ =>
      (Real.sqrt (b.Delta r) : ℂ) • fr θ -
        radialR0 b σ m omega r • KN.Physics.I4.toEuclideanLin (f θ) -
        radialR1 b σ omega r • KN.Physics.J4.toEuclideanLin (f θ) := by
  let d : ℂ := Real.sqrt (b.Delta r)
  let a := radialR0 b σ m omega r
  let c := radialR1 b σ omega r
  filter_upwards [Lp.coeFn_sub (d • deriv F r-a • fullI (F r)) (c • fullJ (F r)),
    Lp.coeFn_sub (d • deriv F r) (a • fullI (F r)),Lp.coeFn_smul d (deriv F r),
    Lp.coeFn_smul a (fullI (F r)),Lp.coeFn_smul c (fullJ (F r)),
    fullI_ae (F r),KN.Analysis.fullJ_ae (F r),hf,hfr] with θ h1 h2 h3 h4 h5 hi hj hf hfr
  change (d • deriv F r-a • fullI (F r)-c • fullJ (F r)) θ=_
  rw [h1]
  change (d • deriv F r-a • fullI (F r)) θ-(c • fullJ (F r)) θ=_
  rw [h2]
  change (d • deriv F r) θ-(a • fullI (F r)) θ-(c • fullJ (F r)) θ=_
  rw [h3,h4,h5]
  change d • deriv F r θ-a • fullI (F r) θ-c • fullJ (F r) θ=_
  rw [hi,hj,hf,hfr]
  rfl

/-- Assembly from ordinary classical representatives and genuine L² radial
calculus. Maximal angular-domain membership and action are derived, not inputs. -/
def fullField_of_classical (b : KN.Background) (hQ : b.Q≠0)
    (σ : ℝ) (hσ : σ=1 ∨ σ= -1) (m : ℤ) (omega : ℂ)
    (F : ℝ → FullAngularHilbert) (f : ℝ → ℝ → EuclideanSpace ℂ (Fin 4))
    (hF : ContDiffOn ℝ ∞ F (Ioi b.rPlus))
    (hrep : ∀ r, b.rPlus<r → F r =ᵐ[angularMeasure] f r)
    (hdr : ∀ r, b.rPlus<r → deriv F r =ᵐ[angularMeasure] fun θ => deriv (fun t => f t θ) r)
    (ha : ∀ r, b.rPlus<r → ContDiffOn ℝ ∞ (f r) (Ioo 0 Real.pi))
    (heq : ∀ r θ, b.rPlus<r → θ ∈ Ioo 0 Real.pi →
      (Real.sqrt (b.Delta r) : ℂ) • deriv (fun t => f t θ) r =
        fullPrincipal.toEuclideanLin (deriv (f r) θ)+
        (fullStaticPotential (staticCoefficient σ m θ : ℂ) (b.beta:ℂ)).toEuclideanLin (f r θ)+
        omega • (KN.Analysis.fullPerturbationMatrix b σ θ).toEuclideanLin (f r θ)+
        radialR0 b σ m omega r • KN.Physics.I4.toEuclideanLin (f r θ)+
        radialR1 b σ omega r • KN.Physics.J4.toEuclideanLin (f r θ))
    (hplus : KN.Boundary.HorizonRegular b m omega ((1-2*σ)/4) (fun r => fullPiPlus (F r)))
    (hminus : KN.Boundary.HorizonRegular b m omega ((1-4*σ)/4) (fun r => fullPiMinus (F r)))
    (hout : KN.Boundary.Outgoing b m omega F) :
    FullField b hQ σ hσ m omega := by
  have hg (r : ℝ) (hr : b.rPlus<r) :
      ∃ hm : F r ∈ (fullFrequencyOperator b hQ σ hσ m omega).domain,
      fullFrequencyOperator b hQ σ hσ m omega ⟨F r,hm⟩=fullRadialResidual b σ m omega F r := by
    apply KN.Analysis.fullFrequencyOperator_of_smooth_classical b hQ σ hσ m omega (F r) _ (f r)
      (fun θ => (Real.sqrt (b.Delta r) : ℂ) • deriv (fun t => f t θ) r -
        radialR0 b σ m omega r • KN.Physics.I4.toEuclideanLin (f r θ) -
        radialR1 b σ omega r • KN.Physics.J4.toEuclideanLin (f r θ))
      (hrep r hr) (fullRadialResidual_ae b σ m omega F _ _ r (hrep r hr) (hdr r hr))
      (ha r hr)
    intro θ hθ
    rw [heq r θ hr hθ]
    abel
  refine ⟨F,hF,(fun r hr => (hg r hr).choose),?_,hplus,hminus,hout⟩
  intro r hr
  rw [(hg r hr).choose_spec]
  unfold fullRadialResidual
  abel

end
end KN.Angular
