import KN.Analysis.FullChiralAlgebra
import KN.Angular.FullGraphSymmetry
import Mathlib.Analysis.Calculus.Deriv.Star

noncomputable section
namespace KN.Analysis
open KN.Angular KN.Physics MeasureTheory
open scoped ComplexConjugate
set_option backward.isDefEq.respectTransparency false

def conjugateFiber (N : ℕ) : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin N) where
  toFun u := WithLp.toLp 2 (fun i => star (u i))
  map_add' u v := by ext i; simp
  map_smul' c u := by ext i; simp
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [EuclideanSpace.norm_sq_eq]

theorem conjugateFiber_apply (N : ℕ) (u : EuclideanSpace ℂ (Fin N)) (i : Fin N) :
    conjugateFiber N u i=star (u i) := rfl

theorem conjugateFiber_smul (N : ℕ) (c : ℂ) (u : EuclideanSpace ℂ (Fin N)) :
    conjugateFiber N (c • u)=star c • conjugateFiber N u := by
  ext i
  simp [conjugateFiber_apply]

def fullConjugate : FullAngularHilbert →L[ℝ] FullAngularHilbert :=
  (conjugateFiber 4).toContinuousLinearMap.compLpL 2 angularMeasure

theorem fullConjugate_ae (u : FullAngularHilbert) :
    fullConjugate u =ᵐ[angularMeasure] fun θ => conjugateFiber 4 (u θ) :=
  (conjugateFiber 4).toContinuousLinearMap.coeFn_compLpL u

def fullRealStructure : FullAngularHilbert →L[ℝ] FullAngularHilbert :=
  (fullI.restrictScalars ℝ).comp fullConjugate

theorem conjugateFiber_principal (u : EuclideanSpace ℂ (Fin 4)) :
    conjugateFiber 4 (fullPrincipal.toEuclideanLin u)=
      -fullPrincipal.toEuclideanLin (conjugateFiber 4 u) := by
  ext i
  fin_cases i <;> simp [conjugateFiber_apply,Matrix.toLpLin_apply,
    fullPrincipal,dotProduct,Fin.sum_univ_succ]

theorem conjugateFiber_potential (g β : ℝ) (u : EuclideanSpace ℂ (Fin 4)) :
    conjugateFiber 4 ((fullStaticPotential g β).toEuclideanLin u)=
      -(fullStaticPotential g β).toEuclideanLin (conjugateFiber 4 u) := by
  ext i
  fin_cases i <;> simp [conjugateFiber_apply,Matrix.toLpLin_apply,
    fullStaticPotential,dotProduct,Fin.sum_univ_succ] <;> ring

theorem angularTest_conjugate {φ : ℝ → ℂ} (h : IsAngularTest φ) :
    IsAngularTest (fun θ => star (φ θ)) := by
  have ht : tsupport (fun θ => star (φ θ))=tsupport φ := by
    unfold tsupport
    congr 1
    ext θ
    simp
  exact ⟨Complex.conjCLE.contDiff.comp h.1,by simpa only [HasCompactSupport,ht] using h.2.1,
    by simpa only [ht] using h.2.2⟩

theorem fullWeakGraph_conjugate (σ β : ℝ) (m : ℤ)
    {u v : ℝ → EuclideanSpace ℂ (Fin 4)}
    (h : MatrixWeakGraph fullPrincipal
      (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ)) u v) :
    MatrixWeakGraph fullPrincipal
      (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
      (fun θ => conjugateFiber 4 (u θ)) (fun θ => -conjugateFiber 4 (v θ)) := by
  intro φ hφ
  have he := congrArg (fun w => -conjugateFiber 4 w) (h _ (angularTest_conjugate hφ))
  rw [← (conjugateFiber 4).integral_comp_comm,← (conjugateFiber 4).integral_comp_comm] at he
  simp only [map_add,conjugateFiber_smul,deriv.star',star_neg,star_star,
    conjugateFiber_principal,conjugateFiber_potential,smul_neg] at he
  simpa only [← integral_neg,neg_add_rev,neg_neg,smul_neg,neg_smul,add_comm] using he

theorem fullStaticGraph_conjugate (σ β : ℝ) (m : ℤ) {u v : FullAngularHilbert}
    (h : FullStaticGraph σ β m u v) :
    FullStaticGraph σ β m (fullConjugate u) (-fullConjugate v) := by
  apply (MatrixWeakGraph.congr_ae fullPrincipal
    (fun θ => fullStaticPotential (staticCoefficient σ m θ : ℂ) (β : ℂ))
    (fullConjugate_ae u) ?_).mpr (fullWeakGraph_conjugate σ β m h)
  filter_upwards [Lp.coeFn_neg (fullConjugate v),fullConjugate_ae v] with θ h1 h2
  rw [h1]
  change -fullConjugate v θ = _
  rw [h2]

theorem fullRealStructure_graph (σ β : ℝ) (m : ℤ) {u v : FullAngularHilbert}
    (h : FullStaticGraph σ β m u v) :
    FullStaticGraph σ β m (fullRealStructure u) (fullRealStructure v) := by
  have hI := fullStaticGraph_I σ β m (fullStaticGraph_conjugate σ β m h)
  change FullStaticGraph σ β m (fullI (fullConjugate u)) (fullI (fullConjugate v))
  simpa only [map_neg,neg_neg] using hI

theorem fullConjugate_smul (c : ℂ) (u : FullAngularHilbert) :
    fullConjugate (c • u)=star c • fullConjugate u := by
  apply Lp.ext
  filter_upwards [fullConjugate_ae (c • u),fullConjugate_ae u,
    Lp.coeFn_smul c u,Lp.coeFn_smul (star c) (fullConjugate u)] with θ h1 h2 h3 h4
  rw [h1,h3,h4]
  simp only [Pi.smul_apply]
  rw [h2,conjugateFiber_smul]

theorem fullRealStructure_smul (c : ℂ) (u : FullAngularHilbert) :
    fullRealStructure (c • u)=star c • fullRealStructure u := by
  change fullI (fullConjugate (c • u))=_
  rw [fullConjugate_smul,map_smul]
  rfl

theorem fullConjugate_norm (u : FullAngularHilbert) : ‖fullConjugate u‖=‖u‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [fullConjugate_ae u] with θ hθ
  rw [hθ,(conjugateFiber 4).norm_map]

theorem fullRealStructure_norm (u : FullAngularHilbert) : ‖fullRealStructure u‖=‖u‖ := by
  change ‖fullI (fullConjugate u)‖=‖u‖
  rw [fullI_norm,fullConjugate_norm]

theorem fullRealStructure_ne_zero {u : FullAngularHilbert} (hu : u ≠ 0) :
    fullRealStructure u ≠ 0 := by
  intro h
  have hn := fullRealStructure_norm u
  rw [h,norm_zero] at hn
  exact hu (norm_eq_zero.mp hn.symm)

end KN.Analysis
