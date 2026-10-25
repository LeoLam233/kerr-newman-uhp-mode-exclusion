import KN.Physics.HorizonAlgebra
import KN.Boundary.Powers
import Mathlib.Analysis.Matrix.Normed

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix.Norms.Elementwise
open Set Matrix
namespace KN.Physics

lemma matrix_mulVec_smooth {s : Set ℝ}
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (u : ℝ → Fin 2 → ℂ)
    (hA : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) A s)
    (hu : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) u s) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r => A r *ᵥ u r) s := by
  apply contDiffOn_pi.mpr
  intro i
  change ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r => ∑ j : Fin 2, A r i j*u r j) s
  apply ContDiffOn.sum
  intro j hj
  exact ((contDiffOn_pi.mp (contDiffOn_pi.mp hA i)) j).mul (contDiffOn_pi.mp hu j)

/-- Positive-spin source transport in its exact square-root-cancelled form.
E and O are the horizon-smooth sum/difference matrices from HorizonAlgebra. -/
theorem positive_source_horizon_transport (b : KN.Background) (m : ℤ) (ω : ℂ)
    (A B E O : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (U V : ℝ → Fin 2 → ℂ)
    (hE : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) E (Ici b.rPlus))
    (hO : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) O (Ici b.rPlus))
    (hU : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) U (Ici b.rPlus))
    (hV : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) V (Ici b.rPlus))
    (hs : ∀ r>b.rPlus, A r+B r=(Real.sqrt (b.Delta r):ℂ) • E r)
    (hd : ∀ r>b.rPlus, A r-B r=O r) :
    KN.Boundary.HorizonRegular b m ω ((-1:ℝ)/4)
      (fun r => (KN.Boundary.gauge b m ω r*(Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ)) •
        (A r *ᵥ (U r+(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r) +
          B r *ᵥ (U r-(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r))) ∧
    KN.Boundary.HorizonRegular b m ω ((-3:ℝ)/4)
      (fun r => (KN.Boundary.gauge b m ω r*(Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ)) •
        (A r *ᵥ (U r+(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r) -
          B r *ᵥ (U r-(Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V r))) := by
  have hEU := matrix_mulVec_smooth E U hE hU
  have hOV := matrix_mulVec_smooth O V hO hV
  have hOU := matrix_mulVec_smooth O U hO hU
  have hEV := matrix_mulVec_smooth E V hE hV
  have hDelta : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r => (b.Delta r:ℂ)) (Ici b.rPlus) := by
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    exact (((contDiffOn_id.pow 2).sub (contDiffOn_const.mul contDiffOn_id)).add contDiffOn_const).add contDiffOn_const
  constructor
  · refine ⟨fun r => E r *ᵥ U r+Complex.I • (O r *ᵥ V r), hEU.add ((contDiffOn_const (c := Complex.I)).fun_smul hOV), ?_⟩
    intro r hr
    dsimp only
    rw [positive_horizon_sum _ _ _ _ _ _ _ (hs r hr) (hd r hr),smul_smul]
    rw [mul_assoc, KN.Boundary.positive_horizon_shift b hr]
  · refine ⟨fun r => O r *ᵥ U r+(Complex.I*(b.Delta r:ℂ)) • (E r *ᵥ V r),
      hOU.add (((contDiffOn_const (c := Complex.I)).mul hDelta).fun_smul hEV), ?_⟩
    intro r hr
    dsimp only
    rw [positive_horizon_difference _ _ _ _ _ _ _ (hs r hr) (hd r hr)]
    have ht : (Real.sqrt (b.Delta r):ℂ)^2=(b.Delta r:ℂ) := by
      norm_cast; exact Real.sq_sqrt (le_of_lt (b.Delta_pos hr))
    rw [ht]

/-- Negative-spin transport retains the distinct three-quarter and five-quarter weights. -/
theorem negative_source_horizon_transport (b : KN.Background) (m : ℤ) (ω : ℂ)
    (A B E O : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (U V : ℝ → Fin 2 → ℂ)
    (hE : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) E (Ici b.rPlus))
    (hO : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) O (Ici b.rPlus))
    (hU : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) U (Ici b.rPlus))
    (hV : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) V (Ici b.rPlus))
    (hs : ∀ r>b.rPlus, A r+B r=(Real.sqrt (b.Delta r):ℂ) • E r)
    (hd : ∀ r>b.rPlus, A r-B r=O r) :
    KN.Boundary.HorizonRegular b m ω ((3:ℝ)/4)
      (fun r => (KN.Boundary.gauge b m ω r*(Real.rpow (b.Delta r) ((3:ℝ)/4):ℂ)) •
        (A r *ᵥ ((Real.sqrt (b.Delta r):ℂ) • U r-Complex.I • V r) +
          B r *ᵥ ((Real.sqrt (b.Delta r):ℂ) • U r+Complex.I • V r))) ∧
    KN.Boundary.HorizonRegular b m ω ((5:ℝ)/4)
      (fun r => (KN.Boundary.gauge b m ω r*(Real.rpow (b.Delta r) ((3:ℝ)/4):ℂ)) •
        (A r *ᵥ ((Real.sqrt (b.Delta r):ℂ) • U r-Complex.I • V r) -
          B r *ᵥ ((Real.sqrt (b.Delta r):ℂ) • U r+Complex.I • V r))) := by
  have hEU := matrix_mulVec_smooth E U hE hU
  have hOV := matrix_mulVec_smooth O V hO hV
  have hOU := matrix_mulVec_smooth O U hO hU
  have hEV := matrix_mulVec_smooth E V hE hV
  have hDelta : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r => (b.Delta r:ℂ)) (Ici b.rPlus) := by
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    exact (((contDiffOn_id.pow 2).sub (contDiffOn_const.mul contDiffOn_id)).add contDiffOn_const).add contDiffOn_const
  constructor
  · refine ⟨fun r => (b.Delta r:ℂ) • (E r *ᵥ U r)-Complex.I • (O r *ᵥ V r),
      (hDelta.fun_smul hEU).sub ((contDiffOn_const (c := Complex.I)).fun_smul hOV), ?_⟩
    intro r hr
    dsimp only
    rw [negative_horizon_sum _ _ _ _ _ _ _ (hs r hr) (hd r hr)]
    have ht : (Real.sqrt (b.Delta r):ℂ)^2=(b.Delta r:ℂ) := by
      norm_cast; exact Real.sq_sqrt (le_of_lt (b.Delta_pos hr))
    rw [ht]
  · refine ⟨fun r => O r *ᵥ U r-Complex.I • (E r *ᵥ V r),
      hOU.sub ((contDiffOn_const (c := Complex.I)).fun_smul hEV), ?_⟩
    intro r hr
    dsimp only
    rw [negative_horizon_difference _ _ _ _ _ _ _ (hs r hr) (hd r hr),smul_smul]
    rw [mul_assoc, KN.Boundary.negative_horizon_shift b hr]

end KN.Physics
