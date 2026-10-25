import KN.Physics.SourceHilbertBoundaryHorizon

noncomputable section
set_option linter.unnecessarySeqFocus false
set_option backward.isDefEq.respectTransparency false
namespace KN.Physics
open KN.Angular KN.Boundary

lemma horizon_power_products (d : ℝ) (hd : 0<d) :
    (Real.rpow d ((5:ℝ)/4):ℂ)*(Real.rpow d (-2):ℂ)=(Real.rpow d ((-3:ℝ)/4):ℂ) ∧
    (Real.rpow d ((5:ℝ)/4):ℂ)*(Real.sqrt d:ℂ)⁻¹*(Real.rpow d (-1):ℂ)=
      (Real.rpow d ((-3:ℝ)/4):ℂ)*(Real.sqrt d:ℂ) ∧
    (Real.rpow d ((-3:ℝ)/4):ℂ)*(Real.rpow d 2:ℂ)=
      (Real.rpow d ((3:ℝ)/4):ℂ)*(Real.sqrt d:ℂ) ∧
    (Real.rpow d ((-3:ℝ)/4):ℂ)*(Real.sqrt d:ℂ)*(Real.rpow d 1:ℂ)=
      (Real.rpow d ((3:ℝ)/4):ℂ) := by
  have hm (p q : ℝ) : Real.rpow d p*Real.rpow d q=Real.rpow d (p+q) := (Real.rpow_add hd p q).symm
  have hs : Real.sqrt d=Real.rpow d ((1:ℝ)/2) := Real.sqrt_eq_rpow _
  have hi : (Real.sqrt d)⁻¹=Real.rpow d ((-1:ℝ)/2) := by
    rw [hs]
    have hh := Real.rpow_neg (le_of_lt hd) ((1:ℝ)/2)
    convert hh.symm using 1 <;> norm_num
  have h0 : Real.rpow d ((5:ℝ)/4)*Real.rpow d (-2)=Real.rpow d ((-3:ℝ)/4) := by
    rw [hm]
    congr 1
    norm_num
  have h1 : Real.rpow d ((5:ℝ)/4)*(Real.sqrt d)⁻¹*Real.rpow d (-1)=
      Real.rpow d ((-3:ℝ)/4)*Real.sqrt d := by
    rw [hi,hs,hm,hm,hm]
    congr 1
    norm_num
  have h2 : Real.rpow d ((-3:ℝ)/4)*Real.rpow d 2=Real.rpow d ((3:ℝ)/4)*Real.sqrt d := by
    rw [hs,hm,hm]
    congr 1
    norm_num
  have h3 : Real.rpow d ((-3:ℝ)/4)*Real.sqrt d*Real.rpow d 1=Real.rpow d ((3:ℝ)/4) := by
    rw [hs,hm,hm]
    congr 1
    norm_num
  exact ⟨by exact_mod_cast h0,by exact_mod_cast h1,by exact_mod_cast h2,by exact_mod_cast h3⟩

lemma source_normalization_positive (b : KN.Background) (m : ℤ) (omega : ℂ)
    (r : ℝ) (hr : b.rPlus<r) (U V : AngularHilbert)
    (L : AngularHilbert →L[ℂ] AngularHilbert) (s : ℂ) :
    (Real.rpow (b.Delta r) ((5:ℝ)/4):ℂ) • L
      ((gauge b m omega r*(Real.rpow (b.Delta r) (-2):ℂ)) • U+
        (s*Complex.I*(Real.sqrt (b.Delta r):ℂ)⁻¹) •
          ((gauge b m omega r*(Real.rpow (b.Delta r) (-1):ℂ)) • V))=
    (gauge b m omega r*(Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ)) •
      L (U+(s*Complex.I*(Real.sqrt (b.Delta r):ℂ)) • V) := by
  obtain ⟨h0,h1,_,_⟩ := horizon_power_products (b.Delta r) (b.Delta_pos hr)
  simp only [map_add,map_smul,smul_add,smul_smul]
  congr 1
  · congr 1
    linear_combination gauge b m omega r*h0
  · congr 1
    linear_combination s*Complex.I*gauge b m omega r*h1

lemma source_normalization_negative (b : KN.Background) (m : ℤ) (omega : ℂ)
    (r : ℝ) (hr : b.rPlus<r) (U V : AngularHilbert)
    (L : AngularHilbert →L[ℂ] AngularHilbert) (s : ℂ) :
    (Real.rpow (b.Delta r) ((-3:ℝ)/4):ℂ) • L
      ((gauge b m omega r*(Real.rpow (b.Delta r) 2:ℂ)) • U+
        (-s*Complex.I*(Real.sqrt (b.Delta r):ℂ)) •
          ((gauge b m omega r*(Real.rpow (b.Delta r) 1:ℂ)) • V))=
    (gauge b m omega r*(Real.rpow (b.Delta r) ((3:ℝ)/4):ℂ)) •
      L ((Real.sqrt (b.Delta r):ℂ) • U+(-s*Complex.I) • V) := by
  obtain ⟨_,_,h0,h1⟩ := horizon_power_products (b.Delta r) (b.Delta_pos hr)
  simp only [map_add,map_smul,smul_add,smul_smul]
  congr 1
  · congr 1
    linear_combination gauge b m omega r*h0
  · congr 1
    linear_combination (-s*Complex.I*gauge b m omega r)*h1

end KN.Physics
