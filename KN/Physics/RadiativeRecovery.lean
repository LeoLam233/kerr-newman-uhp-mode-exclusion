import KN.Physics.PhysicalTransform

noncomputable section
namespace KN.Physics

/-- The negative-spin phantom normalization in manuscript (8b). -/
theorem electromagneticMinus_phantom (M Q ρ Ψ Ψ₂ : ℂ) (hM : M ≠ 0) :
    ρ^3/(3*M)*(Q*Ψ-3*ρ^2*Ψ₂*0) =
      ((Real.sqrt 2 : ℂ)*Q)/(3*M) * (ρ^3*Ψ/(Real.sqrt 2 : ℂ)) := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
  field_simp
  ring

/-- Zero-charge identification is algebraic in a nonsingular tetrad, not a
limit of the singular charged phantom frame. -/
theorem electromagneticPlus_zero_charge (M ρ : ℂ) (v : RadiativeCurvatureMaxwell)
    (hM : M ≠ 0) (hρ : ρ ≠ 0) :
    electromagneticPlus M 0 ρ (-M/ρ^3) v = v.dPhi0 := by
  unfold electromagneticPlus
  field_simp
  ring

theorem electromagneticMinus_zero_charge (M ρ : ℂ) (v : RadiativeCurvatureMaxwell)
    (hM : M ≠ 0) (hρ : ρ ≠ 0) :
    electromagneticMinus M 0 ρ (-M/ρ^3) v = ρ^2*v.dPhi2 := by
  unfold electromagneticMinus
  field_simp
  ring

/-- Recover all physical radiative quantities from the original phantom
components; this statement does not assert any field equation or exclusion. -/
theorem phantom_radiative_zero (M Q ρ Ψ₂ : ℂ) (v : RadiativeCurvatureMaxwell)
    (_hM : M ≠ 0) (hρ : ρ ≠ 0)
    (hgauge0 : v.dPhi0=0) (hgauge2 : v.dPhi2=0)
    (hp2 : v.dPsi0=0) (hm2 : ρ^4*v.dPsi4=0)
    (hp1 : (Real.sqrt 2 : ℂ)*ρ*v.dPsi1=0)
    (hm1 : ρ^3*v.dPsi3/(Real.sqrt 2 : ℂ)=0) :
    gravitationalPlus v=0 ∧ gravitationalMinus ρ v=0 ∧
      electromagneticPlus M Q ρ Ψ₂ v=0 ∧ electromagneticMinus M Q ρ Ψ₂ v=0 := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
  have h1 : v.dPsi1=0 := (mul_eq_zero.mp hp1).resolve_left (mul_ne_zero hs hρ)
  have h3 : v.dPsi3=0 := by
    have h := (div_eq_zero_iff.mp hm1).resolve_right hs
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hρ)
  exact ⟨hp2,hm2,by simp [electromagneticPlus,hgauge0,h1],
    by simp [electromagneticMinus,hgauge2,h3]⟩

end KN.Physics
