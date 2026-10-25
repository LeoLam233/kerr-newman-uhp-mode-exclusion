import KN.ChargedRadial.OriginalPair

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace KN.ChargedRadial

/-- An affine coupling with nonzero slope cannot conceal a differentiable
partner at its possible zero. Differentiating the zero product handles that
point without division by the coupling. -/
theorem partner_zero_of_affine_product (r0 : ℝ) (u a : ℂ) (hu : u ≠ 0)
    (z : ℝ → ℂ) (hz : DifferentiableOn ℝ z (Ioi r0))
    (hprod : ∀ r > r0, (u*(r:ℂ)+a)*z r=0) : EqOn z 0 (Ioi r0) := by
  intro r hr
  by_cases hA : u*(r:ℂ)+a=0
  · have hp := (radialAffine_hasDerivAt u a r).mul
      (hz.differentiableAt (Ioi_mem_nhds hr)).hasDerivAt
    have he : (fun t : ℝ => radialAffine u a t*z t) =ᶠ[𝓝 r] 0 := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      exact hprod t ht
    have hd : deriv (fun t : ℝ => radialAffine u a t*z t) r=0 := by
      rw [he.deriv_eq]
      exact deriv_const r (0:ℂ)
    have hh := hp.deriv
    change deriv (fun t : ℝ => radialAffine u a t*z t) r=_ at hh
    rw [hd] at hh
    dsimp [radialAffine] at hh
    rw [hA,zero_mul,add_zero] at hh
    exact (mul_eq_zero.mp hh.symm).resolve_left hu
  · exact (mul_eq_zero.mp (hprod r hr)).resolve_left hA

/-- Vanishing of the selected original component recovers its partner at every
exterior point, including any zero of R1+i sigma lambda. -/
theorem original_partner_zero (b : KN.Background) (hQ : b.Q ≠ 0) (m : ℤ)
    (sigma : ℝ) (hs : sigma=1 ∨ sigma= -1) (omega lam : ℂ) (hw : 0<omega.im)
    (y z : ℝ → ℂ) (hpair : OriginalSelectedPair b m sigma omega lam y z)
    (hy : EqOn y 0 (Ioi b.rPlus)) : EqOn z 0 (Ioi b.rPlus) := by
  have hc : (b.c:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by
    unfold KN.Background.c
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt b.mass_pos)) hQ) b.d_ne)
  have hs0 : (sigma:ℂ) ≠ 0 := by rcases hs with rfl|rfl <;> norm_num
  have hu : -(sigma:ℂ)*b.c*omega ≠ 0 :=
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hs0) hc) (KN.Background.uhpfrequency_ne_zero hw)
  apply partner_zero_of_affine_product b.rPlus (-(sigma:ℂ)*b.c*omega)
    ((sigma:ℂ)*b.Q*b.eta*omega+Complex.I*b.beta+Complex.I*sigma*lam) hu z
  · intro r hr
    exact (hpair r hr).2.differentiableAt.differentiableWithinAt
  · intro r hr
    have he : y =ᶠ[𝓝 r] 0 := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      exact hy ht
    have hd : deriv y r=0 := by rw [he.deriv_eq]; exact deriv_const r (0:ℂ)
    have hh := (hpair r hr).1.deriv
    rw [hd,hy hr] at hh
    simp only [Pi.zero_apply,mul_zero,zero_add] at hh
    have ht : (Real.sqrt (b.Delta r):ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
    have hh' := hh.symm
    field_simp [ht] at hh'
    dsimp [physicalR1] at hh'
    linear_combination hh'

end KN.ChargedRadial
