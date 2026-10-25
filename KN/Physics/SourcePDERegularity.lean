import KN.Physics.SourcePDE

namespace KN.Physics
noncomputable section
set_option backward.isDefEq.respectTransparency false

lemma transformScale_differentiable (positive : Bool) (b : Background)
    {r θ : ℝ} (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi) :
    SourceDifferentiableAt (transformScale positive b) r θ := by
  let q : ℝ := if positive then 5/4 else -3/4
  have hrad := (KN.Boundary.delta_rpow_hasDerivAt b q hr).ofReal_comp
  have hang := ((Real.hasDerivAt_sin θ).sqrt (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ hπ))).ofReal_comp
  constructor
  · convert hrad.differentiableAt.mul_const (Real.sqrt (Real.sin θ):ℂ) using 1
    ext x
    cases positive <;> simp [transformScale,q]
  · convert hang.differentiableAt.const_mul (Real.rpow (b.Delta r) q:ℂ) using 1
    ext y
    cases positive <;> simp [transformScale,q]

lemma transformMix_differentiable (positive : Bool) (b : Background)
    {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    SourceDifferentiableAt (fun x _ => transformMix positive b x) r θ := by
  have hs := (source_sqrt_deriv b hr).differentiableAt
  have ht : (Real.sqrt (b.Delta r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  constructor
  · cases positive
    · exact hs.neg
    · exact hs.inv ht
  · exact differentiableAt_const _

/-- Ordinary smoothness of original source components already supplies all
partial derivatives required by the chiral source entry. -/
theorem sourceY_differentiable (positive : Bool) (b : Background)
    (u : ℝ → ℝ → Fin 4 → ℂ) {r θ : ℝ}
    (hr : b.rPlus<r) (hθ : 0<θ) (hπ : θ<Real.pi)
    (hu : ∀ i, SourceDifferentiableAt (fun x y => u x y i) r θ)
    (sign : ℂ) (i : Fin 2) :
    SourceDifferentiableAt (fun x y => sourceY positive sign b u x y i) r θ := by
  have hF := transformScale_differentiable positive b hr hθ hπ
  have ht := transformMix_differentiable positive b hr θ
  have hc := SourceDifferentiableAt.const
  fin_cases i
  · exact hF.mul ((hu 0).add (((hc (sign*Complex.I) r θ).mul ht).mul (hu 1)))
  · exact hF.mul ((hc (-2*transformCharge positive b) r θ).mul
      ((hu 2).add (((hc (sign*Complex.I) r θ).mul ht).mul (hu 3))))

theorem sourceChiralDifferentiable_of_original (positive : Bool) (b : Background)
    (u : ℝ → ℝ → Fin 4 → ℂ)
    (hu : ∀ r θ, b.rPlus<r → 0<θ → θ<Real.pi →
      ∀ i, SourceDifferentiableAt (fun x y => u x y i) r θ) :
    SourceChiralDifferentiable positive b u := by
  intro r θ hr hθ hπ sign _ i
  exact sourceY_differentiable positive b u hr hθ hπ (hu r θ hr hθ hπ) sign i

end
end KN.Physics
