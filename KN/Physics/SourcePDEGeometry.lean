import KN.Physics.SourcePDECalculus

namespace KN.Physics
set_option backward.isDefEq.respectTransparency false
noncomputable section

def sourceF2 (b : Background) (r θ : ℝ) : ℂ :=
  (Real.sqrt (b.Delta r):ℂ)-(b.a:ℂ)*(Real.sin θ:ℂ)
def sourceF4 (b : Background) (r θ : ℝ) : ℂ :=
  (Real.sqrt (b.Delta r):ℂ)+(b.a:ℂ)*(Real.sin θ:ℂ)

lemma rho_radial_deriv (b : Background) (r θ : ℝ) :
    HasDerivAt (fun x => rho b x θ) 1 r := by
  simpa only [rho,Complex.ofReal_one,id_eq] using ((hasDerivAt_id r).ofReal_comp.add_const (Complex.I*b.a*Real.cos θ))
lemma rhoStar_radial_deriv (b : Background) (r θ : ℝ) :
    HasDerivAt (fun x => rhoStar b x θ) 1 r := by
  simpa only [rhoStar,Complex.ofReal_one,id_eq] using ((hasDerivAt_id r).ofReal_comp.sub_const (Complex.I*b.a*Real.cos θ))
lemma rho_angular_deriv (b : Background) (r θ : ℝ) :
    HasDerivAt (rho b r) (-Complex.I*b.a*Real.sin θ) θ := by
  convert ((Real.hasDerivAt_cos θ).ofReal_comp.const_mul (Complex.I*b.a)).const_add (r:ℂ) using 1
  · rfl
  · push_cast; ring
lemma rhoStar_angular_deriv (b : Background) (r θ : ℝ) :
    HasDerivAt (rhoStar b r) (Complex.I*b.a*Real.sin θ) θ := by
  convert ((Real.hasDerivAt_cos θ).ofReal_comp.const_mul (Complex.I*b.a)).const_sub (r:ℂ) using 1
  · rfl
  · push_cast; ring
lemma source_sqrt_deriv (b : Background) {r : ℝ} (hr : b.rPlus<r) :
    HasDerivAt (fun x => (Real.sqrt (b.Delta x):ℂ))
      (((r:ℂ)-b.M)/(Real.sqrt (b.Delta r):ℂ)) r := by
  convert ((KN.Boundary.delta_hasDerivAt b r).sqrt (ne_of_gt (b.Delta_pos hr))).ofReal_comp using 1
  push_cast
  ring

lemma sourceF2_radial_deriv (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    HasDerivAt (fun x => sourceF2 b x θ)
      (((r:ℂ)-b.M)/(Real.sqrt (b.Delta r):ℂ)) r :=
  (source_sqrt_deriv b hr).sub_const _
lemma sourceF4_radial_deriv (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    HasDerivAt (fun x => sourceF4 b x θ)
      (((r:ℂ)-b.M)/(Real.sqrt (b.Delta r):ℂ)) r :=
  (source_sqrt_deriv b hr).add_const _
lemma sourceF2_angular_deriv (b : Background) (r θ : ℝ) :
    HasDerivAt (sourceF2 b r) (-(b.a:ℂ)*(Real.cos θ:ℂ)) θ := by
  convert ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul (b.a:ℂ)).const_sub (Real.sqrt (b.Delta r):ℂ) using 1
  · rfl
  · ring
lemma sourceF4_angular_deriv (b : Background) (r θ : ℝ) :
    HasDerivAt (sourceF4 b r) ((b.a:ℂ)*(Real.cos θ:ℂ)) θ :=
  ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul (b.a:ℂ)).const_add _

lemma source_geometry_jets (b : Background) {r : ℝ} (hr : b.rPlus<r) (θ : ℝ) :
    sourceD (Real.sqrt (b.Delta r)) (-1) (rho b) r θ=sourceF2 b r θ ∧
    sourceD (Real.sqrt (b.Delta r)) (-1) (sourceF2 b) r θ=rho b r θ-b.M ∧
    sourceD (Real.sqrt (b.Delta r)) (-1) (rhoStar b) r θ=sourceF4 b r θ ∧
    sourceD (Real.sqrt (b.Delta r)) (-1) (sourceF4 b) r θ=rhoStar b r θ-b.M := by
  have ht : (Real.sqrt (b.Delta r):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (b.Delta_pos hr)))
  unfold sourceD
  rw [(rho_radial_deriv b r θ).deriv,(rho_angular_deriv b r θ).deriv,
    (rhoStar_radial_deriv b r θ).deriv,(rhoStar_angular_deriv b r θ).deriv,
    (sourceF2_radial_deriv b hr θ).deriv,(sourceF2_angular_deriv b r θ).deriv,
    (sourceF4_radial_deriv b hr θ).deriv,(sourceF4_angular_deriv b r θ).deriv]
  simp only [rho,rhoStar,sourceF2,sourceF4]
  constructor
  · ring_nf; simp only [Complex.I_sq]; ring
  constructor
  · field_simp; ring
  constructor
  · ring_nf; simp only [Complex.I_sq]; ring
  · field_simp; ring

end
end KN.Physics
