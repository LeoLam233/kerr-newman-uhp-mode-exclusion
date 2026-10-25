import KN.Energy.TailGrowth
import KN.Boundary.GaugeDerivative

noncomputable section
open Set Filter
namespace KN.Boundary
open KN.Energy KN.Energy.ConormalExpr

/-- A polynomially bounded smooth function with conormal logarithmic Euler
coefficient has conormal bounds at every order. -/
theorem polynomialConormal_of_euler_product (rp : ℝ) (f L : ℝ → ℂ)
    (hfs : ExteriorSmooth rp f) (hLs : ExteriorSmooth rp L)
    (hf : PolyBound f) (hL : PolynomialConormal L)
    (he : ∀ r>rp, eulerDeriv f r=L r*f r) : PolynomialConormal f := by
  let F : Fin 2 → ℕ → ℝ → ℂ := fun i n => if i=0 then f else (eulerDeriv^[n]) L
  let δ : Fin 2 → ℕ → ConormalExpr := fun i n =>
    if i=0 then .mul (.var 1 0) (.var 0 0) else .var 1 (n+1)
  have hF : ∀ i n, ExteriorSmooth rp (F i n) := by
    intro i n
    dsimp [F]
    split
    · exact hfs
    · exact euler_iterate_smooth hLs n
  have hD : ∀ i n r, rp<r → eulerDeriv (F i n) r=eval F (δ i n) r := by
    intro i n r hr
    fin_cases i
    · simpa [F,δ,eval] using he r hr
    · simp [F,δ,eval,Function.iterate_succ_apply']
  have hB : ∀ i n, PolyBound (F i n) := by
    intro i n
    dsimp [F]
    split
    · exact hf
    · exact hL n
  exact conormal_of_euler_family (eval F) (diffUsing δ) rp
    (fun p => eval_diffUsing F rp hF δ hD p) (eval_polyBound F hB) (.var 0 0)

theorem delta_rpow_polyBound_all (b : KN.Background) (q : ℝ) :
    PolyBound (fun r : ℝ => (Real.rpow (b.Delta r) q:ℂ)) := by
  obtain ⟨N,hN⟩ := exists_nat_ge q
  have hp := polynomialConormal_pow b.rPlus (fun r : ℝ => (b.Delta r:ℂ))
    (delta_smooth b) (delta_conormal b) N
  apply polyBound_of_norm_le (hp 0)
  filter_upwards [delta_eventually_one_le b] with r hr
  change ‖(Real.rpow (b.Delta r) q:ℂ)‖ ≤ ‖(b.Delta r:ℂ)^N‖
  simp only [norm_pow,Complex.norm_real,Real.norm_eq_abs]
  change |(b.Delta r)^q| ≤ |b.Delta r|^N
  rw [abs_of_nonneg (Real.rpow_nonneg (le_trans zero_le_one hr) q),
    abs_of_nonneg (le_trans zero_le_one hr)]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hr hN

def deltaPowerEulerCoefficient (b : KN.Background) (q : ℝ) (r : ℝ) : ℂ :=
  (q:ℂ)*(r:ℂ)*(reciprocal b.rPlus r+reciprocal b.rMinus r)

theorem deltaPowerEulerCoefficient_smooth_conormal (b : KN.Background) (q : ℝ) :
    ExteriorSmooth b.rPlus (deltaPowerEulerCoefficient b q) ∧
      PolynomialConormal (deltaPowerEulerCoefficient b q) := by
  have hgap : b.rMinus < b.rPlus := by have := b.horizon_gap; linarith [b.delta_pos]
  have hm := (reciprocal_smooth b.rMinus).mono (Ioi_subset_Ioi hgap.le)
  have hp := reciprocal_smooth b.rPlus
  have hc : ExteriorSmooth b.rPlus (fun r : ℝ => (r:ℂ)) := Complex.ofRealCLM.contDiff.contDiffOn
  have hsum := (polynomialConormal_add_mul b.rPlus _ _ hp hm
    (polynomialConormal_reciprocal _) (polynomialConormal_reciprocal _)).1
  have hfirst := (polynomialConormal_add_mul b.rPlus (fun _ : ℝ => (q:ℂ)) _
    contDiffOn_const hc (polynomialConormal_const _) polynomialConormal_coordinate).2
  exact ⟨(contDiffOn_const.mul hc).mul (hp.add hm),
    (polynomialConormal_add_mul b.rPlus _ _ (contDiffOn_const.mul hc) (hp.add hm) hfirst hsum).2⟩

theorem delta_rpow_smooth (b : KN.Background) (q : ℝ) :
    ExteriorSmooth b.rPlus (fun r : ℝ => (Real.rpow (b.Delta r) q:ℂ)) := by
  apply Complex.ofRealCLM.contDiff.comp_contDiffOn
  apply ContDiffOn.rpow_const_of_ne
  · exact (((contDiffOn_id.pow 2).sub (contDiffOn_const.mul contDiffOn_id)).add contDiffOn_const).add contDiffOn_const
  · intro r hr
    exact ne_of_gt (b.Delta_pos hr)

theorem delta_rpow_euler (b : KN.Background) (q : ℝ) {r : ℝ} (hr : b.rPlus<r) :
    eulerDeriv (fun r : ℝ => (Real.rpow (b.Delta r) q:ℂ)) r=
      deltaPowerEulerCoefficient b q r*(Real.rpow (b.Delta r) q:ℂ) := by
  have hd := (delta_rpow_hasDerivAt b q hr).ofReal_comp
  have hdp := ne_of_gt (b.Delta_pos hr)
  have hp : r-b.rPlus ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  have hm : r-b.rMinus ≠ 0 := by
    have := b.horizon_gap
    have := b.delta_pos
    have : b.rMinus<r := by linarith
    exact ne_of_gt (sub_pos.mpr this)
  change (r:ℂ)*deriv (fun r : ℝ => (Real.rpow (b.Delta r) q:ℂ)) r=_
  rw [hd.deriv]
  have hpow : Real.rpow (b.Delta r) (q-1)=Real.rpow (b.Delta r) q / b.Delta r := Real.rpow_sub_one hdp q
  rw [hpow]
  dsimp [deltaPowerEulerCoefficient,reciprocal]
  rw [b.delta_factor]
  push_cast
  have hp' : (r:ℂ)-(b.rPlus:ℂ) ≠ 0 := by exact_mod_cast hp
  have hm' : (r:ℂ)-(b.rMinus:ℂ) ≠ 0 := by exact_mod_cast hm
  field_simp
  simp only [KN.Background.rPlus,KN.Background.rMinus]
  push_cast
  ring

theorem delta_rpow_conormal (b : KN.Background) (q : ℝ) :
    PolynomialConormal (fun r : ℝ => (Real.rpow (b.Delta r) q:ℂ)) :=
  polynomialConormal_of_euler_product b.rPlus _ _ (delta_rpow_smooth b q)
    (deltaPowerEulerCoefficient_smooth_conormal b q).1 (delta_rpow_polyBound_all b q)
    (deltaPowerEulerCoefficient_smooth_conormal b q).2 (fun _ hr => delta_rpow_euler b q hr)

end KN.Boundary
