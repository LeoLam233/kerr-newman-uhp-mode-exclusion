import KN.Energy.ConormalCalculus

open Set Polynomial
namespace KN.Energy
open KN.Boundary

theorem polynomialConormal_neg (rp : ℝ) (f : ℝ → ℂ) (hs : ExteriorSmooth rp f)
    (hf : PolynomialConormal f) : PolynomialConormal (fun r => -f r) := by
  simpa only [neg_one_mul] using (polynomialConormal_add_mul rp (fun _ : ℝ => (-1:ℂ)) f
    contDiffOn_const hs (polynomialConormal_const (-1)) hf).2

theorem polynomialConormal_sub (rp : ℝ) (f g : ℝ → ℂ)
    (hfs : ExteriorSmooth rp f) (hgs : ExteriorSmooth rp g)
    (hf : PolynomialConormal f) (hg : PolynomialConormal g) :
    PolynomialConormal (fun r => f r-g r) := by
  simpa only [sub_eq_add_neg] using (polynomialConormal_add_mul rp f (fun r => -g r)
    hfs hgs.neg hf (polynomialConormal_neg rp g hgs hg)).1

noncomputable def covariantDerivative (p f : ℝ → ℂ) (r : ℝ) := deriv f r-p r*f r

theorem covariantDerivative_preserves (rp : ℝ) (p f : ℝ → ℂ)
    (hps : ExteriorSmooth rp p) (hfs : ExteriorSmooth rp f)
    (hp : PolynomialConormal p) (hf : PolynomialConormal f) :
    ExteriorSmooth rp (covariantDerivative p f) ∧ PolynomialConormal (covariantDerivative p f) := by
  have hd : ExteriorSmooth rp (deriv f) := hfs.deriv_of_isOpen isOpen_Ioi (by simp)
  exact ⟨hd.sub (hps.mul hfs), polynomialConormal_sub rp (deriv f) (fun r => p r*f r)
    hd (hps.mul hfs) (polynomialConormal_deriv rp f hfs hf)
    (polynomialConormal_add_mul rp p f hps hfs hp hf).2⟩

theorem covariantDerivative_iterate_preserves (rp : ℝ) (p f : ℝ → ℂ)
    (hps : ExteriorSmooth rp p) (hfs : ExteriorSmooth rp f)
    (hp : PolynomialConormal p) (hf : PolynomialConormal f) (n : ℕ) :
    ExteriorSmooth rp ((covariantDerivative p)^[n] f) ∧
      PolynomialConormal ((covariantDerivative p)^[n] f) := by
  induction n with
  | zero => exact ⟨hfs,hf⟩
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using
      covariantDerivative_preserves rp p ((covariantDerivative p)^[n] f) hps ih.1 hp ih.2

noncomputable def deltaPolynomial (b : KN.Background) : Polynomial ℂ :=
  X^2-C (2*(b.M:ℂ))*X+C ((b.a:ℂ)^2+(b.Q:ℂ)^2)

theorem deltaPolynomial_eval (b : KN.Background) (r : ℝ) :
    (deltaPolynomial b).eval (r:ℂ) = (b.Delta r:ℂ) := by
  simp [deltaPolynomial, KN.Background.Delta]
  ring

theorem delta_conormal (b : KN.Background) : PolynomialConormal (fun r : ℝ => (b.Delta r:ℂ)) := by
  simpa only [deltaPolynomial_eval] using polynomialConormal_polynomial (deltaPolynomial b)

theorem delta_smooth (b : KN.Background) : ExteriorSmooth b.rPlus (fun r : ℝ => (b.Delta r:ℂ)) := by
  have hd : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (fun r : ℝ => b.Delta r) := by
    unfold KN.Background.Delta
    fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hd).contDiffOn

noncomputable def frequencyPolynomial (b : KN.Background) (m : ℤ) (ω : ℂ) : Polynomial ℂ :=
  C (-ω)*X^2+C (-(b.a:ℂ)^2*ω+(b.a:ℂ)*m)

theorem frequencyPolynomial_eval (b : KN.Background) (m : ℤ) (ω : ℂ) (r : ℝ) :
    (frequencyPolynomial b m ω).eval (r:ℂ) = b.frequencyK m ω r := by
  simp [frequencyPolynomial, KN.Background.frequencyK]
  ring

theorem frequencyK_conormal (b : KN.Background) (m : ℤ) (ω : ℂ) :
    PolynomialConormal (b.frequencyK m ω) := by
  simpa only [frequencyPolynomial_eval] using polynomialConormal_polynomial (frequencyPolynomial b m ω)

theorem frequencyK_smooth (b : KN.Background) (m : ℤ) (ω : ℂ) :
    ExteriorSmooth b.rPlus (b.frequencyK m ω) := by
  have hh : ExteriorSmooth b.rPlus (fun r : ℝ => (frequencyPolynomial b m ω).eval (r:ℂ)) :=
    (((frequencyPolynomial b m ω).contDiff_aeval _).restrict_scalars ℝ |>.comp
      Complex.ofRealCLM.contDiff).contDiffOn
  simpa only [frequencyPolynomial_eval] using hh

noncomputable def logarithmicCoefficient (b : KN.Background) (m : ℤ) (ω : ℂ) (r : ℝ) : ℂ :=
  2*Complex.I*b.frequencyK m ω r/(b.Delta r:ℂ)

theorem logarithmicCoefficient_smooth_conormal (b : KN.Background) (m : ℤ) (ω : ℂ) :
    ExteriorSmooth b.rPlus (logarithmicCoefficient b m ω) ∧
      PolynomialConormal (logarithmicCoefficient b m ω) := by
  have hdn : ∀ r ∈ Ioi b.rPlus, (b.Delta r:ℂ) ≠ 0 := by
    intro r hr
    exact_mod_cast ne_of_gt (b.Delta_pos hr)
  have hsm : ExteriorSmooth b.rPlus (logarithmicCoefficient b m ω) := by
    unfold logarithmicCoefficient
    simp only [div_eq_mul_inv]
    change ExteriorSmooth b.rPlus (fun r => (2*Complex.I*b.frequencyK m ω r)*(b.Delta r:ℂ)⁻¹)
    exact (contDiffOn_const.mul (frequencyK_smooth b m ω)).mul ((delta_smooth b).inv hdn)
  have hgap : b.rMinus < b.rPlus := by have := b.horizon_gap; linarith [b.delta_pos]
  have hrms : ExteriorSmooth b.rPlus (reciprocal b.rMinus) :=
    (reciprocal_smooth b.rMinus).mono (Ioi_subset_Ioi hgap.le)
  have hn := (polynomialConormal_add_mul b.rPlus (fun _ : ℝ => 2*Complex.I) (b.frequencyK m ω)
    contDiffOn_const (frequencyK_smooth b m ω) (polynomialConormal_const _) (frequencyK_conormal b m ω)).2
  have hprod := (polynomialConormal_add_mul b.rPlus (reciprocal b.rPlus) (reciprocal b.rMinus)
    (reciprocal_smooth b.rPlus) hrms (polynomialConormal_reciprocal _) (polynomialConormal_reciprocal _)).2
  have hmul := (polynomialConormal_add_mul b.rPlus (fun r => (2*Complex.I)*b.frequencyK m ω r)
    (fun r => reciprocal b.rPlus r*reciprocal b.rMinus r)
    (contDiffOn_const.mul (frequencyK_smooth b m ω)) ((reciprocal_smooth _).mul hrms) hn hprod).2
  refine ⟨hsm, polynomialConormal_congr_exterior b.rPlus hmul ?_⟩
  intro r _
  dsimp [logarithmicCoefficient,reciprocal]
  rw [b.delta_factor]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring
end KN.Energy
