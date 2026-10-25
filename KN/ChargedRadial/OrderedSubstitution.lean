import KN.ChargedRadial.TransformCoefficients
import KN.Background.Parameters
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

noncomputable section
namespace KN.ChargedRadial

/-- Direct ordered replacement in `D²(ΔD+L)-(R₁²+λ²)D-(3R₁-iσλ)R₁'`.
`f₀,f₁,f₂` are the Fourier-side jet, and derivatives of `iξF` are expanded
with the product rule. This definition preserves the multiplication order. -/
def orderedFourierJet (p : RadialPolynomialData) (xi f0 f1 f2 : ℂ) : ℂ :=
  -xi^2 * (-(Complex.I*(2*f1+xi*f2)) - 2*p.M*Complex.I*(Complex.I*(f0+xi*f1)) +
    (p.a^2+p.Q^2)*Complex.I*xi*f0 - p.L2*f2 + Complex.I*p.L1*f1+p.L0*f0) -
  (-p.u^2*(Complex.I*(2*f1+xi*f2)) + 2*p.u*p.b*Complex.I*(Complex.I*(f0+xi*f1)) +
    (p.b^2+p.lam^2)*Complex.I*xi*f0) -
  (3*Complex.I*p.u^2*f1+(3*p.b-Complex.I*p.sigma*p.lam)*p.u*f0)

theorem orderedFourierJet_coefficients (p : RadialPolynomialData) (xi f0 f1 f2 : ℂ) :
    orderedFourierJet p xi f0 f1 f2 =
      fourierSecond p xi*f2 + fourierFirst p xi*f1 + fourierZeroth p xi*f0 := by
  unfold orderedFourierJet fourierSecond fourierFirst fourierZeroth
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Product-rule terms used in the ordered Fourier substitution are actual derivatives. -/
theorem fourier_linear_factor_derivative (F : ℂ → ℂ) (hF : Differentiable ℂ F) (xi : ℂ) :
    deriv (fun t => Complex.I*t*F t) xi = Complex.I*(F xi+xi*deriv F xi) := by
  have hh := ((hasDerivAt_id xi).const_mul Complex.I).mul (hF xi).hasDerivAt
  change deriv ((fun y => Complex.I*id y)*F) xi = _
  rw [hh.deriv]
  dsimp
  ring

theorem fourier_linear_factor_second_derivative (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hF' : Differentiable ℂ (deriv F)) (xi : ℂ) :
    deriv (deriv (fun t => Complex.I*t*F t)) xi =
      Complex.I*(2*deriv F xi+xi*deriv (deriv F) xi) := by
  have he : deriv (fun t => Complex.I*t*F t) =
      fun t => Complex.I*(F t+t*deriv F t) := funext (fourier_linear_factor_derivative F hF)
  rw [he]
  have hh := ((hF xi).hasDerivAt.add
    ((hasDerivAt_id xi).mul (hF' xi).hasDerivAt)).const_mul Complex.I
  convert hh.deriv using 1
  · rfl
  · dsimp
    ring

def backgroundPolynomialData (b : KN.Background) (m : ℤ) (sigma omega lam : ℂ) :
    RadialPolynomialData where
  M := b.M
  a := b.a
  Q := b.Q
  m := m
  eta := b.eta
  c := b.c
  beta := b.beta
  sigma := sigma
  omega := omega
  lam := lam

lemma background_cQ (b : KN.Background) : b.c*b.Q = b.M*b.eta := by
  dsimp [KN.Background.c, KN.Background.eta]
  ring

lemma background_c_squared (b : KN.Background) : b.c^2 = b.eta*(b.eta+2) := by
  have h := b.kappa_sq_sub_c_sq
  dsimp [KN.Background.kappa] at h
  nlinarith

lemma background_betaQ (b : KN.Background) (hQ : b.Q ≠ 0) : b.Q*b.beta = 3/2*b.M := by
  dsimp [KN.Background.beta]
  field_simp

/-- All three coefficient identities at the physical background, without any
undischarged coefficient relations. -/
theorem physical_fourier_coefficients (b : KN.Background) (hQ : b.Q ≠ 0)
    (m : ℤ) (sigma omega lam x : ℂ) (hs : sigma = 1 ∨ sigma = -1) :
    let p := backgroundPolynomialData b m sigma omega lam
    fourierSecond p (omega*x) = Complex.I*omega^3*transformA p x ∧
    fourierFirst p (omega*x) = Complex.I*omega^2*(transformB p x+Complex.I*omega*transformC p x) ∧
    fourierZeroth p (omega*x) = Complex.I*omega*
      (transformD0 p x+omega*transformD1 p x+omega^2*transformD2 p x+Complex.I*omega*transformE p x) := by
  let p := backgroundPolynomialData b m sigma omega lam
  have hc : p.c^2 = p.eta*(p.eta+2) := by
    dsimp [p, backgroundPolynomialData]
    exact_mod_cast background_c_squared b
  have hcQ : p.c*p.Q = p.M*p.eta := by
    dsimp [p, backgroundPolynomialData]
    exact_mod_cast background_cQ b
  have hcb : p.c*p.beta = 3/2*(p.eta+2) := by
    dsimp [p, backgroundPolynomialData]
    have hr : b.c*b.beta = (3:ℝ)/2*(b.eta+2) := by
      have ht := b.beta_mul_c hQ
      dsimp [KN.Background.h] at ht
      nlinarith
    have hh := congrArg Complex.ofReal hr
    push_cast at hh
    exact hh
  have hQb : p.Q*p.beta = 3/2*p.M := by
    dsimp [p, backgroundPolynomialData]
    have hh := congrArg Complex.ofReal (background_betaQ b hQ)
    push_cast at hh
    exact hh
  exact ⟨fourier_second_coefficient p hs hc x,
    fourier_first_coefficient p hs hc hcQ hcb x,
    fourier_zeroth_coefficient p hs hcQ hcb hQb x⟩

end KN.ChargedRadial
