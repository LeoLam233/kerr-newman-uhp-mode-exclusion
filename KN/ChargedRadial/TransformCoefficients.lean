import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Ordered Fourier substitution for the polynomial third-order radial operator.
This verifies coefficients only. Analytic transform existence and substitution for the
supported extension are NOT hypotheses hidden in this file and remain separate obligations. -/
noncomputable section
namespace KN.ChargedRadial

structure RadialPolynomialData where
  M : ℂ
  a : ℂ
  Q : ℂ
  m : ℂ
  eta : ℂ
  c : ℂ
  beta : ℂ
  sigma : ℂ
  omega : ℂ
  lam : ℂ

def RadialPolynomialData.u (p : RadialPolynomialData) : ℂ := -p.sigma * p.c * p.omega
def RadialPolynomialData.b (p : RadialPolynomialData) : ℂ :=
  p.sigma * p.Q * p.eta * p.omega + Complex.I * p.beta

def RadialPolynomialData.L2 (p : RadialPolynomialData) : ℂ :=
  2 * Complex.I * (1 + p.eta) * p.omega

def RadialPolynomialData.L1 (p : RadialPolynomialData) : ℂ :=
  1 + 3 * p.sigma - 4 * Complex.I * p.eta * p.M * p.omega

def RadialPolynomialData.L0 (p : RadialPolynomialData) : ℂ :=
  -(1 + 3 * p.sigma) * p.M +
    2 * Complex.I * (p.a^2 + p.eta * (p.a^2 + p.Q^2)) * p.omega -
    2 * Complex.I * p.a * p.m

/-- Coefficients after substitution `D_r ↦ iξ`, `r ↦ i D_ξ`, respecting order. -/
def fourierSecond (p : RadialPolynomialData) (xi : ℂ) : ℂ :=
  Complex.I * xi^3 + p.L2 * xi^2 + Complex.I * p.u^2 * xi

def fourierFirst (p : RadialPolynomialData) (xi : ℂ) : ℂ :=
  xi^2 * (2 * Complex.I - 2 * p.M * xi - Complex.I * p.L1) +
    2 * p.u * p.b * xi - Complex.I * p.u^2

def fourierZeroth (p : RadialPolynomialData) (xi : ℂ) : ℂ :=
  -xi^2 * (2*p.M + Complex.I * (p.a^2+p.Q^2) * xi + p.L0) -
    p.u*p.b + Complex.I*p.sigma*p.lam*p.u - Complex.I*(p.b^2+p.lam^2)*xi

def transformA (p : RadialPolynomialData) (x : ℂ) : ℂ := x*(x+p.eta)*(x+p.eta+2)
def transformB (p : RadialPolynomialData) (x : ℂ) : ℂ :=
  x^2-p.eta*(p.eta+2)-3*p.sigma*x*(x+p.eta+2)
def transformC (p : RadialPolynomialData) (x : ℂ) : ℂ := 2*p.M*x*(x+p.eta)^2

def transformE (p : RadialPolynomialData) (x : ℂ) : ℂ :=
  p.M*(x+p.eta)*(x-p.eta-3*p.sigma*x)
def transformD0 (p : RadialPolynomialData) (x : ℂ) : ℂ :=
  (p.beta^2-p.lam^2)*x+3/2*p.sigma*(p.eta+2)-p.c*p.lam
def transformD1 (p : RadialPolynomialData) (x : ℂ) : ℂ := 2*p.a*p.m*x^2
def transformD2 (p : RadialPolynomialData) (x : ℂ) : ℂ :=
  -(2*p.a^2+(p.a^2+p.Q^2)*(x+2*p.eta))*x^2-p.Q^2*p.eta^2*x

/-- Leading Fourier coefficient, including both spin signs, without division by ω. -/
theorem fourier_second_coefficient (p : RadialPolynomialData)
    (hs : p.sigma = 1 ∨ p.sigma = -1)
    (hc : p.c^2 = p.eta*(p.eta+2)) (x : ℂ) :
    fourierSecond p (p.omega*x) = Complex.I*p.omega^3*transformA p x := by
  unfold fourierSecond RadialPolynomialData.L2 RadialPolynomialData.u transformA
  rcases hs with hs | hs <;> rw [hs] <;>
    linear_combination (norm := ring_nf) Complex.I * p.omega^3 * x * hc

/-- First Fourier coefficient. `cQ=Mη` and `cβ=3h/2` are the actual
background identities; neither is an angular or transformed positivity assumption. -/
theorem fourier_first_coefficient (p : RadialPolynomialData)
    (hs : p.sigma = 1 ∨ p.sigma = -1)
    (hc : p.c^2 = p.eta*(p.eta+2))
    (hcQ : p.c*p.Q = p.M*p.eta)
    (hcb : p.c*p.beta = 3/2*(p.eta+2)) (x : ℂ) :
    fourierFirst p (p.omega*x) =
      Complex.I*p.omega^2*(transformB p x+Complex.I*p.omega*transformC p x) := by
  unfold fourierFirst RadialPolynomialData.L1 RadialPolynomialData.u
    RadialPolynomialData.b transformB transformC
  rcases hs with hs | hs <;> rw [hs]
  · linear_combination (norm := ring_nf) -Complex.I*p.omega^2*hc -
      2*p.eta*p.omega^3*x*hcQ - 2*Complex.I*p.omega^2*x*hcb
    simp [Complex.I_sq]
  · linear_combination (norm := ring_nf) -Complex.I*p.omega^2*hc -
      2*p.eta*p.omega^3*x*hcQ + 2*Complex.I*p.omega^2*x*hcb
    simp [Complex.I_sq]

/-- Zeroth Fourier coefficient, with the complex-frequency terms kept intact. -/
theorem fourier_zeroth_coefficient (p : RadialPolynomialData)
    (hs : p.sigma = 1 ∨ p.sigma = -1)
    (hcQ : p.c*p.Q = p.M*p.eta)
    (hcb : p.c*p.beta = 3/2*(p.eta+2))
    (hQb : p.Q*p.beta = 3/2*p.M) (x : ℂ) :
    fourierZeroth p (p.omega*x) = Complex.I*p.omega*
      (transformD0 p x+p.omega*transformD1 p x+p.omega^2*transformD2 p x+
        Complex.I*p.omega*transformE p x) := by
  unfold fourierZeroth RadialPolynomialData.L0 RadialPolynomialData.u
    RadialPolynomialData.b transformD0 transformD1 transformD2 transformE
  rcases hs with hs | hs <;> rw [hs]
  · linear_combination (norm := ring_nf) Complex.I*p.omega*hcb +
      p.eta*p.omega^2*hcQ + 2*p.eta*p.omega^2*x*hQb
    simp [Complex.I_sq]
  · linear_combination (norm := ring_nf) -Complex.I*p.omega*hcb +
      p.eta*p.omega^2*hcQ - 2*p.eta*p.omega^2*x*hQb
    simp [Complex.I_sq]

end KN.ChargedRadial
