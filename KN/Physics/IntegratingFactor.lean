import KN.Physics.HorizonAlgebra

noncomputable section
namespace KN.Physics
open Matrix

/-- Geometric numerator identity behind the matrix integrating factor. -/
theorem integrating_geometry (M Q a r t sn cs : ℂ)
    (ht : t^2=r^2-2*M*r+a^2+Q^2) (hs : sn^2+cs^2=1) :
    (r+Complex.I*a*cs)*(r-Complex.I*a*cs) - (t-a*sn)*(t+a*sn) =
      M*((r+Complex.I*a*cs)+(r-Complex.I*a*cs))-Q^2 := by
  linear_combination (norm := ring_nf) -ht + a^2*hs
  simp [Complex.I_sq]

def factorX (M Q f1 f2 f3 f4 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Q*f4/f1,-Complex.I*(M-Q^2/f1); Complex.I*(M-Q^2/f3),Q*f2/f3]
def factorDX (M Q f1 f2 f3 f4 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Q*((f3-M)*f1-f4*f2)/f1^2,-Complex.I*Q^2*f2/f1^2;
    Complex.I*Q^2*f4/f3^2,Q*((f1-M)*f3-f2*f4)/f3^2]
def factorConnection (Q f1 f3 : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,-Complex.I*Q*f3/f1^2; Complex.I*Q*f1/f3^2,0]

/-- The explicit differentiated source satisfies the actual matrix connection equation.
The derivatives used here are Df1=f2, Df2=f1-M, Df3=f4, Df4=f3-M. -/
theorem factor_connection_identity (M Q f1 f2 f3 f4 : ℂ)
    (h1 : f1 ≠ 0) (h3 : f3 ≠ 0)
    (hg : f1*f3-f2*f4=M*(f1+f3)-Q^2) :
    factorDX M Q f1 f2 f3 f4 = factorConnection Q f1 f3 * factorX M Q f1 f2 f3 f4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [factorDX, factorConnection, factorX, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;>
    simp only [Complex.I_sq] <;>
    linear_combination (norm := ring_nf) Q * hg

end KN.Physics
