import KN.Physics.HorizonAlgebra

noncomputable section
namespace KN.Physics
open Matrix

def chiralCoupling (M Q a r t sn cs m ω σ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let d := M^2-Q^2
  let eta := 2*Q^2/d
  let kappa := eta+1
  let c := 2*M*Q/d
  let beta := 3*M/(2*Q)
  let K := -(r^2+a^2)*ω+a*m
  let R0 := 3*(2*(r-M))/(4*t)-Complex.I*σ*(K/t-eta*ω*t)
  let R1 := -σ*2*ω*Q*(M*r-Q^2)/d+Complex.I*beta
  let W := (3:ℂ)/2*cs/sn+σ*m/sn-σ*a*kappa*ω*sn
  let T := -beta-σ*a*c*ω*cs
  !![R0+Complex.I*W,R1+Complex.I*T;-R1+Complex.I*T,R0-Complex.I*W]

def originalChiralCoupling (M Q a r t sn cs m ω σ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  let rp := r+Complex.I*a*cs
  let rm := r-Complex.I*a*cs
  let K := -(r^2+a^2)*ω+a*m
  let cc := σ*Complex.I*K/t+3*t/rm-3*(2*(r-M))/(4*t)
  let bb := -σ*(-a*ω*sn+m/sn)-(3:ℂ)/2*cs/sn+3*Complex.I*a*sn/rm
  !![cc-Complex.I*bb,-Complex.I*(3*(M*rp-Q^2)/(Q*rp));
    -Complex.I*(3*Q*rp/rm^2),cc+Complex.I*bb]

theorem source_coupling_identity (M Q a r t sn cs m ω σ : ℂ)
    (hQ : Q ≠ 0) (hd : M^2-Q^2 ≠ 0) (hsn : sn ≠ 0) (ht0 : t ≠ 0)
    (hp : r+Complex.I*a*cs ≠ 0) (hm : r-Complex.I*a*cs ≠ 0)
    (ht : t^2=r^2-2*M*r+a^2+Q^2) (htrig : sn^2+cs^2=1) :
    chiralCoupling M Q a r t sn cs m ω σ * sourceStar M Q a r t sn cs =
      sourceAdj M Q a r t sn cs * originalChiralCoupling M Q a r t sn cs m ω σ := by
  have hp' : r+a*Complex.I*cs ≠ 0 := by simpa only [mul_comm a Complex.I] using hp
  have hm' : r-a*Complex.I*cs ≠ 0 := by simpa only [mul_comm a Complex.I] using hm
  have hsn2 : sn^2=1-cs^2 := by linear_combination htrig
  have ht3 : t^3=(r^2-2*M*r+a^2+Q^2)*t := by rw [pow_succ,ht]
  have hsn3 : sn^3=(1-cs^2)*sn := by rw [pow_succ,hsn2]
  have hI3 : Complex.I^3 = -Complex.I := by norm_num [pow_succ,Complex.I_sq]
  have hI4 : Complex.I^4 = 1 := by norm_num [pow_succ,Complex.I_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chiralCoupling, originalChiralCoupling, sourceStar, sourceAdj,
      Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp [hp',hm'] <;>
    ring_nf <;>
    simp only [ht, ht3, hsn2, hsn3, Complex.I_sq, hI3,hI4] <;>
    ring_nf

end KN.Physics
