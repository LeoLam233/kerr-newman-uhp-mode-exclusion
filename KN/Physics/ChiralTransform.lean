import KN.Physics.SourceRecovery
import KN.Physics.HorizonAlgebra

noncomputable section
namespace KN.Physics
open Matrix

def chiralInput (F Q t sign : ℂ) (u : Fin 4 → ℂ) : Fin 2 → ℂ :=
  F • ![u 0 + sign*Complex.I*t*u 1, -2*Q*(u 2 + sign*Complex.I*t*u 3)]

/-- Simultaneous chiral maps recover all four original components. -/
theorem chiralInput_zero (F Q t : ℂ) (hF : F ≠ 0) (hQ : Q ≠ 0) (ht : t ≠ 0)
    (u : Fin 4 → ℂ) (hp : chiralInput F Q t 1 u = 0)
    (hm : chiralInput F Q t (-1) u = 0) : u = 0 := by
  have hp' : ![u 0 + Complex.I*t*u 1, -2*Q*(u 2 + Complex.I*t*u 3)] = (0 : Fin 2 → ℂ) := by
    have hn := (smul_eq_zero.mp hp).resolve_left hF
    simpa only [one_mul] using hn
  have hm' : ![u 0 - Complex.I*t*u 1, -2*Q*(u 2 - Complex.I*t*u 3)] = (0 : Fin 2 → ℂ) := by
    have hn := (smul_eq_zero.mp hm).resolve_left hF
    simpa only [neg_one_mul, neg_mul, sub_eq_add_neg, one_mul] using hn
  have hα : Complex.I*t ≠ 0 := mul_ne_zero Complex.I_ne_zero ht
  have h01 := recover_chiral_pair hα (congrFun hp' 0) (congrFun hm' 0)
  have h2p : u 2 + Complex.I*t*u 3 = 0 := by
    have he := congrFun hp' 1
    change (-2*Q)*(u 2 + Complex.I*t*u 3) = 0 at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hQ)
  have h2m : u 2 - Complex.I*t*u 3 = 0 := by
    have he := congrFun hm' 1
    change (-2*Q)*(u 2 - Complex.I*t*u 3) = 0 at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hQ)
  have h23 := recover_chiral_pair hα h2p h2m
  ext i; fin_cases i <;> simp [h01.1, h01.2, h23.1, h23.2]

/-- Both actual matrix source blocks are injective. -/
theorem transformed_chiral_zero (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det ≠ 0)
    (F Q t : ℂ) (hF : F ≠ 0) (hQ : Q ≠ 0) (ht : t ≠ 0) (u : Fin 4 → ℂ)
    (hp : A.adjugate *ᵥ chiralInput F Q t 1 u = 0)
    (hm : A.conjTranspose *ᵥ chiralInput F Q t (-1) u = 0) : u = 0 := by
  apply chiralInput_zero F Q t hF hQ ht u
  · exact (adjugate_mulVec_eq_zero_iff hA _).mp hp
  · apply Matrix.eq_zero_of_mulVec_eq_zero _ hm
    simpa only [Matrix.det_conjTranspose, ne_eq, star_eq_zero] using hA

end KN.Physics
