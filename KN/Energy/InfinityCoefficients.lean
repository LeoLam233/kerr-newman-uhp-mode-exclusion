import KN.Energy.TailGrowth
import KN.Energy.PhysicalFiniteEndpoint

noncomputable section
namespace KN.Energy

theorem polyBound_pow {f : ℝ → ℂ} (hf : PolyBound f) (n : ℕ) :
    PolyBound (fun r => f r^n) := by
  induction n with
  | zero => simpa only [pow_zero] using polyBound_const (1:ℂ)
  | succ n ih => simpa only [pow_succ] using polyBound_mul ih hf

theorem polyBound_sub {f g : ℝ → ℂ} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun r => f r-g r) := by
  simpa only [mul_neg_one,sub_eq_add_neg] using
    polyBound_add hf (polyBound_mul hg (polyBound_const (-1:ℂ)))

theorem reflected_linear_polyBound (c : ℝ) :
    PolyBound (fun r : ℝ => ((-r+c:ℝ):ℂ)) := by
  have h := polynomialConormal_polynomial (-Polynomial.X+Polynomial.C (c:ℂ))
  simpa [PolyBound] using h 0

theorem reflected_inverse_polyBound (c : ℝ) :
    PolyBound (fun r : ℝ => ((-r+c:ℝ):ℂ)⁻¹) := by
  have h := polyBound_mul (polyBound_const (-1:ℂ)) (reciprocal_polyBound c)
  convert h using 1
  ext r
  dsimp [reciprocal]
  rw [show -r+c = -(r-c) by ring]
  simp only [Complex.ofReal_neg, inv_neg, neg_one_mul]

theorem physical_reflected_coefficients (positive : Bool) (b : KN.Background) (T L σ D : ℝ) :
    PolyBound (fun r : ℝ => (systemP positive b (-r):ℂ)) ∧
    PolyBound (fun r : ℝ => (systemW positive b (-r):ℂ)) ∧
    PolyBound (fun r : ℝ => (angularK b T L σ (-r):ℂ)) ∧
    PolyBound (fun r : ℝ => (radialR b (-r)-D:ℝ)) := by
  have hx := reflected_inverse_polyBound 0
  have hx' : PolyBound (fun r : ℝ => ((-r:ℝ):ℂ)⁻¹) := by simpa only [add_zero] using hx
  have he := reflected_linear_polyBound b.eta
  have hei := reflected_inverse_polyBound b.eta
  have hh := reflected_linear_polyBound (b.eta+2)
  have hhi := reflected_inverse_polyBound b.h
  constructor
  · cases positive
    · have h := polyBound_mul (polyBound_mul hh (polyBound_pow he 4)) hx'
      convert h using 1
      ext r
      simp [systemP,Pminus,div_eq_mul_inv,add_assoc]
    · have h := polyBound_mul hh (polyBound_mul hx' (polyBound_pow hei 2))
      convert h using 1
      ext r
      simp [systemP,Pplus,div_eq_mul_inv]
      ring
  constructor
  · cases positive
    · have h := polyBound_mul (polyBound_pow he 3) hx'
      convert h using 1
      ext r
      simp [systemW,Wminus,div_eq_mul_inv]
    · have h := polyBound_mul hx' (polyBound_pow hei 3)
      convert h using 1
      ext r
      simp [systemW,Wplus,div_eq_mul_inv,mul_comm]
  constructor
  · have h := polyBound_add (polyBound_const (T:ℂ))
      (polyBound_mul (polyBound_mul (polyBound_const (b.c:ℂ)) hx') (polyBound_const ((L-σ*b.beta:ℝ):ℂ)))
    convert h using 1
    ext r
    simp [angularK,div_eq_mul_inv]
  · have h := polyBound_sub
      (polyBound_sub
        (polyBound_add
          (polyBound_mul (polyBound_pow he 2)
            (polyBound_sub (polyBound_const ((b.delta^2:ℝ):ℂ))
              (polyBound_mul (polyBound_const ((2*b.M^2:ℝ):ℂ)) hhi)))
          (polyBound_const ((b.a^2*b.eta^2:ℝ):ℂ)))
        (polyBound_mul (polyBound_const ((2*b.a^2:ℝ):ℂ)) (reflected_linear_polyBound 0)))
      (polyBound_const (D:ℂ))
    convert h using 1
    ext r
    simp [radialR,div_eq_mul_inv]

end KN.Energy
