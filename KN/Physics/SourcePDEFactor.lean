import KN.Physics.SourcePDECalculus

namespace KN.Physics
noncomputable section
open Matrix

/-- The integrating-factor jet is the genuine directional derivative, not an
independent formal variable. -/
theorem sourceD_factorX (t ε M Q : ℂ) (f1 f2 f3 f4 : ℝ → ℝ → ℂ) (r θ : ℝ)
    (h1 : SourceDifferentiableAt f1 r θ) (h2 : SourceDifferentiableAt f2 r θ)
    (h3 : SourceDifferentiableAt f3 r θ) (h4 : SourceDifferentiableAt f4 r θ)
    (hn1 : f1 r θ≠0) (hn3 : f3 r θ≠0)
    (hd1 : sourceD t ε f1 r θ=f2 r θ) (hd2 : sourceD t ε f2 r θ=f1 r θ-M)
    (hd3 : sourceD t ε f3 r θ=f4 r θ) (hd4 : sourceD t ε f4 r θ=f3 r θ-M) :
    (fun i j => sourceD t ε (fun x y => factorX M Q (f1 x y) (f2 x y) (f3 x y) (f4 x y) i j) r θ)=
      factorDX M Q (f1 r θ) (f2 r θ) (f3 r θ) (f4 r θ) := by
  have hc := SourceDifferentiableAt.const
  have h00 : sourceD t ε (fun x y => Q*f4 x y/f1 x y) r θ =
      Q*((f3 r θ-M)*f1 r θ-f4 r θ*f2 r θ)/(f1 r θ)^2 := by
    rw [sourceD_div _ _ _ _ _ _ ((hc Q r θ).mul h4) h1 hn1,
      sourceD_const_mul _ _ _ _ _ _ h4,hd4,hd1]
    ring
  have h11 : sourceD t ε (fun x y => Q*f2 x y/f3 x y) r θ =
      Q*((f1 r θ-M)*f3 r θ-f2 r θ*f4 r θ)/(f3 r θ)^2 := by
    rw [sourceD_div _ _ _ _ _ _ ((hc Q r θ).mul h2) h3 hn3,
      sourceD_const_mul _ _ _ _ _ _ h2,hd2,hd3]
    ring
  have h01 : sourceD t ε (fun x y => -Complex.I*(M-Q^2/f1 x y)) r θ =
      -Complex.I*Q^2*f2 r θ/(f1 r θ)^2 := by
    rw [sourceD_const_mul _ _ _ _ _ _ ((hc M r θ).sub ((hc (Q^2) r θ).div h1 hn1)),
      sourceD_sub _ _ _ _ _ _ (hc M r θ) ((hc (Q^2) r θ).div h1 hn1),sourceD_const,
      sourceD_div _ _ _ _ _ _ (hc (Q^2) r θ) h1 hn1,sourceD_const,hd1]
    ring
  have h10 : sourceD t ε (fun x y => Complex.I*(M-Q^2/f3 x y)) r θ =
      Complex.I*Q^2*f4 r θ/(f3 r θ)^2 := by
    rw [sourceD_const_mul _ _ _ _ _ _ ((hc M r θ).sub ((hc (Q^2) r θ).div h3 hn3)),
      sourceD_sub _ _ _ _ _ _ (hc M r θ) ((hc (Q^2) r θ).div h3 hn3),sourceD_const,
      sourceD_div _ _ _ _ _ _ (hc (Q^2) r θ) h3 hn3,sourceD_const,hd3]
    ring
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [factorX,factorDX] using h00
  · simpa [factorX,factorDX] using h01
  · simpa [factorX,factorDX] using h10
  · simpa [factorX,factorDX] using h11

end
end KN.Physics
