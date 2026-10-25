import KN.Kerr.SphericalSpectrum
import KN.Analysis.ResolventAdjoint
import KN.Analysis.ResolventEigenbasis

namespace KN.Kerr
noncomputable section
open KN.Analysis KN.Angular.External

lemma sphericalEigenvalue_lower (m s : ℤ) (n : ℕ) :
    (n:ℝ)*((n:ℝ)+1) ≤ sphericalEigenvalue m s n := by
  have hs : |(s:ℝ)| ≤ (max m.natAbs s.natAbs : ℕ) := by
    have h : (s.natAbs : ℝ) ≤ (max m.natAbs s.natAbs : ℕ) := by exact_mod_cast le_max_right m.natAbs s.natAbs
    simp
  have hL : (0:ℝ) ≤ (max m.natAbs s.natAbs : ℕ) := by positivity
  have hn : (0:ℝ) ≤ n := by positivity
  have hsq : (s:ℝ)^2 ≤ ((max m.natAbs s.natAbs : ℕ):ℝ)^2 := by
    nlinarith [sq_abs (s:ℝ), abs_nonneg (s:ℝ)]
  unfold sphericalEigenvalue sphericalLevel
  nlinarith [mul_nonneg hn hL]

lemma sphericalEigenvalue_resolvent_growth (m s : ℤ) (n : ℕ) :
    1 * ((n:ℝ)+1) ≤ ‖(sphericalEigenvalue m s n : ℂ)-Complex.I‖ := by
  have h := sphericalEigenvalue_lower m s n
  have hn : (0:ℝ) ≤ n := by positivity
  have hv : 0 ≤ sphericalEigenvalue m s n := le_trans (by positivity) h
  have hsq : ‖(sphericalEigenvalue m s n : ℂ)-Complex.I‖^2 =
      (sphericalEigenvalue m s n)^2+1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two]
  rcases n with _ | n
  · norm_num at h ⊢
    nlinarith [sq_nonneg (sphericalEigenvalue m s 0), norm_nonneg ((sphericalEigenvalue m s 0 : ℂ)-Complex.I)]
  · have hn1 : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hval : (n+1:ℕ)+1 ≤ sphericalEigenvalue m s (n+1) := by nlinarith
    have hnorm : sphericalEigenvalue m s (n+1) ≤ ‖(sphericalEigenvalue m s (n+1) : ℂ)-Complex.I‖ := by
      nlinarith [norm_nonneg ((sphericalEigenvalue m s (n+1) : ℂ)-Complex.I)]
    simpa only [one_mul] using hval.trans hnorm

/-- Canonical complex-frequency angular operator, on the unchanged regular graph domain. -/
def spheroidalOperator (m s : ℤ) (a : ℝ) (omega : ℂ) : AngularH →ₗ.[ℂ] AngularH :=
  boundedPerturbation (External.spherical_spectral_data m s).operator (frequencyMultiplier a s omega)

/-- Adjoint root completeness for the actual canonical fixed-m spin operator.
No semisimplicity or orthogonal spheroidal basis is assumed. -/
theorem spheroidal_dense_adjoint_roots (m s : ℤ) (a : ℝ) (omega : ℂ) :
    Dense (Submodule.span ℂ {u : AngularH | IsGeneralizedRoot (spheroidalOperator m s a omega).adjoint u} : Set AngularH) := by
  let S := External.spherical_spectral_data m s
  obtain ⟨R,_⟩ := selfAdjoint_exists_resolvent S.operator S.selfAdjoint Complex.I (by simp)
  have hHS := resolvent_hilbertSchmidt_of_eigenvalue_growth S.operator Complex.I R S.basis
    (fun n => (sphericalEigenvalue m s n : ℂ)) S.mem_domain S.eigen 1 (by norm_num)
    (sphericalEigenvalue_resolvent_growth m s)
  exact boundedPerturbation_dense_adjoint_roots S.operator S.selfAdjoint
    (frequencyMultiplier a s omega) S.basis Complex.I R hHS

end
end KN.Kerr
