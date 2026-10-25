import KN.Kerr.EllipticRegularity
import KN.Kerr.SphericalCompleteness
import KN.Kerr.WhitingInterface

namespace KN.Kerr
noncomputable section
open Set

/-- A genuine adjoint angular eigenvector supplies the regular primal angular
function at the conjugate eigenvalue. This uses no semisimplicity assumption. -/
theorem regularAngularEigenfunction_of_adjoint_eigenvector
    (b : KN.Background) (m s : ℤ) (omega z : ℂ) (v : AngularH) (hvne : v ≠ 0)
    (hv : v ∈ (spheroidalOperator m s b.a omega).adjoint.domain)
    (heig : (spheroidalOperator m s b.a omega).adjoint ⟨v,hv⟩=z • v) :
    ∃ u : ℝ → ℂ, RegularAngularEigenfunction b m s omega (star z) u := by
  let S := External.spherical_spectral_data m s
  obtain ⟨u,_,_,hreg,hne,heq⟩ := External.regular_adjoint_eigenfunction m s
    S.operator S.graph_eq (frequencyPotential b.a s omega)
    (frequencyPotential_memLp b.a s omega)
    (frequencyPotential_smoothAxisymmetric b.a s omega) z v hvne hv heig
  refine ⟨fun θ => star (u θ), hreg.conjugate, ?_, ?_⟩
  · obtain ⟨θ,hθ,hn⟩ := hne
    exact ⟨θ,hθ,by simpa only [ne_eq,star_eq_zero] using hn⟩
  · intro θ hθ
    rw [angularOperator_add_potential,angularOperator_static_star]
    have h := congrArg star (heq θ hθ)
    simpa only [star_add,star_mul,star_star,mul_comm] using h

end
end KN.Kerr
