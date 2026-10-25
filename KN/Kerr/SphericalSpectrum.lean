import KN.Kerr.HilbertAngular
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
Classical spherical spectral interface. Goldberg, Macfarlane, Newman,
Rohrlich and Sudarshan, J. Math. Phys. 8 (1967), 2155–2161, §2, equations
(2.3), (2.5), (2.8), and the completeness statement on p.2156.
Primary author-hosted text: https://web2.ph.utexas.edu/~gsudama/pub/1967_008.pdf
The usual self-adjoint closure formulation is included. The graph is fixed
below as the closure of the smooth spin-section core; no maximal scalar
endpoint extension is allowed. This interface contains no complex-frequency
root completeness, radial statement, or exclusion theorem.
-/
namespace KN.Kerr
noncomputable section
open scoped ComplexInnerProductSpace

def sphericalLevel (m s : ℤ) (n : ℕ) : ℝ := n + max m.natAbs s.natAbs

def sphericalEigenvalue (m s : ℤ) (n : ℕ) : ℝ :=
  sphericalLevel m s n * (sphericalLevel m s n + 1) - (s : ℝ)^2

/-- Exact canonical spherical spectral data. -/
structure SphericalSpectralData (m s : ℤ) where
  operator : AngularH →ₗ.[ℂ] AngularH
  graph_eq : (operator.graph : Set (AngularH × AngularH)) = sphericalClosedGraph m s
  selfAdjoint : IsSelfAdjoint operator
  basis : HilbertBasis ℕ ℂ AngularH
  mem_domain : ∀ n, basis n ∈ operator.domain
  eigen : ∀ n, operator ⟨basis n, mem_domain n⟩ =
    (sphericalEigenvalue m s n : ℂ) • basis n

namespace External
/-- Published spherical spectral theorem, including the canonical regular
self-adjoint realization. All perturbative and radial work remains separate. -/
axiom spherical_spectral_data (m s : ℤ) : SphericalSpectralData m s
end External

end
end KN.Kerr
