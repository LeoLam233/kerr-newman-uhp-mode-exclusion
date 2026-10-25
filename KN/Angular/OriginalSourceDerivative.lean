import KN.Angular.OriginalSourceBoundary
import KN.Physics.SourcePDEEuclidean
import KN.Analysis.LpDerivativeRepresentative

namespace KN.Angular.OriginalSourceField
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set KN.Physics
open scoped ContDiff
variable {positive : Bool} {b : KN.Background} {m : ℤ} {omega : ℂ}

/-- Differentiation of the actual L² source transform agrees with its ordinary
pointwise radial derivative, derived by the subsequence uniqueness argument. -/
theorem transformed_derivative_ae (U : OriginalSourceField positive b m omega)
    {r : ℝ} (hr : b.rPlus<r) :
    deriv U.transformed r =ᵐ[angularMeasure] fun θ =>
      deriv (fun x => WithLp.toLp 2 (sourceFullVector positive b U.components x θ)) r := by
  apply KN.Analysis.lp_derivative_representative hr
    ((U.transformed_smooth.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hr)).hasDerivAt (fun x hx => U.transformed_ae hx)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
  exact (sourceFullEuclidean_differentiable positive b U.components hr hθ.1 hθ.2
    (U.source_differentiable r θ hr hθ.1 hθ.2)).1

end
end KN.Angular.OriginalSourceField
