import KN.Angular.ExternalMityaginSiegl
import Mathlib.Analysis.Normed.Ring.Units

namespace KN.Analysis
noncomputable section
open KN.Angular.External
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Bounded perturbation on the unchanged, actual partial-operator domain. -/
def boundedPerturbation (T : E →ₗ.[ℂ] E) (B : E →L[ℂ] E) : E →ₗ.[ℂ] E where
  domain := T.domain
  toFun := T.toFun + B.toLinearMap.comp T.domain.subtype

omit [CompleteSpace E] in
@[simp] theorem boundedPerturbation_apply (T : E →ₗ.[ℂ] E) (B : E →L[ℂ] E) (u : T.domain) :
    boundedPerturbation T B u = T u+B u := rfl

/-- Explicit two-sided inverse after a bounded perturbation; domain membership
and both inverse identities are proved rather than included as assumptions. -/
def resolventPerturbation (T : E →ₗ.[ℂ] E) (z : ℂ) (R : ResolventAt T z)
    (B X : E →L[ℂ] E)
    (hXR : (1+B*R.inverse)*X=1) (hXL : X*(1+B*R.inverse)=1) :
    ResolventAt (boundedPerturbation T B) z where
  inverse := R.inverse*X
  mem_domain u := R.mem_domain (X u)
  right_inverse u := by
    change T ⟨R.inverse (X u),R.mem_domain (X u)⟩ + B (R.inverse (X u)) - z • R.inverse (X u) = u
    have h := congrArg (fun F : E →L[ℂ] E => F u) hXR
    change X u+B (R.inverse (X u))=u at h
    have hr := R.right_inverse (X u)
    calc
      _ = (T ⟨R.inverse (X u),R.mem_domain (X u)⟩-z • R.inverse (X u))+B (R.inverse (X u)) := by abel
      _ = u := by rw [hr]; exact h
  left_inverse u := by
    change R.inverse (X (T u+B u-z • (u:E))) = (u:E)
    have h := congrArg (fun F : E →L[ℂ] E => F (T u-z • (u:E))) hXL
    change X ((T u-z • (u:E))+B (R.inverse (T u-z • (u:E)))) = T u-z • (u:E) at h
    rw [R.left_inverse u] at h
    have he : T u+B u-z • (u:E)=(T u-z • (u:E))+B u := by abel
    rw [he,h,R.left_inverse u]

/-- Neumann construction of the actual perturbed resolvent. -/
def neumannResolvent (T : E →ₗ.[ℂ] E) (z : ℂ) (R : ResolventAt T z)
    (B : E →L[ℂ] E) (hsmall : ‖B*R.inverse‖<1) : ResolventAt (boundedPerturbation T B) z := by
  let U := Units.oneSub (-(B*R.inverse)) (by simpa using hsmall)
  have hU : (U : E →L[ℂ] E)=1+B*R.inverse := by simp [U]
  apply resolventPerturbation T z R B (↑U⁻¹)
  · rw [← hU]; exact U.val_inv
  · rw [← hU]; exact U.inv_val

end
end KN.Analysis
