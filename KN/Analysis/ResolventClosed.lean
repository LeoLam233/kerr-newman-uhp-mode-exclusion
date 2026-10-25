import KN.Analysis.ResolventPerturbation

namespace KN.Analysis
noncomputable section
open Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Bounded perturbations preserve closedness on exactly the original domain. -/
theorem boundedPerturbation_isClosed (T : E →ₗ.[ℂ] E) (hT : T.IsClosed)
    (B : E →L[ℂ] E) : (boundedPerturbation T B).IsClosed := by
  have he : ((boundedPerturbation T B).graph : Set (E×E)) =
      (fun p : E×E => (p.1,p.2-B p.1)) ⁻¹' (T.graph : Set (E×E)) := by
    ext p
    change p ∈ (boundedPerturbation T B).graph ↔ (p.1,p.2-B p.1) ∈ T.graph
    rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
    constructor
    · rintro ⟨u,hu,hv⟩
      refine ⟨u,hu,?_⟩
      change T u+B u=p.2 at hv
      rw [← hu]
      exact eq_sub_of_add_eq hv
    · rintro ⟨u,hu,hv⟩
      refine ⟨u,hu,?_⟩
      change T u+B u=p.2
      rw [← hu] at hv
      exact eq_sub_iff_add_eq.mp hv
  unfold LinearPMap.IsClosed
  rw [he]
  exact hT.preimage (continuous_fst.prodMk (continuous_snd.sub (B.continuous.comp continuous_fst)))

/-- Density of the partial-operator domain is unchanged by bounded perturbation. -/
theorem boundedPerturbation_dense (T : E →ₗ.[ℂ] E) (hT : Dense (T.domain : Set E))
    (B : E →L[ℂ] E) : Dense ((boundedPerturbation T B).domain : Set E) := hT

end
end KN.Analysis
