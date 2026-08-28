import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalTriangle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalSupport

/-!
# Support of ordered triangle cross products

Triangle products stay in the product of the two input vertex supports, just
as point and edge products do.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W : Type*} {S : Set V} {T : Set W}

/-- The triangle product preserves the product of the two vertex-support sets. -/
theorem formalTriangleCrossProduct_mem_supported : ∀ (q : ℕ)
    {c : FormalChains V 3} {d : FormalChains W (q + 1)},
    c ∈ formalChainsSupported S 3 → d ∈ formalChainsSupported T (q + 1) →
    formalTriangleCrossProduct q c d ∈ formalChainsSupported (S ×ˢ T) (q + 3) := by
  intro q
  induction q with
  | zero =>
      intro c d hc hd
      apply formalLinearMap_mem_of_supported (formalTriangleCrossProduct 0 c)
        (formalChainsSupported (S ×ˢ T) 3) hd
      intro w hw
      rw [formalTriangleCrossProduct_zero_simplex_right]
      exact formalMap_mem_supported (S := S) (T := S ×ˢ T)
        (fun v => (v, w 0)) (fun _ hv => ⟨hv, hw 0⟩) hc
  | succ q ih =>
      intro c d hc hd
      apply formalLinearMap_mem_of_supported ((formalTriangleCrossProduct (q + 1)).flip d)
        (formalChainsSupported (S ×ˢ T) (q + 4)) hc
      intro v hv
      change formalTriangleCrossProduct (q + 1) (formalSimplex v) d ∈ _
      apply formalLinearMap_mem_of_supported
        (formalTriangleCrossProduct (q + 1) (formalSimplex v))
        (formalChainsSupported (S ×ˢ T) (q + 4)) hd
      intro w hw
      rw [formalTriangleCrossProduct_simplex_succ]
      apply formalCone_mem_supported (show (v 0, w 0) ∈ S ×ˢ T from ⟨hv 0, hw 0⟩)
      apply Submodule.add_mem
      · exact formalEdgeCrossProduct_mem_supported (q + 1)
          (formalBoundary_mem_supported 2 (formalSimplex_mem_supported hv))
          (formalSimplex_mem_supported hw)
      · exact ih (formalSimplex_mem_supported hv)
          (formalBoundary_mem_supported (q + 1) (formalSimplex_mem_supported hw))

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
