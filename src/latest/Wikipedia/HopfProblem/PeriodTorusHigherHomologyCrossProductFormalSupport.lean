import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormal
import Wikipedia.HopfProblem.SingularMayerVietorisFormalChainsSupport

/-!
# Support of ordered-chain cross products

The point and edge products do not introduce vertices outside the product of
the vertex supports of their inputs.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W : Type*} {S : Set V} {T : Set W}

/-- The point product preserves the product of the two vertex-support sets. -/
theorem formalPointCrossProduct_mem_supported (q : ℕ)
    {c : FormalChains V 1} {d : FormalChains W (q + 1)}
    (hc : c ∈ formalChainsSupported S 1)
    (hd : d ∈ formalChainsSupported T (q + 1)) :
    formalPointCrossProduct q c d ∈ formalChainsSupported (S ×ˢ T) (q + 1) := by
  apply formalLinearMap_mem_of_supported ((formalPointCrossProduct q).flip d)
    (formalChainsSupported (S ×ˢ T) (q + 1)) hc
  intro v hv
  change formalPointCrossProduct q (formalSimplex v) d ∈ _
  rw [formalPointCrossProduct_simplex_left]
  exact formalMap_mem_supported (S := T) (T := S ×ˢ T)
    (fun w => (v 0, w)) (fun _ hw => ⟨hv 0, hw⟩) hd

/-- The edge product preserves the product of the two vertex-support sets. -/
theorem formalEdgeCrossProduct_mem_supported : ∀ (q : ℕ)
    {c : FormalChains V 2} {d : FormalChains W (q + 1)},
    c ∈ formalChainsSupported S 2 → d ∈ formalChainsSupported T (q + 1) →
    formalEdgeCrossProduct q c d ∈ formalChainsSupported (S ×ˢ T) (q + 2) := by
  intro q
  induction q with
  | zero =>
      intro c d hc hd
      apply formalLinearMap_mem_of_supported (formalEdgeCrossProduct 0 c)
        (formalChainsSupported (S ×ˢ T) 2) hd
      intro w hw
      rw [formalEdgeCrossProduct_zero_simplex_right]
      exact formalMap_mem_supported (S := S) (T := S ×ˢ T)
        (fun v => (v, w 0)) (fun _ hv => ⟨hv, hw 0⟩) hc
  | succ q ih =>
      intro c d hc hd
      apply formalLinearMap_mem_of_supported ((formalEdgeCrossProduct (q + 1)).flip d)
        (formalChainsSupported (S ×ˢ T) (q + 3)) hc
      intro v hv
      change formalEdgeCrossProduct (q + 1) (formalSimplex v) d ∈ _
      apply formalLinearMap_mem_of_supported
        (formalEdgeCrossProduct (q + 1) (formalSimplex v))
        (formalChainsSupported (S ×ˢ T) (q + 3)) hd
      intro w hw
      rw [formalEdgeCrossProduct_simplex_succ]
      apply formalCone_mem_supported (show (v 0, w 0) ∈ S ×ˢ T from ⟨hv 0, hw 0⟩)
      apply Submodule.sub_mem
      · exact formalPointCrossProduct_mem_supported (q + 1)
          (formalBoundary_mem_supported 1 (formalSimplex_mem_supported hv))
          (formalSimplex_mem_supported hw)
      · exact ih (formalSimplex_mem_supported hv)
          (formalBoundary_mem_supported (q + 1) (formalSimplex_mem_supported hw))

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
