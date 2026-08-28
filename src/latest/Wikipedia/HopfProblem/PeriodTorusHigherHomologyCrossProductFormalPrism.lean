import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormal

/-!
# Endpoint and prism identities for the formal edge product

These formulas expose the two endpoint insertions, so that realizing the first
factor by a singular path gives the signed prism identity directly.  No
identification of the endpoints, or of a formal chain module with homology, is
used here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris
open scoped BigOperators

variable {V W : Type*}

/-- The boundary of an ordered edge is its target minus its source. -/
theorem formalBoundary_edge_simplex (v : Fin 2 → V) :
    formalBoundary 1 (formalSimplex v) =
      formalSimplex (fun _ : Fin 1 => v 1) - formalSimplex (fun _ : Fin 1 => v 0) := by
  rw [formalBoundary_simplex]
  change (∑ i : Fin 2, (-1 : ℤ) ^ i.val • formalSimplex (v ∘ i.succAbove)) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
    pow_zero, pow_one, one_smul, neg_one_smul, ← sub_eq_add_neg]
  congr 1 <;> congr 1 <;> funext i <;> rw [Fin.eq_zero i] <;> rfl

/-- Multiplying an edge boundary inserts its two endpoints with opposite signs. -/
theorem formalPointCrossProduct_edge_boundary (q : ℕ) (v : Fin 2 → V)
    (d : FormalChains W (q + 1)) :
    formalPointCrossProduct q (formalBoundary 1 (formalSimplex v)) d =
      formalMap (fun w => (v 1, w)) (q + 1) d -
        formalMap (fun w => (v 0, w)) (q + 1) d := by
  rw [formalBoundary_edge_simplex, map_sub, LinearMap.sub_apply,
    formalPointCrossProduct_simplex_left, formalPointCrossProduct_simplex_left]

/-- The degree-zero endpoint formula for an edge times an arbitrary zero-chain. -/
theorem formalBoundary_edgeCrossProduct_zero_simplex_left
    (v : Fin 2 → V) (d : FormalChains W 1) :
    formalBoundary 1 (formalEdgeCrossProduct 0 (formalSimplex v) d) =
      formalMap (fun w => (v 1, w)) 1 d - formalMap (fun w => (v 0, w)) 1 d := by
  rw [formalBoundary_edgeCrossProduct_zero, formalPointCrossProduct_edge_boundary]

/-- The positive-degree signed boundary formula, with the endpoints made explicit. -/
theorem formalBoundary_edgeCrossProduct_simplex_left (q : ℕ)
    (v : Fin 2 → V) (d : FormalChains W (q + 2)) :
    formalBoundary (q + 2) (formalEdgeCrossProduct (q + 1) (formalSimplex v) d) =
      formalMap (fun w => (v 1, w)) (q + 2) d -
        formalMap (fun w => (v 0, w)) (q + 2) d -
          formalEdgeCrossProduct q (formalSimplex v) (formalBoundary (q + 1) d) := by
  rw [formalBoundary_edgeCrossProduct, formalPointCrossProduct_edge_boundary]

/-- The formal edge product is an explicit prism between its endpoint insertions. -/
theorem formalEdgeCrossProduct_prism (q : ℕ) (v : Fin 2 → V)
    (d : FormalChains W (q + 2)) :
    formalBoundary (q + 2) (formalEdgeCrossProduct (q + 1) (formalSimplex v) d) +
        formalEdgeCrossProduct q (formalSimplex v) (formalBoundary (q + 1) d) =
      formalMap (fun w => (v 1, w)) (q + 2) d -
        formalMap (fun w => (v 0, w)) (q + 2) d := by
  rw [formalBoundary_edgeCrossProduct_simplex_left, sub_add_cancel]

/-- For a formal edge cycle the right boundary enters with a minus sign. -/
theorem formalBoundary_edgeCrossProduct_of_cycle (q : ℕ) (c : FormalChains V 2)
    (hc : formalBoundary 1 c = 0) (d : FormalChains W (q + 2)) :
    formalBoundary (q + 2) (formalEdgeCrossProduct (q + 1) c d) =
      -formalEdgeCrossProduct q c (formalBoundary (q + 1) d) := by
  rw [formalBoundary_edgeCrossProduct, hc, map_zero, LinearMap.zero_apply, zero_sub]

/-- A product of an edge cycle and a positive-degree cycle is a cycle. -/
theorem formalEdgeCrossProduct_isCycle (q : ℕ) (c : FormalChains V 2)
    (hc : formalBoundary 1 c = 0) (d : FormalChains W (q + 2))
    (hd : formalBoundary (q + 1) d = 0) :
    formalBoundary (q + 2) (formalEdgeCrossProduct (q + 1) c d) = 0 := by
  rw [formalBoundary_edgeCrossProduct_of_cycle q c hc, hd, map_zero, neg_zero]

/-- An edge cycle times any zero-chain is a cycle. -/
theorem formalEdgeCrossProduct_zero_isCycle (c : FormalChains V 2)
    (hc : formalBoundary 1 c = 0) (d : FormalChains W 1) :
    formalBoundary 1 (formalEdgeCrossProduct 0 c d) = 0 := by
  rw [formalBoundary_edgeCrossProduct_zero, hc, map_zero, LinearMap.zero_apply]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
