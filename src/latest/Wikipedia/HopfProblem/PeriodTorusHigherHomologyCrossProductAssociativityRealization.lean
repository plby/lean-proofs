import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductAssociativity
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductAssociativityAffine

/-!
# Realizing the associator equation in actual singular chains

The actual associator homotopy and both parenthesized products agree with
triple affine realization of their ordered-vertex constructions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Triple affine realization intertwines the actual and formal associator homotopies. -/
theorem crossProductAssociatorHomotopy_affineChainMap (p q r n : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) 2)
    (c : FormalChains (Simplex r) (n + 1)) :
    crossProductAssociatorHomotopy (Simplex p) (Simplex q) (Simplex r) n
        (affineChainMap p 1 a) (affineChainMap q 1 b) (affineChainMap r n c) =
      tripleAffineChainMap p q r (n + 3) (formalAssociatorHomotopy n a b c) := by
  have heq : integerTrilinearPrecompose
        (crossProductAssociatorHomotopy (Simplex p) (Simplex q) (Simplex r) n)
        (affineChainMap p 1) (affineChainMap q 1) (affineChainMap r n) =
      integerTrilinearPostcompose (formalAssociatorHomotopy n)
        (tripleAffineChainMap p q r (n + 3)) := by
    apply formalChains_ext
    intro v
    apply formalChains_ext
    intro w
    apply formalChains_ext
    intro z
    simp only [integerTrilinearPrecompose_apply, integerTrilinearPostcompose_apply,
      affineChainMap_simplex, crossProductAssociatorHomotopy_simplex]
    rw [inducedChain_tripleAffineChainMap]
    change tripleAffineChainMap p q r (n + 3)
      (formalMap (Prod.map (affineSimplex v)
        (Prod.map (affineSimplex w) (affineSimplex z))) (n + 4)
        (formalAssociatorHomotopy n (formalSimplex (stdVertices 1))
          (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices n)))) = _
    rw [formalMap_associatorHomotopy, formalMap_simplex, formalMap_simplex,
      formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image, affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

/-- Both actual parenthesizations realize their formal counterparts. -/
theorem crossProductAssociatorDefect_affineChainMap (p q r n : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) 2)
    (c : FormalChains (Simplex r) (n + 1)) :
    crossProductAssociatorDefect (Simplex p) (Simplex q) (Simplex r) n
        (affineChainMap p 1 a) (affineChainMap q 1 b) (affineChainMap r n c) =
      tripleAffineChainMap p q r (n + 2) (formalAssociatorDefect n a b c) := by
  simp only [crossProductAssociatorDefect_apply, crossProductEdge_affineChainMap, Nat.reduceAdd,
    crossProductTriangle_productAffineChainMap_left,
    crossProductEdge_productAffineChainMap_right, formalAssociatorDefect_apply, map_sub]

/-- The degree-zero associator homotopy identity after affine realization. -/
theorem crossProductAssociatorHomotopy_boundary_zero_affine (p q r : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) 2)
    (c : FormalChains (Simplex r) 1) :
    ((singularComplex (Simplex p × (Simplex q × Simplex r))).d 3 2).hom
        (crossProductAssociatorHomotopy (Simplex p) (Simplex q) (Simplex r) 0
          (affineChainMap p 1 a) (affineChainMap q 1 b) (affineChainMap r 0 c)) =
      crossProductAssociatorDefect (Simplex p) (Simplex q) (Simplex r) 0
        (affineChainMap p 1 a) (affineChainMap q 1 b) (affineChainMap r 0 c) := by
  rw [crossProductAssociatorHomotopy_affineChainMap, tripleAffineChainMap_boundary,
    formalAssociatorHomotopy_boundary_zero, crossProductAssociatorDefect_affineChainMap]

/-- The equation `d Q + Q d = D` after triple affine realization. -/
theorem crossProductAssociatorHomotopy_boundary_affine (p q r n : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) 2)
    (c : FormalChains (Simplex r) (n + 2)) :
    ((singularComplex (Simplex p × (Simplex q × Simplex r))).d (n + 4) (n + 3)).hom
        (crossProductAssociatorHomotopy (Simplex p) (Simplex q) (Simplex r) (n + 1)
          (affineChainMap p 1 a) (affineChainMap q 1 b) (affineChainMap r (n + 1) c)) +
      crossProductAssociatorHomotopy (Simplex p) (Simplex q) (Simplex r) n
        (affineChainMap p 1 a) (affineChainMap q 1 b)
        (((singularComplex (Simplex r)).d (n + 1) n).hom (affineChainMap r (n + 1) c)) =
      crossProductAssociatorDefect (Simplex p) (Simplex q) (Simplex r) (n + 1)
        (affineChainMap p 1 a) (affineChainMap q 1 b) (affineChainMap r (n + 1) c) := by
  rw [crossProductAssociatorHomotopy_affineChainMap, tripleAffineChainMap_boundary,
    affineChainMap_boundary, crossProductAssociatorHomotopy_affineChainMap,
    ← map_add, formalAssociatorHomotopy_boundary, crossProductAssociatorDefect_affineChainMap]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
