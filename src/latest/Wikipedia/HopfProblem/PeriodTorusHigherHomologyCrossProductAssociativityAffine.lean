import Wikipedia.HopfProblem.PeriodTorusHigherHomologyAffineTriple
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductTriangle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalAssociatorAxes

/-!
# Affine realization of the two parenthesized singular products

The actual triangle product in the first two factors and the actual edge
product in the last two factors realize the corresponding ordered-vertex
products in a right-associated triple product. Componentwise affine maps
also commute with this actual chain realization.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

/-- A product affine simplex takes its standard vertices to the prescribed pairs. -/
theorem productAffineSimplex_stdVertices_image {n p q : ℕ}
    (v : Fin (n + 1) → Simplex p × Simplex q) :
    productAffineSimplex v ∘ stdVertices n = v := by
  funext i
  exact productAffineSimplex_vertex v i

/-- Componentwise affine maps preserve the affine interpolation of triples. -/
theorem prodMap_tripleAffineSimplex {a b c m p q r : ℕ}
    (v : Fin (a + 1) → Simplex p) (w : Fin (b + 1) → Simplex q)
    (z : Fin (c + 1) → Simplex r)
    (t : Fin (m + 1) → Simplex a × (Simplex b × Simplex c)) :
    ((affineSimplex v).prodMap ((affineSimplex w).prodMap (affineSimplex z))).comp
        (tripleAffineSimplex t) =
      tripleAffineSimplex (fun j =>
        (affineSimplex v (t j).1,
          (affineSimplex w (t j).2.1, affineSimplex z (t j).2.2))) := by
  apply ContinuousMap.ext
  intro s
  apply Prod.ext
  · exact congrArg (fun f : C(Simplex m, Simplex p) => f s)
      (affineSimplex_comp v (fun j => (t j).1))
  · apply Prod.ext
    · exact congrArg (fun f : C(Simplex m, Simplex q) => f s)
        (affineSimplex_comp w (fun j => (t j).2.1))
    · exact congrArg (fun f : C(Simplex m, Simplex r) => f s)
        (affineSimplex_comp z (fun j => (t j).2.2))

/-- Componentwise affine maps commute with triple realization in actual singular chains. -/
theorem inducedChain_tripleAffineChainMap {a b c m p q r : ℕ}
    (v : Fin (a + 1) → Simplex p) (w : Fin (b + 1) → Simplex q)
    (z : Fin (c + 1) → Simplex r)
    (t : FormalChains (Simplex a × (Simplex b × Simplex c)) (m + 1)) :
    inducedChain
        ((affineSimplex v).prodMap ((affineSimplex w).prodMap (affineSimplex z))) m
        (tripleAffineChainMap a b c m t) =
      tripleAffineChainMap p q r m
        (formalMap
          ((affineSimplex v).prodMap ((affineSimplex w).prodMap (affineSimplex z)))
          (m + 1) t) := by
  have h : (inducedChain
      ((affineSimplex v).prodMap ((affineSimplex w).prodMap (affineSimplex z))) m).comp
        (tripleAffineChainMap a b c m) =
      (tripleAffineChainMap p q r m).comp
        (formalMap
          ((affineSimplex v).prodMap ((affineSimplex w).prodMap (affineSimplex z)))
          (m + 1)) := by
    apply formalChains_ext
    intro s
    simp only [LinearMap.comp_apply, tripleAffineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, prodMap_tripleAffineSimplex]
    rfl
  exact LinearMap.congr_fun h t

/-- The left-parenthesized triangle product realizes the reassociated formal product. -/
theorem crossProductTriangle_productAffineChainMap_left (p q r n : ℕ)
    (a : FormalChains (Simplex p × Simplex q) 3)
    (b : FormalChains (Simplex r) (n + 1)) :
    inducedChain
        (Homeomorph.prodAssoc (Simplex p) (Simplex q) (Simplex r) : C(_, _)) (n + 2)
        (crossProductTriangle (Simplex p × Simplex q) (Simplex r) n
          (productAffineChainMap p q 2 a) (affineChainMap r n b)) =
      tripleAffineChainMap p q r (n + 2)
        (formalMap
          (fun x : (Simplex p × Simplex q) × Simplex r => (x.1.1, (x.1.2, x.2)))
          (n + 3) (formalTriangleCrossProduct n a b)) := by
  have h : integerBilinearPostcompose
      (integerBilinearPrecompose
        (crossProductTriangle (Simplex p × Simplex q) (Simplex r) n)
        (productAffineChainMap p q 2) (affineChainMap r n))
      (inducedChain
        (Homeomorph.prodAssoc (Simplex p) (Simplex q) (Simplex r) : C(_, _)) (n + 2)) =
      integerBilinearPostcompose (formalTriangleCrossProduct n)
        ((tripleAffineChainMap p q r (n + 2)).comp
          (formalMap
            (fun x : (Simplex p × Simplex q) × Simplex r => (x.1.1, (x.1.2, x.2)))
            (n + 3))) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      productAffineChainMap_simplex, affineChainMap_simplex, crossProductTriangle_simplex,
      LinearMap.comp_apply]
    rw [← LinearMap.comp_apply, ← inducedChain_comp]
    change inducedChain (affineProductLeft v w) (n + 2)
      (productAffineChainMap 2 n (n + 2)
        (formalTriangleCrossProduct n (formalSimplex (stdVertices 2))
          (formalSimplex (stdVertices n)))) = _
    rw [inducedChain_affineProductLeft]
    apply congrArg (tripleAffineChainMap p q r (n + 2))
    change formalMap
      ((fun x : (Simplex p × Simplex q) × Simplex r => (x.1.1, (x.1.2, x.2))) ∘
        Prod.map (productAffineSimplex v) (affineSimplex w)) (n + 3)
      (formalTriangleCrossProduct n (formalSimplex (stdVertices 2))
        (formalSimplex (stdVertices n))) = _
    rw [← formalMap_comp_apply, formalMap_triangleCrossProduct,
      formalMap_simplex, formalMap_simplex, productAffineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The right-parenthesized edge product realizes the formal product of triple vertices. -/
theorem crossProductEdge_productAffineChainMap_right (p q r n : ℕ)
    (a : FormalChains (Simplex p) 2)
    (b : FormalChains (Simplex q × Simplex r) (n + 1)) :
    crossProductEdge (Simplex p) (Simplex q × Simplex r) n
        (affineChainMap p 1 a) (productAffineChainMap q r n b) =
      tripleAffineChainMap p q r (n + 1) (formalEdgeCrossProduct n a b) := by
  have h : integerBilinearPrecompose
      (crossProductEdge (Simplex p) (Simplex q × Simplex r) n)
      (affineChainMap p 1) (productAffineChainMap q r n) =
      integerBilinearPostcompose (formalEdgeCrossProduct n)
        (tripleAffineChainMap p q r (n + 1)) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      affineChainMap_simplex, productAffineChainMap_simplex, crossProductEdge_simplex]
    change inducedChain (affineProductRight v w) (n + 1)
      (productAffineChainMap 1 n (n + 1)
        (formalEdgeCrossProduct n (formalSimplex (stdVertices 1))
          (formalSimplex (stdVertices n)))) = _
    rw [inducedChain_affineProductRight]
    change tripleAffineChainMap p q r (n + 1)
      (formalMap (Prod.map (affineSimplex v) (productAffineSimplex w)) (n + 2)
        (formalEdgeCrossProduct n (formalSimplex (stdVertices 1))
          (formalSimplex (stdVertices n)))) = _
    rw [formalMap_edgeCrossProduct, formalMap_simplex, formalMap_simplex,
      affineSimplex_stdVertices_image, productAffineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
