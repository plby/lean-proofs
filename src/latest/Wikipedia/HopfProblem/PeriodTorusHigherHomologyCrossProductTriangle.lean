import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalTriangle

/-!
# Actual singular cross products with a two-chain

The formal triangle product is evaluated in the product of standard simplices
and pushed forward by pairs of singular simplices. Its boundary formula has
the positive sign in the second term. In particular, crossing a two-boundary
with a cycle gives an actual boundary in the product space.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Cross product of an actual singular two-chain with an actual singular `n`-chain. -/
def crossProductTriangle (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Chains X 2 →ₗ[ℤ] Chains Y n →ₗ[ℤ] Chains (X × Y) (n + 2) :=
  chainBilinearLift X Y 2 n fun σ τ => inducedChain (σ.prodMap τ) (n + 2)
    (productAffineChainMap 2 n (n + 2)
      (formalTriangleCrossProduct n (formalSimplex (stdVertices 2))
        (formalSimplex (stdVertices n))))

@[simp] theorem crossProductTriangle_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (σ : SingularSimplex X 2) (τ : SingularSimplex Y n) :
    crossProductTriangle X Y n (simplexChain X 2 σ) (simplexChain Y n τ) =
      inducedChain (σ.prodMap τ) (n + 2)
        (productAffineChainMap 2 n (n + 2)
          (formalTriangleCrossProduct n (formalSimplex (stdVertices 2))
            (formalSimplex (stdVertices n)))) :=
  chainBilinearLift_simplex X Y 2 n _ σ τ

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Naturality of the actual triangle cross product under arbitrary continuous maps. -/
theorem crossProductTriangle_natural (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : Chains X 2) (b : Chains Y n) :
    inducedChain (f.prodMap g) (n + 2) (crossProductTriangle X Y n a b) =
      crossProductTriangle X' Y' n (inducedChain f 2 a) (inducedChain g n b) := by
  have h : integerBilinearPostcompose (crossProductTriangle X Y n)
        (inducedChain (f.prodMap g) (n + 2)) =
      integerBilinearPrecompose (crossProductTriangle X' Y' n)
        (inducedChain f 2) (inducedChain g n) := by
    apply chainBilinearMap_ext X Y 2 n
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      inducedChain_simplex, crossProductTriangle_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Affine realization intertwines the formal and actual triangle products. -/
theorem crossProductTriangle_affineChainMap (p q n : ℕ)
    (a : FormalChains (Simplex p) 3) (b : FormalChains (Simplex q) (n + 1)) :
    crossProductTriangle (Simplex p) (Simplex q) n
        (affineChainMap p 2 a) (affineChainMap q n b) =
      productAffineChainMap p q (n + 2) (formalTriangleCrossProduct n a b) := by
  have h : integerBilinearPrecompose (crossProductTriangle (Simplex p) (Simplex q) n)
        (affineChainMap p 2) (affineChainMap q n) =
      integerBilinearPostcompose (formalTriangleCrossProduct n)
        (productAffineChainMap p q (n + 2)) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      affineChainMap_simplex, crossProductTriangle_simplex]
    rw [inducedChain_productAffineChainMap]
    change productAffineChainMap p q (n + 2)
      (formalMap (Prod.map (affineSimplex v) (affineSimplex w)) (n + 3)
        (formalTriangleCrossProduct n (formalSimplex (stdVertices 2))
          (formalSimplex (stdVertices n)))) = _
    rw [formalMap_triangleCrossProduct, formalMap_simplex, formalMap_simplex,
      affineSimplex_stdVertices_image, affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The degree-zero product-boundary identity on realized formal chains. -/
theorem crossProductTriangle_boundary_zero_affine (p q : ℕ)
    (a : FormalChains (Simplex p) 3) (b : FormalChains (Simplex q) 1) :
    ((singularComplex (Simplex p × Simplex q)).d 2 1).hom
        (crossProductTriangle (Simplex p) (Simplex q) 0
          (affineChainMap p 2 a) (affineChainMap q 0 b)) =
      crossProductEdge (Simplex p) (Simplex q) 0
        (((singularComplex (Simplex p)).d 2 1).hom (affineChainMap p 2 a))
        (affineChainMap q 0 b) := by
  rw [crossProductTriangle_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_triangleCrossProduct_zero, affineChainMap_boundary,
    crossProductEdge_affineChainMap]

/-- The degree-two signed product-boundary identity on realized formal chains. -/
theorem crossProductTriangle_boundary_affine (p q n : ℕ)
    (a : FormalChains (Simplex p) 3) (b : FormalChains (Simplex q) (n + 2)) :
    ((singularComplex (Simplex p × Simplex q)).d (n + 3) (n + 2)).hom
        (crossProductTriangle (Simplex p) (Simplex q) (n + 1)
          (affineChainMap p 2 a) (affineChainMap q (n + 1) b)) =
      crossProductEdge (Simplex p) (Simplex q) (n + 1)
          (((singularComplex (Simplex p)).d 2 1).hom (affineChainMap p 2 a))
          (affineChainMap q (n + 1) b) +
        crossProductTriangle (Simplex p) (Simplex q) n (affineChainMap p 2 a)
          (((singularComplex (Simplex q)).d (n + 1) n).hom (affineChainMap q (n + 1) b)) := by
  rw [crossProductTriangle_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_triangleCrossProduct, map_add, affineChainMap_boundary,
    affineChainMap_boundary, crossProductEdge_affineChainMap,
    crossProductTriangle_affineChainMap]

/-- The boundary of an actual two-chain crossed with a zero-chain. -/
theorem crossProductTriangle_boundary_zero (a : Chains X 2) (b : Chains Y 0) :
    ((singularComplex (X × Y)).d 2 1).hom (crossProductTriangle X Y 0 a b) =
      crossProductEdge X Y 0 (((singularComplex X).d 2 1).hom a) b := by
  have h : integerBilinearPostcompose (crossProductTriangle X Y 0)
        ((singularComplex (X × Y)).d 2 1).hom =
      integerBilinearPrecompose (crossProductEdge X Y 0)
        ((singularComplex X).d 2 1).hom LinearMap.id := by
    apply chainBilinearMap_ext X Y 2 0
    intro σ τ
    have hstd := crossProductTriangle_boundary_zero_affine 2 0
      (formalSimplex (stdVertices 2)) (formalSimplex (stdVertices 0))
    have hστ := congrArg (inducedChain (σ.prodMap τ) 1) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.id_apply, inducedChain_boundary, crossProductTriangle_natural,
      crossProductEdge_natural, affineChainMap_stdVertices, inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The actual singular-chain Leibniz rule with a degree-two left factor. -/
theorem crossProductTriangle_boundary (n : ℕ) (a : Chains X 2) (b : Chains Y (n + 1)) :
    ((singularComplex (X × Y)).d (n + 3) (n + 2)).hom
        (crossProductTriangle X Y (n + 1) a b) =
      crossProductEdge X Y (n + 1) (((singularComplex X).d 2 1).hom a) b +
        crossProductTriangle X Y n a (((singularComplex Y).d (n + 1) n).hom b) := by
  have h : integerBilinearPostcompose (crossProductTriangle X Y (n + 1))
        ((singularComplex (X × Y)).d (n + 3) (n + 2)).hom =
      integerBilinearPrecompose (crossProductEdge X Y (n + 1))
          ((singularComplex X).d 2 1).hom LinearMap.id +
        integerBilinearPrecompose (crossProductTriangle X Y n) LinearMap.id
          ((singularComplex Y).d (n + 1) n).hom := by
    apply chainBilinearMap_ext X Y 2 (n + 1)
    intro σ τ
    have hstd := crossProductTriangle_boundary_affine 2 (n + 1) n
      (formalSimplex (stdVertices 2)) (formalSimplex (stdVertices (n + 1)))
    have hστ := congrArg (inducedChain (σ.prodMap τ) (n + 2)) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, inducedChain_boundary,
      crossProductTriangle_natural, crossProductEdge_natural,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Crossing a left boundary with a right cycle is the boundary of its triangle product. -/
theorem crossProductTriangle_boundary_of_right_cycle (n : ℕ)
    (a : Chains X 2) (b : Chains Y n)
    (hb : ((singularComplex Y).d n (n - 1)).hom b = 0) :
    ((singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductTriangle X Y n a b) =
      crossProductEdge X Y n (((singularComplex X).d 2 1).hom a) b := by
  cases n with
  | zero => exact crossProductTriangle_boundary_zero a b
  | succ n =>
      have hb' : ((singularComplex Y).d (n + 1) n).hom b = 0 := by
        simpa only [Nat.succ_sub_one] using hb
      simp only [crossProductTriangle_boundary, hb', map_zero, add_zero]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
