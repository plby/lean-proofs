import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductSymmetry
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductTriangle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalMixedSwap

/-!
# A mixed triangle-edge swap homotopy on actual singular chains

The formal mixed swap filling is realized in the product of a standard
triangle and a standard interval. Its boundary, corrected by the edge-edge
swap homotopy on the triangle boundary, is the positively signed mixed swap
defect. The identity holds for arbitrary actual chains; a cycle hypothesis
on the triangle input removes the correction term.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

/-- A natural four-chain homotopy swapping a triangle chain and an edge chain. -/
def crossProductMixedSwapHomotopy (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    Chains X 2 →ₗ[ℤ] Chains Y 1 →ₗ[ℤ] Chains (X × Y) 4 :=
  chainBilinearLift X Y 2 1 fun σ τ => inducedChain (σ.prodMap τ) 4
    (productAffineChainMap 2 1 4
      (formalMixedSwapHomotopy (formalSimplex (stdVertices 2))
        (formalSimplex (stdVertices 1))))

@[simp] theorem crossProductMixedSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (σ : SingularSimplex X 2) (τ : SingularSimplex Y 1) :
    crossProductMixedSwapHomotopy X Y (simplexChain X 2 σ) (simplexChain Y 1 τ) =
      inducedChain (σ.prodMap τ) 4
        (productAffineChainMap 2 1 4
          (formalMixedSwapHomotopy (formalSimplex (stdVertices 2))
            (formalSimplex (stdVertices 1)))) :=
  chainBilinearLift_simplex X Y 2 1 _ σ τ

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Naturality of the actual mixed swap homotopy under arbitrary continuous maps. -/
theorem crossProductMixedSwapHomotopy_natural (f : C(X, X')) (g : C(Y, Y'))
    (a : Chains X 2) (b : Chains Y 1) :
    inducedChain (f.prodMap g) 4 (crossProductMixedSwapHomotopy X Y a b) =
      crossProductMixedSwapHomotopy X' Y' (inducedChain f 2 a) (inducedChain g 1 b) := by
  have h : integerBilinearPostcompose (crossProductMixedSwapHomotopy X Y)
        (inducedChain (f.prodMap g) 4) =
      integerBilinearPrecompose (crossProductMixedSwapHomotopy X' Y')
        (inducedChain f 2) (inducedChain g 1) := by
    apply chainBilinearMap_ext X Y 2 1
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      inducedChain_simplex, crossProductMixedSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Affine realization intertwines the formal and actual mixed swap homotopies. -/
theorem crossProductMixedSwapHomotopy_affineChainMap (p q : ℕ)
    (a : FormalChains (Simplex p) 3) (b : FormalChains (Simplex q) 2) :
    crossProductMixedSwapHomotopy (Simplex p) (Simplex q)
        (affineChainMap p 2 a) (affineChainMap q 1 b) =
      productAffineChainMap p q 4 (formalMixedSwapHomotopy a b) := by
  have h : integerBilinearPrecompose (crossProductMixedSwapHomotopy (Simplex p) (Simplex q))
        (affineChainMap p 2) (affineChainMap q 1) =
      integerBilinearPostcompose formalMixedSwapHomotopy (productAffineChainMap p q 4) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      affineChainMap_simplex, crossProductMixedSwapHomotopy_simplex]
    rw [inducedChain_productAffineChainMap]
    change productAffineChainMap p q 4
      (formalMap (Prod.map (affineSimplex v) (affineSimplex w)) 5
        (formalMixedSwapHomotopy (formalSimplex (stdVertices 2))
          (formalSimplex (stdVertices 1)))) = _
    rw [formalMap_mixedSwapHomotopy, formalMap_simplex, formalMap_simplex,
      affineSimplex_stdVertices_image, affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The mixed swap-boundary identity on realized formal chains. -/
theorem crossProductMixedSwapHomotopy_boundary_affine (p q : ℕ)
    (a : FormalChains (Simplex p) 3) (b : FormalChains (Simplex q) 2) :
    ((singularComplex (Simplex p × Simplex q)).d 4 3).hom
        (crossProductMixedSwapHomotopy (Simplex p) (Simplex q)
          (affineChainMap p 2 a) (affineChainMap q 1 b)) +
      crossProductSwapHomotopy (Simplex p) (Simplex q)
        (((singularComplex (Simplex p)).d 2 1).hom (affineChainMap p 2 a))
        (affineChainMap q 1 b) =
      crossProductTriangle (Simplex p) (Simplex q) 1
          (affineChainMap p 2 a) (affineChainMap q 1 b) -
        inducedChain ContinuousMap.prodSwap 3
          (crossProductEdge (Simplex q) (Simplex p) 2
            (affineChainMap q 1 b) (affineChainMap p 2 a)) := by
  rw [crossProductMixedSwapHomotopy_affineChainMap, productAffineChainMap_boundary,
    affineChainMap_boundary, crossProductSwapHomotopy_affineChainMap,
    crossProductTriangle_affineChainMap, crossProductEdge_affineChainMap,
    inducedChain_swap_productAffineChainMap, ← map_add,
    formalMixedSwapHomotopy_boundary, formalMixedSwapDefect_apply, map_sub]

/-- The mixed swap homotopy identity for arbitrary actual triangle and edge chains. -/
theorem crossProductMixedSwapHomotopy_boundary (a : Chains X 2) (b : Chains Y 1) :
    ((singularComplex (X × Y)).d 4 3).hom (crossProductMixedSwapHomotopy X Y a b) +
      crossProductSwapHomotopy X Y (((singularComplex X).d 2 1).hom a) b =
      crossProductTriangle X Y 1 a b -
        inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) := by
  have h : integerBilinearPostcompose (crossProductMixedSwapHomotopy X Y)
          ((singularComplex (X × Y)).d 4 3).hom +
        integerBilinearPrecompose (crossProductSwapHomotopy X Y)
          ((singularComplex X).d 2 1).hom LinearMap.id =
      crossProductTriangle X Y 1 -
        integerBilinearPostcompose (integerBilinearFlip (crossProductEdge Y X 2))
          (inducedChain ContinuousMap.prodSwap 3) := by
    apply chainBilinearMap_ext X Y 2 1
    intro σ τ
    have hstd := crossProductMixedSwapHomotopy_boundary_affine 2 1
      (formalSimplex (stdVertices 2)) (formalSimplex (stdVertices 1))
    have hστ := congrArg (inducedChain (σ.prodMap τ) 3) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      integerBilinearFlip_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_add, map_sub, inducedChain_boundary, crossProductMixedSwapHomotopy_natural,
      crossProductSwapHomotopy_natural, inducedChain_prodMap_swap,
      crossProductTriangle_natural, crossProductEdge_natural,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- For a triangle cycle, the mixed swap defect is the boundary of the chosen homotopy. -/
theorem crossProductMixedSwapHomotopy_boundary_of_cycle (a : Chains X 2)
    (ha : ((singularComplex X).d 2 1).hom a = 0) (b : Chains Y 1) :
    ((singularComplex (X × Y)).d 4 3).hom (crossProductMixedSwapHomotopy X Y a b) =
      crossProductTriangle X Y 1 a b -
        inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) := by
  simpa only [ha, map_zero, LinearMap.zero_apply, add_zero] using
    crossProductMixedSwapHomotopy_boundary a b

/-- The positive mixed swap relation with its actual singular four-chain exposed. -/
theorem crossProductTriangle_swap_boundary (a : Chains X 2)
    (ha : ((singularComplex X).d 2 1).hom a = 0) (b : Chains Y 1) :
    crossProductTriangle X Y 1 a b -
        inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) =
      ((singularComplex (X × Y)).d 4 3).hom (crossProductMixedSwapHomotopy X Y a b) :=
  (crossProductMixedSwapHomotopy_boundary_of_cycle a ha b).symm

/-- A boundary witness for the positive swap of a triangle cycle with any edge chain. -/
theorem crossProductTriangle_swap_is_boundary (a : Chains X 2)
    (ha : ((singularComplex X).d 2 1).hom a = 0) (b : Chains Y 1) :
    ∃ c : Chains (X × Y) 4,
      ((singularComplex (X × Y)).d 4 3).hom c =
        crossProductTriangle X Y 1 a b -
          inducedChain ContinuousMap.prodSwap 3 (crossProductEdge Y X 2 b a) :=
  ⟨crossProductMixedSwapHomotopy X Y a b,
    crossProductMixedSwapHomotopy_boundary_of_cycle a ha b⟩

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
