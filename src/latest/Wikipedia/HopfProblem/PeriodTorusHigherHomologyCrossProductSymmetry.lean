import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBoundary
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalSwap

/-!
# A signed swap homotopy on actual singular chains

The formal cone filling the signed swap defect is realized in the product of
two standard intervals, then pushed forward by the two singular simplices.
Its boundary is the signed swap defect for arbitrary actual one-chains, not
only for cycles. All chain groups and differentials here are Mathlib's
integral singular chain groups and differentials.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Swapping coordinates commutes with affine interpolation of vertex pairs. -/
theorem prodSwap_productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → Simplex p × Simplex q) :
    (ContinuousMap.prodSwap : C(Simplex p × Simplex q, Simplex q × Simplex p)).comp
        (productAffineSimplex v) =
      productAffineSimplex (Prod.swap ∘ v) := rfl

/-- The literal swap of actual affine chains realizes the formal vertex swap. -/
theorem inducedChain_swap_productAffineChainMap (p q n : ℕ)
    (c : FormalChains (Simplex p × Simplex q) (n + 1)) :
    inducedChain (ContinuousMap.prodSwap : C(Simplex p × Simplex q, Simplex q × Simplex p)) n
        (productAffineChainMap p q n c) =
      productAffineChainMap q p n (formalMap Prod.swap (n + 1) c) := by
  have h : (inducedChain
        (ContinuousMap.prodSwap : C(Simplex p × Simplex q, Simplex q × Simplex p)) n).comp
        (productAffineChainMap p q n) =
      (productAffineChainMap q p n).comp (formalMap Prod.swap (n + 1)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex, inducedChain_simplex,
      formalMap_simplex, prodSwap_productAffineSimplex]
  exact LinearMap.congr_fun h c

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Product maps commute with the literal swap on actual singular chains. -/
theorem inducedChain_prodMap_swap (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (c : Chains (Y × X) n) :
    inducedChain (f.prodMap g) n (inducedChain ContinuousMap.prodSwap n c) =
      inducedChain ContinuousMap.prodSwap n (inducedChain (g.prodMap f) n c) := by
  calc
    _ = inducedChain ((f.prodMap g).comp ContinuousMap.prodSwap) n c :=
      (LinearMap.congr_fun (inducedChain_comp _ _ n) c).symm
    _ = inducedChain (ContinuousMap.prodSwap.comp (g.prodMap f)) n c := rfl
    _ = _ := LinearMap.congr_fun (inducedChain_comp _ _ n) c

/-- A natural actual three-chain filling the signed swap of two one-chains. -/
def crossProductSwapHomotopy (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Chains X 1 →ₗ[ℤ] Chains Y 1 →ₗ[ℤ] Chains (X × Y) 3 :=
  chainBilinearLift X Y 1 1 fun σ τ => inducedChain (σ.prodMap τ) 3
    (productAffineChainMap 1 1 3
      (formalEdgeSwapHomotopy (formalSimplex (stdVertices 1))
        (formalSimplex (stdVertices 1))))

@[simp] theorem crossProductSwapHomotopy_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (σ : SingularSimplex X 1) (τ : SingularSimplex Y 1) :
    crossProductSwapHomotopy X Y (simplexChain X 1 σ) (simplexChain Y 1 τ) =
      inducedChain (σ.prodMap τ) 3
        (productAffineChainMap 1 1 3
          (formalEdgeSwapHomotopy (formalSimplex (stdVertices 1))
            (formalSimplex (stdVertices 1)))) :=
  chainBilinearLift_simplex X Y 1 1 _ σ τ

/-- Naturality of the swap homotopy under arbitrary continuous maps. -/
theorem crossProductSwapHomotopy_natural (f : C(X, X')) (g : C(Y, Y'))
    (a : Chains X 1) (b : Chains Y 1) :
    inducedChain (f.prodMap g) 3 (crossProductSwapHomotopy X Y a b) =
      crossProductSwapHomotopy X' Y' (inducedChain f 1 a) (inducedChain g 1 b) := by
  have h : integerBilinearPostcompose (crossProductSwapHomotopy X Y)
        (inducedChain (f.prodMap g) 3) =
      integerBilinearPrecompose (crossProductSwapHomotopy X' Y')
        (inducedChain f 1) (inducedChain g 1) := by
    apply chainBilinearMap_ext X Y 1 1
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      inducedChain_simplex, crossProductSwapHomotopy_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Realization of the formal swap homotopy in arbitrary standard simplices. -/
theorem crossProductSwapHomotopy_affineChainMap (p q : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) 2) :
    crossProductSwapHomotopy (Simplex p) (Simplex q)
        (affineChainMap p 1 a) (affineChainMap q 1 b) =
      productAffineChainMap p q 3 (formalEdgeSwapHomotopy a b) := by
  have h : integerBilinearPrecompose (crossProductSwapHomotopy (Simplex p) (Simplex q))
        (affineChainMap p 1) (affineChainMap q 1) =
      integerBilinearPostcompose formalEdgeSwapHomotopy (productAffineChainMap p q 3) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      affineChainMap_simplex, crossProductSwapHomotopy_simplex]
    rw [inducedChain_productAffineChainMap]
    change productAffineChainMap p q 3
      (formalMap (Prod.map (affineSimplex v) (affineSimplex w)) 4
        (formalEdgeSwapHomotopy (formalSimplex (stdVertices 1))
          (formalSimplex (stdVertices 1)))) = _
    rw [formalMap_edgeSwapHomotopy, formalMap_simplex, formalMap_simplex,
      affineSimplex_stdVertices_image, affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The actual swap-boundary identity on realized formal chains. -/
theorem crossProductSwapHomotopy_boundary_affine (p q : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) 2) :
    ((singularComplex (Simplex p × Simplex q)).d 3 2).hom
        (crossProductSwapHomotopy (Simplex p) (Simplex q)
          (affineChainMap p 1 a) (affineChainMap q 1 b)) =
      crossProductEdge (Simplex p) (Simplex q) 1
          (affineChainMap p 1 a) (affineChainMap q 1 b) +
        inducedChain ContinuousMap.prodSwap 2
          (crossProductEdge (Simplex q) (Simplex p) 1
            (affineChainMap q 1 b) (affineChainMap p 1 a)) := by
  rw [crossProductSwapHomotopy_affineChainMap, productAffineChainMap_boundary,
    formalEdgeSwapHomotopy_boundary, formalEdgeSwapDefect_apply, map_add,
    crossProductEdge_affineChainMap, crossProductEdge_affineChainMap,
    inducedChain_swap_productAffineChainMap]

/-- The signed swap defect is a boundary for arbitrary actual one-chains. -/
theorem crossProductSwapHomotopy_boundary (a : Chains X 1) (b : Chains Y 1) :
    ((singularComplex (X × Y)).d 3 2).hom (crossProductSwapHomotopy X Y a b) =
      crossProductEdge X Y 1 a b +
        inducedChain ContinuousMap.prodSwap 2 (crossProductEdge Y X 1 b a) := by
  have h : integerBilinearPostcompose (crossProductSwapHomotopy X Y)
        ((singularComplex (X × Y)).d 3 2).hom =
      crossProductEdge X Y 1 +
        integerBilinearPostcompose (integerBilinearFlip (crossProductEdge Y X 1))
          (inducedChain ContinuousMap.prodSwap 2) := by
    apply chainBilinearMap_ext X Y 1 1
    intro σ τ
    have hstd := crossProductSwapHomotopy_boundary_affine 1 1
      (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices 1))
    have hστ := congrArg (inducedChain (σ.prodMap τ) 2) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearFlip_apply,
      LinearMap.add_apply, map_add, inducedChain_boundary,
      crossProductSwapHomotopy_natural, inducedChain_prodMap_swap, crossProductEdge_natural,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- A boundary witness for the signed swap relation, without any cycle hypothesis. -/
theorem crossProductEdge_swap_is_boundary (a : Chains X 1) (b : Chains Y 1) :
    ∃ c : Chains (X × Y) 3,
      ((singularComplex (X × Y)).d 3 2).hom c =
        crossProductEdge X Y 1 a b +
          inducedChain ContinuousMap.prodSwap 2 (crossProductEdge Y X 1 b a) :=
  ⟨crossProductSwapHomotopy X Y a b, crossProductSwapHomotopy_boundary a b⟩

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
