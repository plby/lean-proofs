import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalSupport

/-!
# The signed swap homotopy for two formal edges

The sum of the two edge products, after swapping the coordinates of the second,
is a cycle even when the input edges are not cycles.  Coning this sum gives an
explicit, natural three-chain whose boundary is the signed swap defect.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W Z V' W' : Type*}

/-- Composition of arbitrary vertex maps agrees with composition on formal chains. -/
theorem formalMap_comp (f : W → Z) (g : V → W) (n : ℕ) (c : FormalChains V n) :
    formalMap f n (formalMap g n c) = formalMap (f ∘ g) n c := by
  have h : (formalMap f n).comp (formalMap g n) = formalMap (f ∘ g) n := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalMap_simplex, Function.comp_assoc]
  exact LinearMap.congr_fun h c

/-- Coordinate swaps commute with maps on the two factors, in reversed order. -/
theorem formalMap_prod_swap (f : V → V') (g : W → W') (n : ℕ)
    (c : FormalChains (W × V) n) :
    formalMap (Prod.map f g) n (formalMap Prod.swap n c) =
      formalMap Prod.swap n (formalMap (Prod.map g f) n c) := by
  rw [formalMap_comp, formalMap_comp]
  rfl

/-- Swapping a point times an edge is the literal edge times point product. -/
theorem formalMap_swap_pointCrossProduct_one (c : FormalChains V 1)
    (d : FormalChains W 2) :
    formalMap Prod.swap 2 (formalPointCrossProduct 1 c d) =
      formalEdgeCrossProduct 0 d c := by
  have h : (formalPointCrossProduct (V := V) (W := W) 1).compr₂
        (formalMap Prod.swap 2) = (formalEdgeCrossProduct 0).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change formalMap Prod.swap 2
        (formalPointCrossProduct 1 (formalSimplex v) (formalSimplex w)) =
      formalEdgeCrossProduct 0 (formalSimplex w) (formalSimplex v)
    calc
      _ = formalMap Prod.swap 2
          (formalMap (fun z => (v 0, z)) 2 (formalSimplex w)) :=
        congrArg (formalMap Prod.swap 2)
          (formalPointCrossProduct_simplex_left 1 v (formalSimplex w))
      _ = formalMap (fun z => (z, v 0)) 2 (formalSimplex w) := by
        rw [formalMap_comp]
        rfl
      _ = _ := (formalEdgeCrossProduct_zero_simplex_right (formalSimplex w) v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Swapping an edge times a point is the literal point times edge product. -/
theorem formalMap_swap_edgeCrossProduct_zero (c : FormalChains V 2)
    (d : FormalChains W 1) :
    formalMap Prod.swap 2 (formalEdgeCrossProduct 0 c d) =
      formalPointCrossProduct 1 d c := by
  have h : (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
        (formalMap Prod.swap 2) = (formalPointCrossProduct 1).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change formalMap Prod.swap 2
        (formalEdgeCrossProduct 0 (formalSimplex v) (formalSimplex w)) =
      formalPointCrossProduct 1 (formalSimplex w) (formalSimplex v)
    calc
      _ = formalMap Prod.swap 2
          (formalMap (fun z => (z, w 0)) 2 (formalSimplex v)) :=
        congrArg (formalMap Prod.swap 2)
          (formalEdgeCrossProduct_zero_simplex_right (formalSimplex v) w)
      _ = formalMap (fun z => (w 0, z)) 2 (formalSimplex v) := by
        rw [formalMap_comp]
        rfl
      _ = _ := (formalPointCrossProduct_simplex_left 1 w (formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The signed failure of the two ordered edge products to agree under swapping. -/
def formalEdgeSwapDefect :
    FormalChains V 2 →ₗ[ℤ] FormalChains W 2 →ₗ[ℤ] FormalChains (V × W) 3 :=
  formalEdgeCrossProduct 1 +
    (formalEdgeCrossProduct 1).flip.compr₂ (formalMap Prod.swap 3)

@[simp] theorem formalEdgeSwapDefect_apply (c : FormalChains V 2)
    (d : FormalChains W 2) :
    formalEdgeSwapDefect c d = formalEdgeCrossProduct 1 c d +
      formalMap Prod.swap 3 (formalEdgeCrossProduct 1 d c) := rfl

/-- The signed swap defect is a cycle for arbitrary input edges. -/
theorem formalBoundary_edgeSwapDefect (c : FormalChains V 2)
    (d : FormalChains W 2) :
    formalBoundary 2 (formalEdgeSwapDefect c d) = 0 := by
  rw [formalEdgeSwapDefect_apply, map_add, formalBoundary_edgeCrossProduct,
    ← formalMap_boundary, formalBoundary_edgeCrossProduct, map_sub,
    formalMap_swap_pointCrossProduct_one, formalMap_swap_edgeCrossProduct_zero]
  abel

/-- The signed defect is natural in the vertex sets. -/
theorem formalMap_edgeSwapDefect (f : V → V') (g : W → W')
    (c : FormalChains V 2) (d : FormalChains W 2) :
    formalMap (Prod.map f g) 3 (formalEdgeSwapDefect c d) =
      formalEdgeSwapDefect (formalMap f 2 c) (formalMap g 2 d) := by
  rw [formalEdgeSwapDefect_apply, map_add, formalMap_edgeCrossProduct,
    formalMap_prod_swap, formalMap_edgeCrossProduct, formalEdgeSwapDefect_apply]

/-- An explicit three-chain filling the signed swap defect. -/
def formalEdgeSwapHomotopy :
    FormalChains V 2 →ₗ[ℤ] FormalChains W 2 →ₗ[ℤ] FormalChains (V × W) 4 :=
  formalBilinearLift fun v w =>
    formalCone (v 0, w 0) 3 (formalEdgeSwapDefect (formalSimplex v) (formalSimplex w))

@[simp] theorem formalEdgeSwapHomotopy_simplex (v : Fin 2 → V) (w : Fin 2 → W) :
    formalEdgeSwapHomotopy (formalSimplex v) (formalSimplex w) =
      formalCone (v 0, w 0) 3 (formalEdgeSwapDefect (formalSimplex v) (formalSimplex w)) :=
  formalBilinearLift_simplex _ _ _

/-- The cone construction realizes the signed swap relation as a boundary. -/
theorem formalEdgeSwapHomotopy_boundary (c : FormalChains V 2)
    (d : FormalChains W 2) :
    formalBoundary 3 (formalEdgeSwapHomotopy c d) = formalEdgeSwapDefect c d := by
  have h : (formalEdgeSwapHomotopy (V := V) (W := W)).compr₂ (formalBoundary 3) =
      formalEdgeSwapDefect := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, formalEdgeSwapHomotopy_simplex,
      formalBoundary_cone, formalBoundary_edgeSwapDefect, map_zero, sub_zero]
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The chosen swap homotopy is natural for arbitrary maps on both vertex sets. -/
theorem formalMap_edgeSwapHomotopy (f : V → V') (g : W → W')
    (c : FormalChains V 2) (d : FormalChains W 2) :
    formalMap (Prod.map f g) 4 (formalEdgeSwapHomotopy c d) =
      formalEdgeSwapHomotopy (formalMap f 2 c) (formalMap g 2 d) := by
  have h : (formalEdgeSwapHomotopy (V := V) (W := W)).compr₂
        (formalMap (Prod.map f g) 4) =
      ((formalEdgeSwapHomotopy).compl₂ (formalMap g 2)).comp (formalMap f 2) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      formalMap_simplex, formalEdgeSwapHomotopy_simplex]
    rw [formalMap_cone, formalMap_edgeSwapDefect, formalMap_simplex, formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The signed swap defect uses only vertices from the two input support sets. -/
theorem formalEdgeSwapDefect_mem_supported {S : Set V} {T : Set W}
    {c : FormalChains V 2} (hc : c ∈ formalChainsSupported S 2)
    {d : FormalChains W 2} (hd : d ∈ formalChainsSupported T 2) :
    formalEdgeSwapDefect c d ∈ formalChainsSupported (S ×ˢ T) 3 := by
  rw [formalEdgeSwapDefect_apply]
  apply Submodule.add_mem
  · exact formalEdgeCrossProduct_mem_supported 1 hc hd
  · exact formalMap_mem_supported (S := T ×ˢ S) (T := S ×ˢ T)
      Prod.swap (fun _ h => ⟨h.2, h.1⟩)
      (formalEdgeCrossProduct_mem_supported 1 hd hc)

/-- The swap homotopy preserves the product of the vertex support sets. -/
theorem formalEdgeSwapHomotopy_mem_supported {S : Set V} {T : Set W}
    {c : FormalChains V 2} (hc : c ∈ formalChainsSupported S 2)
    {d : FormalChains W 2} (hd : d ∈ formalChainsSupported T 2) :
    formalEdgeSwapHomotopy c d ∈ formalChainsSupported (S ×ˢ T) 4 := by
  apply formalLinearMap_mem_of_supported
    (formalEdgeSwapHomotopy.flip d) (formalChainsSupported (S ×ˢ T) 4) hc
  intro v hv
  apply formalLinearMap_mem_of_supported
    (formalEdgeSwapHomotopy (formalSimplex v)) (formalChainsSupported (S ×ˢ T) 4) hd
  intro w hw
  rw [formalEdgeSwapHomotopy_simplex]
  exact formalCone_mem_supported (S := S ×ˢ T) ⟨hv 0, hw 0⟩
    (formalEdgeSwapDefect_mem_supported (formalSimplex_mem_supported hv)
      (formalSimplex_mem_supported hw))

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
