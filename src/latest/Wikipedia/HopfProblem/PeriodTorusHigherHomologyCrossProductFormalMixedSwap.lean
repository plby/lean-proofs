import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalSwap
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalTriangleSupport

/-!
# The mixed triangle-edge swap homotopy

For geometric degrees two and one the swap sign is positive.  The boundary of
the mixed swap defect is the already constructed edge-edge defect on the
triangle boundary.  Subtracting its explicit filling before coning therefore
gives a natural mixed swap homotopy, with no cycle hypotheses on its inputs.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W V' W' : Type*}

/-- Swapping a point times a triangle is the literal triangle times point product. -/
theorem formalMap_swap_pointCrossProduct_two (c : FormalChains V 1)
    (d : FormalChains W 3) :
    formalMap Prod.swap 3 (formalPointCrossProduct 2 c d) =
      formalTriangleCrossProduct 0 d c := by
  have heq : (formalPointCrossProduct (V := V) (W := W) 2).compr₂
        (formalMap Prod.swap 3) = (formalTriangleCrossProduct 0).flip := by
    apply formalChains_bilinear_ext
    intro v w
    change formalMap Prod.swap 3
        (formalPointCrossProduct 2 (formalSimplex v) (formalSimplex w)) =
      formalTriangleCrossProduct 0 (formalSimplex w) (formalSimplex v)
    calc
      _ = formalMap Prod.swap 3
          (formalMap (fun z => (v 0, z)) 3 (formalSimplex w)) :=
        congrArg (formalMap Prod.swap 3)
          (formalPointCrossProduct_simplex_left 2 v (formalSimplex w))
      _ = formalMap (fun z => (z, v 0)) 3 (formalSimplex w) := by
        rw [formalMap_comp]
        rfl
      _ = _ := (formalTriangleCrossProduct_zero_simplex_right (formalSimplex w) v).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

/-- The positively signed triangle-edge swap defect. -/
def formalMixedSwapDefect :
    FormalChains V 3 →ₗ[ℤ] FormalChains W 2 →ₗ[ℤ] FormalChains (V × W) 4 :=
  formalTriangleCrossProduct 1 -
    (formalEdgeCrossProduct 2).flip.compr₂ (formalMap Prod.swap 4)

@[simp] theorem formalMixedSwapDefect_apply (c : FormalChains V 3)
    (d : FormalChains W 2) :
    formalMixedSwapDefect c d = formalTriangleCrossProduct 1 c d -
      formalMap Prod.swap 4 (formalEdgeCrossProduct 2 d c) := rfl

/-- The mixed defect has the edge-edge swap defect as its only boundary term. -/
theorem formalBoundary_mixedSwapDefect (c : FormalChains V 3)
    (d : FormalChains W 2) :
    formalBoundary 3 (formalMixedSwapDefect c d) =
      formalEdgeSwapDefect (formalBoundary 2 c) d := by
  rw [formalMixedSwapDefect_apply, map_sub, formalBoundary_triangleCrossProduct,
    ← formalMap_boundary, formalBoundary_edgeCrossProduct, map_sub,
    formalMap_swap_pointCrossProduct_two, formalEdgeSwapDefect_apply]
  abel

/-- The mixed defect is natural for arbitrary maps of both vertex sets. -/
theorem formalMap_mixedSwapDefect (f : V → V') (g : W → W')
    (c : FormalChains V 3) (d : FormalChains W 2) :
    formalMap (Prod.map f g) 4 (formalMixedSwapDefect c d) =
      formalMixedSwapDefect (formalMap f 3 c) (formalMap g 2 d) := by
  rw [formalMixedSwapDefect_apply, map_sub, formalMap_triangleCrossProduct,
    formalMap_prod_swap, formalMap_edgeCrossProduct, formalMixedSwapDefect_apply]

/-- Fill the mixed defect after correcting by the edge-edge swap homotopy. -/
def formalMixedSwapHomotopy :
    FormalChains V 3 →ₗ[ℤ] FormalChains W 2 →ₗ[ℤ] FormalChains (V × W) 5 :=
  formalBilinearLift fun v w =>
    formalCone (v 0, w 0) 4
      (formalMixedSwapDefect (formalSimplex v) (formalSimplex w) -
        formalEdgeSwapHomotopy (formalBoundary 2 (formalSimplex v)) (formalSimplex w))

@[simp] theorem formalMixedSwapHomotopy_simplex (v : Fin 3 → V) (w : Fin 2 → W) :
    formalMixedSwapHomotopy (formalSimplex v) (formalSimplex w) =
      formalCone (v 0, w 0) 4
        (formalMixedSwapDefect (formalSimplex v) (formalSimplex w) -
          formalEdgeSwapHomotopy (formalBoundary 2 (formalSimplex v)) (formalSimplex w)) :=
  formalBilinearLift_simplex _ _ _

/-- The mixed swap homotopy identity for arbitrary triangle and edge chains. -/
theorem formalMixedSwapHomotopy_boundary (c : FormalChains V 3)
    (d : FormalChains W 2) :
    formalBoundary 4 (formalMixedSwapHomotopy c d) +
        formalEdgeSwapHomotopy (formalBoundary 2 c) d =
      formalMixedSwapDefect c d := by
  have heq : (formalMixedSwapHomotopy (V := V) (W := W)).compr₂
        (formalBoundary 4) +
      (formalEdgeSwapHomotopy).comp (formalBoundary 2) = formalMixedSwapDefect := by
    apply formalChains_bilinear_ext
    intro v w
    change formalBoundary 4
        (formalMixedSwapHomotopy (formalSimplex v) (formalSimplex w)) +
        formalEdgeSwapHomotopy (formalBoundary 2 (formalSimplex v)) (formalSimplex w) =
      formalMixedSwapDefect (formalSimplex v) (formalSimplex w)
    have hz : formalBoundary 3
        (formalMixedSwapDefect (formalSimplex v) (formalSimplex w) -
          formalEdgeSwapHomotopy (formalBoundary 2 (formalSimplex v)) (formalSimplex w)) = 0 := by
      rw [map_sub, formalBoundary_mixedSwapDefect, formalEdgeSwapHomotopy_boundary, sub_self]
    rw [formalMixedSwapHomotopy_simplex, formalBoundary_cone,
      hz, map_zero, sub_zero, sub_add_cancel]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

/-- If the triangle input is a cycle, the mixed swap defect is a boundary. -/
theorem formalMixedSwapHomotopy_boundary_of_cycle (c : FormalChains V 3)
    (hc : formalBoundary 2 c = 0) (d : FormalChains W 2) :
    formalBoundary 4 (formalMixedSwapHomotopy c d) = formalMixedSwapDefect c d := by
  simpa only [hc, map_zero, LinearMap.zero_apply, add_zero] using
    formalMixedSwapHomotopy_boundary c d

/-- The positive triangle-edge swap relation, with its filling chain exposed. -/
theorem formalCrossProduct_mixedSwap_boundary (c : FormalChains V 3)
    (hc : formalBoundary 2 c = 0) (d : FormalChains W 2) :
    formalTriangleCrossProduct 1 c d -
        formalMap Prod.swap 4 (formalEdgeCrossProduct 2 d c) =
      formalBoundary 4 (formalMixedSwapHomotopy c d) :=
  (formalMixedSwapHomotopy_boundary_of_cycle c hc d).symm

/-- The chosen mixed swap homotopy is natural for arbitrary vertex maps. -/
theorem formalMap_mixedSwapHomotopy (f : V → V') (g : W → W')
    (c : FormalChains V 3) (d : FormalChains W 2) :
    formalMap (Prod.map f g) 5 (formalMixedSwapHomotopy c d) =
      formalMixedSwapHomotopy (formalMap f 3 c) (formalMap g 2 d) := by
  have heq : (formalMixedSwapHomotopy (V := V) (W := W)).compr₂
        (formalMap (Prod.map f g) 5) =
      ((formalMixedSwapHomotopy).compl₂ (formalMap g 2)).comp (formalMap f 3) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      formalMap_simplex, formalMixedSwapHomotopy_simplex]
    rw [formalMap_cone]
    congr 1
    rw [map_sub, formalMap_mixedSwapDefect, formalMap_edgeSwapHomotopy,
      formalMap_boundary, formalMap_simplex, formalMap_simplex]
  exact LinearMap.congr_fun (LinearMap.congr_fun heq c) d

/-- The mixed swap defect preserves product vertex support. -/
theorem formalMixedSwapDefect_mem_supported {S : Set V} {T : Set W}
    {c : FormalChains V 3} (hc : c ∈ formalChainsSupported S 3)
    {d : FormalChains W 2} (hd : d ∈ formalChainsSupported T 2) :
    formalMixedSwapDefect c d ∈ formalChainsSupported (S ×ˢ T) 4 := by
  rw [formalMixedSwapDefect_apply]
  apply Submodule.sub_mem
  · exact formalTriangleCrossProduct_mem_supported 1 hc hd
  · exact formalMap_mem_supported (S := T ×ˢ S) (T := S ×ˢ T)
      Prod.swap (fun _ h => ⟨h.2, h.1⟩) (formalEdgeCrossProduct_mem_supported 2 hd hc)

/-- The mixed swap homotopy preserves product vertex support. -/
theorem formalMixedSwapHomotopy_mem_supported {S : Set V} {T : Set W}
    {c : FormalChains V 3} (hc : c ∈ formalChainsSupported S 3)
    {d : FormalChains W 2} (hd : d ∈ formalChainsSupported T 2) :
    formalMixedSwapHomotopy c d ∈ formalChainsSupported (S ×ˢ T) 5 := by
  apply formalLinearMap_mem_of_supported
    (formalMixedSwapHomotopy.flip d) (formalChainsSupported (S ×ˢ T) 5) hc
  intro v hv
  apply formalLinearMap_mem_of_supported
    (formalMixedSwapHomotopy (formalSimplex v)) (formalChainsSupported (S ×ˢ T) 5) hd
  intro w hw
  rw [formalMixedSwapHomotopy_simplex]
  apply formalCone_mem_supported (S := S ×ˢ T) ⟨hv 0, hw 0⟩
  apply Submodule.sub_mem
  · exact formalMixedSwapDefect_mem_supported
      (formalSimplex_mem_supported hv) (formalSimplex_mem_supported hw)
  · exact formalEdgeSwapHomotopy_mem_supported
      (formalBoundary_mem_supported 2 (formalSimplex_mem_supported hv))
      (formalSimplex_mem_supported hw)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
