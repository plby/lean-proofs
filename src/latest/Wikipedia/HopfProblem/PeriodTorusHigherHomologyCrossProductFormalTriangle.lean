import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormal

/-!
# Ordered-chain products with triangles

The triangle product supplies the next signed boundary relation after the edge
product.  It is linear in both inputs, natural in both vertex sets, and has the
literal right-unit formula.  The sign on the second boundary term is positive,
because the first geometric degree is two.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W V' W' : Type*}

/-- Cross product with a formal triangle, filling its complete signed boundary. -/
def formalTriangleCrossProduct : (q : ℕ) →
    FormalChains V 3 →ₗ[ℤ] FormalChains W (q + 1) →ₗ[ℤ]
      FormalChains (V × W) (q + 3)
  | 0 => (formalLift fun w : Fin 1 → W =>
      formalMap (fun v => (v, w 0)) 3).flip
  | q + 1 => formalBilinearLift fun v w =>
      formalCone (v 0, w 0) (q + 3)
        (formalEdgeCrossProduct (q + 1) (formalBoundary 2 (formalSimplex v))
            (formalSimplex w) +
          formalTriangleCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (formalSimplex w)))

@[simp] theorem formalTriangleCrossProduct_zero_simplex_right
    (c : FormalChains V 3) (w : Fin 1 → W) :
    formalTriangleCrossProduct 0 c (formalSimplex w) =
      formalMap (fun v => (v, w 0)) 3 c := by
  exact LinearMap.congr_fun (formalLift_simplex _ _) c

@[simp] theorem formalTriangleCrossProduct_simplex_succ (q : ℕ)
    (v : Fin 3 → V) (w : Fin (q + 2) → W) :
    formalTriangleCrossProduct (q + 1) (formalSimplex v) (formalSimplex w) =
      formalCone (v 0, w 0) (q + 3)
        (formalEdgeCrossProduct (q + 1) (formalBoundary 2 (formalSimplex v))
            (formalSimplex w) +
          formalTriangleCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (formalSimplex w))) :=
  formalBilinearLift_simplex _ _ _

/-- Boundary formula when the right factor has geometric degree zero. -/
theorem formalBoundary_triangleCrossProduct_zero (c : FormalChains V 3)
    (d : FormalChains W 1) :
    formalBoundary 2 (formalTriangleCrossProduct 0 c d) =
      formalEdgeCrossProduct 0 (formalBoundary 2 c) d := by
  have h : (formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
        (formalBoundary 2) =
      (formalEdgeCrossProduct 0).comp (formalBoundary 2) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      formalTriangleCrossProduct_zero_simplex_right,
      formalEdgeCrossProduct_zero_simplex_right]
    exact (formalMap_boundary (fun z => (z, w 0)) 2 (formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The triangle-product boundary formula has the sign `(-1)^2 = 1`. -/
theorem formalBoundary_triangleCrossProduct : ∀ (q : ℕ) (c : FormalChains V 3)
    (d : FormalChains W (q + 2)),
    formalBoundary (q + 3) (formalTriangleCrossProduct (q + 1) c d) =
      formalEdgeCrossProduct (q + 1) (formalBoundary 2 c) d +
        formalTriangleCrossProduct q c (formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
      intro c d
      have h : (formalTriangleCrossProduct (V := V) (W := W) 1).compr₂
            (formalBoundary 3) =
          (formalEdgeCrossProduct 1).comp (formalBoundary 2) +
            (formalTriangleCrossProduct 0).compl₂ (formalBoundary 1) := by
        apply formalChains_bilinear_ext
        intro v w
        change formalBoundary 3
            (formalTriangleCrossProduct 1 (formalSimplex v) (formalSimplex w)) = _
        rw [formalTriangleCrossProduct_simplex_succ, formalBoundary_cone]
        have hz : formalBoundary 2
            (formalEdgeCrossProduct 1 (formalBoundary 2 (formalSimplex v))
                (formalSimplex w) +
              formalTriangleCrossProduct 0 (formalSimplex v)
                (formalBoundary 1 (formalSimplex w))) = 0 := by
          rw [map_add, formalBoundary_edgeCrossProduct,
            formalBoundary_boundary, map_zero, LinearMap.zero_apply, zero_sub,
            formalBoundary_triangleCrossProduct_zero, neg_add_cancel]
        rw [hz, map_zero, sub_zero]
        rfl
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
      intro c d
      have h : (formalTriangleCrossProduct (V := V) (W := W) (q + 2)).compr₂
            (formalBoundary (q + 4)) =
          (formalEdgeCrossProduct (q + 2)).comp (formalBoundary 2) +
            (formalTriangleCrossProduct (q + 1)).compl₂ (formalBoundary (q + 2)) := by
        apply formalChains_bilinear_ext
        intro v w
        change formalBoundary (q + 4)
            (formalTriangleCrossProduct (q + 2) (formalSimplex v) (formalSimplex w)) = _
        rw [formalTriangleCrossProduct_simplex_succ, formalBoundary_cone]
        have hz : formalBoundary (q + 3)
            (formalEdgeCrossProduct (q + 2) (formalBoundary 2 (formalSimplex v))
                (formalSimplex w) +
              formalTriangleCrossProduct (q + 1) (formalSimplex v)
                (formalBoundary (q + 2) (formalSimplex w))) = 0 := by
          rw [map_add, formalBoundary_edgeCrossProduct,
            formalBoundary_boundary, map_zero, LinearMap.zero_apply, zero_sub,
            ih, formalBoundary_boundary, map_zero, add_zero, neg_add_cancel]
        rw [hz, map_zero, sub_zero]
        rfl
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Triangle products are natural for arbitrary maps of either vertex set. -/
theorem formalMap_triangleCrossProduct (f : V → V') (g : W → W') :
    ∀ (q : ℕ) (c : FormalChains V 3) (d : FormalChains W (q + 1)),
    formalMap (Prod.map f g) (q + 3) (formalTriangleCrossProduct q c d) =
      formalTriangleCrossProduct q (formalMap f 3 c) (formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
      intro c d
      have h : (formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
            (formalMap (Prod.map f g) 3) =
          ((formalTriangleCrossProduct 0).compl₂ (formalMap g 1)).comp (formalMap f 3) := by
        apply formalChains_bilinear_ext
        intro v w
        simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
          LinearMap.comp_apply, formalTriangleCrossProduct_zero_simplex_right,
          formalMap_simplex]
        rfl
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
      intro c d
      have h : (formalTriangleCrossProduct (V := V) (W := W) (q + 1)).compr₂
            (formalMap (Prod.map f g) (q + 4)) =
          ((formalTriangleCrossProduct (q + 1)).compl₂ (formalMap g (q + 2))).comp
            (formalMap f 3) := by
        apply formalChains_bilinear_ext
        intro v w
        simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
          LinearMap.comp_apply, formalMap_simplex, formalTriangleCrossProduct_simplex_succ]
        rw [formalMap_cone]
        congr 1
        rw [map_add, formalMap_edgeCrossProduct, ih,
          formalMap_boundary, formalMap_boundary, formalMap_simplex, formalMap_simplex]
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- An edge boundary times a zero-chain is the boundary of its triangle product. -/
theorem formalEdgeCrossProduct_boundary_left_zero (c : FormalChains V 3)
    (d : FormalChains W 1) :
    formalEdgeCrossProduct 0 (formalBoundary 2 c) d =
      formalBoundary 2 (formalTriangleCrossProduct 0 c d) :=
  (formalBoundary_triangleCrossProduct_zero c d).symm

/-- An edge boundary times a positive-degree cycle is a boundary. -/
theorem formalEdgeCrossProduct_boundary_left (q : ℕ) (c : FormalChains V 3)
    (d : FormalChains W (q + 2)) (hd : formalBoundary (q + 1) d = 0) :
    formalEdgeCrossProduct (q + 1) (formalBoundary 2 c) d =
      formalBoundary (q + 3) (formalTriangleCrossProduct (q + 1) c d) := by
  rw [formalBoundary_triangleCrossProduct, hd, map_zero, add_zero]

/-- A triangle cycle times a positive-degree cycle is a cycle. -/
theorem formalTriangleCrossProduct_isCycle (q : ℕ) (c : FormalChains V 3)
    (hc : formalBoundary 2 c = 0) (d : FormalChains W (q + 2))
    (hd : formalBoundary (q + 1) d = 0) :
    formalBoundary (q + 3) (formalTriangleCrossProduct (q + 1) c d) = 0 := by
  rw [formalBoundary_triangleCrossProduct, hc, map_zero, LinearMap.zero_apply,
    hd, map_zero, add_zero]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
