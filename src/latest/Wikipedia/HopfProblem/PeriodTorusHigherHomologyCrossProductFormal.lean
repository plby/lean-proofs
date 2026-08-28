import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalHelpers
import Mathlib.LinearAlgebra.BilinearMap

/-!
# Ordered-chain products with points and edges

The point product is literal insertion of a fixed first coordinate.  The edge
product has the analogous literal right-unit formula.  In positive right
degree it is constructed by coning its prescribed signed product boundary to
the pair of first vertices.  The construction is on free integral ordered
chains, before any passage to singular chains or to homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W V' W' : Type*}

/-- Cross product of a formal zero-chain with an ordered chain. -/
def formalPointCrossProduct (q : ℕ) :
    FormalChains V 1 →ₗ[ℤ] FormalChains W (q + 1) →ₗ[ℤ]
      FormalChains (V × W) (q + 1) :=
  formalLift fun v => formalMap (fun w => (v 0, w)) (q + 1)

@[simp] theorem formalPointCrossProduct_simplex_left (q : ℕ) (v : Fin 1 → V)
    (d : FormalChains W (q + 1)) :
    formalPointCrossProduct q (formalSimplex v) d =
      formalMap (fun w => (v 0, w)) (q + 1) d := by
  exact LinearMap.congr_fun (formalLift_simplex _ _) d

@[simp] theorem formalPointCrossProduct_simplex (q : ℕ)
    (v : Fin 1 → V) (w : Fin (q + 1) → W) :
    formalPointCrossProduct q (formalSimplex v) (formalSimplex w) =
      formalSimplex (fun i => (v 0, w i)) := by
  rw [formalPointCrossProduct_simplex_left, formalMap_simplex]
  rfl

@[simp] theorem formalPointCrossProduct_zero_simplex_right
    (c : FormalChains V 1) (w : Fin 1 → W) :
    formalPointCrossProduct 0 c (formalSimplex w) =
      formalMap (fun v => (v, w 0)) 1 c := by
  have h : (formalPointCrossProduct (V := V) 0).flip (formalSimplex w) =
      formalMap (fun v => (v, w 0)) 1 := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.flip_apply, formalPointCrossProduct_simplex,
      formalMap_simplex]
    congr 1
    funext i
    rw [Fin.eq_zero i]
    rfl
  exact LinearMap.congr_fun h c

/-- The point product commutes with every positive-degree boundary. -/
theorem formalBoundary_pointCrossProduct (q : ℕ) (c : FormalChains V 1)
    (d : FormalChains W (q + 2)) :
    formalBoundary (q + 1) (formalPointCrossProduct (q + 1) c d) =
      formalPointCrossProduct q c (formalBoundary (q + 1) d) := by
  have h : (formalPointCrossProduct (V := V) (W := W) (q + 1)).compr₂
        (formalBoundary (q + 1)) =
      (formalPointCrossProduct q).compl₂ (formalBoundary (q + 1)) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      formalPointCrossProduct_simplex_left]
    exact (formalMap_boundary (fun z => (v 0, z)) (q + 1) (formalSimplex w)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Point products are natural for arbitrary maps on either set of vertices. -/
theorem formalMap_pointCrossProduct (f : V → V') (g : W → W') (q : ℕ)
    (c : FormalChains V 1) (d : FormalChains W (q + 1)) :
    formalMap (Prod.map f g) (q + 1) (formalPointCrossProduct q c d) =
      formalPointCrossProduct q (formalMap f 1 c) (formalMap g (q + 1) d) := by
  have h : (formalPointCrossProduct (V := V) (W := W) q).compr₂
        (formalMap (Prod.map f g) (q + 1)) =
      ((formalPointCrossProduct q).compl₂ (formalMap g (q + 1))).comp
        (formalMap f 1) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      LinearMap.comp_apply, formalPointCrossProduct_simplex, formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- Cross product with a formal edge, recursively filling the signed boundary. -/
def formalEdgeCrossProduct : (q : ℕ) →
    FormalChains V 2 →ₗ[ℤ] FormalChains W (q + 1) →ₗ[ℤ]
      FormalChains (V × W) (q + 2)
  | 0 => (formalLift fun w : Fin 1 → W =>
      formalMap (fun v => (v, w 0)) 2).flip
  | q + 1 => formalBilinearLift fun v w =>
      formalCone (v 0, w 0) (q + 2)
        (formalPointCrossProduct (q + 1) (formalBoundary 1 (formalSimplex v))
            (formalSimplex w) -
          formalEdgeCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (formalSimplex w)))

@[simp] theorem formalEdgeCrossProduct_zero_simplex_right
    (c : FormalChains V 2) (w : Fin 1 → W) :
    formalEdgeCrossProduct 0 c (formalSimplex w) =
      formalMap (fun v => (v, w 0)) 2 c := by
  exact LinearMap.congr_fun (formalLift_simplex _ _) c

@[simp] theorem formalEdgeCrossProduct_simplex_succ (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    formalEdgeCrossProduct (q + 1) (formalSimplex v) (formalSimplex w) =
      formalCone (v 0, w 0) (q + 2)
        (formalPointCrossProduct (q + 1) (formalBoundary 1 (formalSimplex v))
            (formalSimplex w) -
          formalEdgeCrossProduct q (formalSimplex v)
            (formalBoundary (q + 1) (formalSimplex w))) :=
  formalBilinearLift_simplex _ _ _

/-- The boundary of an edge times a zero-chain. -/
theorem formalBoundary_edgeCrossProduct_zero (c : FormalChains V 2)
    (d : FormalChains W 1) :
    formalBoundary 1 (formalEdgeCrossProduct 0 c d) =
      formalPointCrossProduct 0 (formalBoundary 1 c) d := by
  have h : (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
        (formalBoundary 1) =
      (formalPointCrossProduct 0).comp (formalBoundary 1) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      formalEdgeCrossProduct_zero_simplex_right,
      formalPointCrossProduct_zero_simplex_right]
    exact (formalMap_boundary (fun z => (z, w 0)) 1 (formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The signed edge-product boundary formula in every positive right degree. -/
theorem formalBoundary_edgeCrossProduct : ∀ (q : ℕ) (c : FormalChains V 2)
    (d : FormalChains W (q + 2)),
    formalBoundary (q + 2) (formalEdgeCrossProduct (q + 1) c d) =
      formalPointCrossProduct (q + 1) (formalBoundary 1 c) d -
        formalEdgeCrossProduct q c (formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
      intro c d
      have h : (formalEdgeCrossProduct (V := V) (W := W) 1).compr₂
            (formalBoundary 2) =
          (formalPointCrossProduct 1).comp (formalBoundary 1) -
            (formalEdgeCrossProduct 0).compl₂ (formalBoundary 1) := by
        apply formalChains_bilinear_ext
        intro v w
        change formalBoundary 2
            (formalEdgeCrossProduct 1 (formalSimplex v) (formalSimplex w)) = _
        rw [formalEdgeCrossProduct_simplex_succ, formalBoundary_cone]
        have hz : formalBoundary 1
            (formalPointCrossProduct 1 (formalBoundary 1 (formalSimplex v))
                (formalSimplex w) -
              formalEdgeCrossProduct 0 (formalSimplex v)
                (formalBoundary 1 (formalSimplex w))) = 0 := by
          rw [map_sub, formalBoundary_pointCrossProduct,
            formalBoundary_edgeCrossProduct_zero, sub_self]
        rw [hz, map_zero, sub_zero]
        rfl
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
      intro c d
      have h : (formalEdgeCrossProduct (V := V) (W := W) (q + 2)).compr₂
            (formalBoundary (q + 3)) =
          (formalPointCrossProduct (q + 2)).comp (formalBoundary 1) -
            (formalEdgeCrossProduct (q + 1)).compl₂ (formalBoundary (q + 2)) := by
        apply formalChains_bilinear_ext
        intro v w
        change formalBoundary (q + 3)
            (formalEdgeCrossProduct (q + 2) (formalSimplex v) (formalSimplex w)) = _
        rw [formalEdgeCrossProduct_simplex_succ, formalBoundary_cone]
        have hz : formalBoundary (q + 2)
            (formalPointCrossProduct (q + 2) (formalBoundary 1 (formalSimplex v))
                (formalSimplex w) -
              formalEdgeCrossProduct (q + 1) (formalSimplex v)
                (formalBoundary (q + 2) (formalSimplex w))) = 0 := by
          rw [map_sub, formalBoundary_pointCrossProduct, ih,
            formalBoundary_boundary, map_zero, sub_zero, sub_self]
        rw [hz, map_zero, sub_zero]
        rfl
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The edge product is natural for arbitrary maps on the vertex sets. -/
theorem formalMap_edgeCrossProduct (f : V → V') (g : W → W') :
    ∀ (q : ℕ) (c : FormalChains V 2) (d : FormalChains W (q + 1)),
    formalMap (Prod.map f g) (q + 2) (formalEdgeCrossProduct q c d) =
      formalEdgeCrossProduct q (formalMap f 2 c) (formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
      intro c d
      have h : (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
            (formalMap (Prod.map f g) 2) =
          ((formalEdgeCrossProduct 0).compl₂ (formalMap g 1)).comp (formalMap f 2) := by
        apply formalChains_bilinear_ext
        intro v w
        simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
          LinearMap.comp_apply, formalEdgeCrossProduct_zero_simplex_right,
          formalMap_simplex]
        rfl
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
      intro c d
      have h : (formalEdgeCrossProduct (V := V) (W := W) (q + 1)).compr₂
            (formalMap (Prod.map f g) (q + 3)) =
          ((formalEdgeCrossProduct (q + 1)).compl₂ (formalMap g (q + 2))).comp
            (formalMap f 2) := by
        apply formalChains_bilinear_ext
        intro v w
        simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
          LinearMap.comp_apply, formalMap_simplex, formalEdgeCrossProduct_simplex_succ]
        rw [formalMap_cone]
        congr 1
        rw [map_sub, formalMap_pointCrossProduct, ih,
          formalMap_boundary, formalMap_boundary, formalMap_simplex, formalMap_simplex]
      exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
