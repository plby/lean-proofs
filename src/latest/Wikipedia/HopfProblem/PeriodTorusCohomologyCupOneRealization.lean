import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneAffine
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalBasic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryaginMaps

/-!
# Actual chain realization of the integral period products

The integer-affine simplices evaluate ordered formal chains in the native
singular chain complex. The realization commutes with the differential and
with the edge cross product followed by addition. The latter comparison uses
the same universal formal prism that defines the actual singular cross product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology
open PeriodTorusHigherHomologyPontryagin

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Evaluation of integral-vertex formal chains in the actual torus complex.
Formal degree counts vertices; singular degree counts dimension. -/
def affineTorusChain (n k : ℕ) :
    FormalChains (Fin n → ℤ) (k + 1) →ₗ[ℤ] Chains (ProductTorus n) k :=
  formalLift fun v => simplexChain (ProductTorus n) k (affineTorusSimplex v)

@[simp] theorem affineTorusChain_simplex (n k : ℕ)
    (v : Fin (k + 1) → Fin n → ℤ) :
    affineTorusChain n k (formalSimplex v) =
      simplexChain (ProductTorus n) k (affineTorusSimplex v) :=
  formalLift_simplex _ _

/-- Literal formal face deletion realizes as the native singular differential. -/
theorem affineTorusChain_boundary (n k : ℕ)
    (c : FormalChains (Fin n → ℤ) (k + 2)) :
    ((singularComplex (ProductTorus n)).d (k + 1) k).hom
        (affineTorusChain n (k + 1) c) =
      affineTorusChain n k (formalBoundary (k + 1) c) := by
  have h : (((singularComplex (ProductTorus n)).d (k + 1) k).hom).comp
      (affineTorusChain n (k + 1)) =
        (affineTorusChain n k).comp (formalBoundary (k + 1)) := by
    apply formalChains_ext
    intro v
    change ((singularComplex (ProductTorus n)).d (k + 1) k).hom
      (affineTorusChain n (k + 1) (formalSimplex v)) = _
    rw [affineTorusChain_simplex, boundary_simplex]
    change _ = affineTorusChain n k (formalBoundary (k + 1) (formalSimplex v))
    rw [formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, affineTorusChain_simplex, affineTorusSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

/-- Affine interpolation of selected standard vertices is precisely the native
map of standard simplices, even when vertices are repeated. -/
theorem affineSimplex_selectedStdVertices {k p : ℕ}
    (f : Fin (k + 1) → Fin (p + 1)) :
    affineSimplex (stdVertices p ∘ f) =
      (⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ : C(Simplex k, Simplex p)) := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  funext j
  change affineSimplex (stdVertices p ∘ f) t j = stdSimplex.map f t j
  rw [affineSimplex_coordinate]
  change (∑ i, t i * stdVertices p (f i) j) =
    FunOnFinite.linearMap ℝ ℝ f (t : Fin (k + 1) → ℝ) j
  simp [stdVertices, Pi.single_apply, FunOnFinite.linearMap_apply_apply,
    Finset.sum_filter, eq_comm]

/-- Barycentric interpolation and native coordinate reduction preserve addition
of the integral vertex tuples. -/
theorem affineTorusSimplex_add {n k : ℕ}
    (v w : Fin (k + 1) → Fin n → ℤ) (t : Simplex k) :
    affineTorusSimplex (fun i => v i + w i) t =
      affineTorusSimplex v t + affineTorusSimplex w t := by
  funext j
  simp only [affineTorusSimplex_coordinate, Pi.add_apply, Int.cast_add,
    mul_add, Finset.sum_add_distrib, AddCircle.coe_add]

/-- Each simplex of the native product prism, followed by torus addition, is
the integer-affine simplex on the corresponding sums of vertices. -/
theorem affineTorusSimplex_standardProduct {n p q k : ℕ}
    (v : Fin (p + 1) → Fin n → ℤ) (w : Fin (q + 1) → Fin n → ℤ)
    (z : Fin (k + 1) → Fin (p + 1) × Fin (q + 1)) :
    (additionMap (ProductTorus n)).comp
        (((affineTorusSimplex v).prodMap (affineTorusSimplex w)).comp
          (productAffineSimplex (Prod.map (stdVertices p) (stdVertices q) ∘ z))) =
      affineTorusSimplex (fun i => v (z i).1 + w (z i).2) := by
  apply ContinuousMap.ext
  intro t
  change affineTorusSimplex v (affineSimplex (stdVertices p ∘ (Prod.fst ∘ z)) t) +
      affineTorusSimplex w (affineSimplex (stdVertices q ∘ (Prod.snd ∘ z)) t) = _
  rw [affineSimplex_selectedStdVertices, affineSimplex_selectedStdVertices]
  change affineTorusSimplex v (stdSimplex.map (Prod.fst ∘ z) t) +
    affineTorusSimplex w (stdSimplex.map (Prod.snd ∘ z) t) = _
  rw [affineTorusSimplex_map, affineTorusSimplex_map]
  exact (affineTorusSimplex_add (v ∘ (Prod.fst ∘ z)) (w ∘ (Prod.snd ∘ z)) t).symm

/-- Comparison on arbitrary formal chains of pairs of vertex indices. -/
theorem affineTorusChain_indexProduct (n p q k : ℕ)
    (v : Fin (p + 1) → Fin n → ℤ) (w : Fin (q + 1) → Fin n → ℤ)
    (c : FormalChains (Fin (p + 1) × Fin (q + 1)) (k + 1)) :
    affineTorusChain n k
        (formalMap (fun x : (Fin n → ℤ) × (Fin n → ℤ) => x.1 + x.2) (k + 1)
          (formalMap (Prod.map v w) (k + 1) c)) =
      inducedChain (additionMap (ProductTorus n)) k
        (inducedChain ((affineTorusSimplex v).prodMap (affineTorusSimplex w)) k
          (productAffineChainMap p q k
            (formalMap (Prod.map (stdVertices p) (stdVertices q)) (k + 1) c))) := by
  have h : (affineTorusChain n k).comp
      ((formalMap (fun x : (Fin n → ℤ) × (Fin n → ℤ) => x.1 + x.2) (k + 1)).comp
        (formalMap (Prod.map v w) (k + 1))) =
      (inducedChain (additionMap (ProductTorus n)) k).comp
        ((inducedChain ((affineTorusSimplex v).prodMap (affineTorusSimplex w)) k).comp
          ((productAffineChainMap p q k).comp
            (formalMap (Prod.map (stdVertices p) (stdVertices q)) (k + 1)))) := by
    apply formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, formalMap_simplex, affineTorusChain_simplex,
      productAffineChainMap_simplex, inducedChain_simplex]
    rw [affineTorusSimplex_standardProduct]
    rfl
  exact LinearMap.congr_fun h c

/-- On simplex generators, formal and actual edge products use the same
universal chain on the pairs of standard vertex indices. -/
theorem affineTorusChain_edgeCrossProduct_simplex (n q : ℕ)
    (v : Fin 2 → Fin n → ℤ) (w : Fin (q + 1) → Fin n → ℤ) :
    affineTorusChain n (q + 1)
        (formalMap (fun x : (Fin n → ℤ) × (Fin n → ℤ) => x.1 + x.2) (q + 2)
          (formalEdgeCrossProduct q (formalSimplex v) (formalSimplex w))) =
      inducedChain (additionMap (ProductTorus n)) (q + 1)
        (crossProductEdge (ProductTorus n) (ProductTorus n) q
          (simplexChain (ProductTorus n) 1 (affineTorusSimplex v))
          (simplexChain (ProductTorus n) q (affineTorusSimplex w))) := by
  let c : FormalChains (Fin 2 × Fin (q + 1)) (q + 2) :=
    formalEdgeCrossProduct q (formalSimplex (id : Fin 2 → Fin 2))
      (formalSimplex (id : Fin (q + 1) → Fin (q + 1)))
  have hvw : formalMap (Prod.map v w) (q + 2) c =
      formalEdgeCrossProduct q (formalSimplex v) (formalSimplex w) := by
    dsimp [c]
    rw [formalMap_edgeCrossProduct]
    simp only [formalMap_simplex, Function.comp_id]
  have hstd : formalMap (Prod.map (stdVertices 1) (stdVertices q)) (q + 2) c =
      formalEdgeCrossProduct q (formalSimplex (stdVertices 1))
        (formalSimplex (stdVertices q)) := by
    dsimp [c]
    rw [formalMap_edgeCrossProduct]
    simp only [formalMap_simplex, Function.comp_id]
  rw [← hvw, affineTorusChain_indexProduct, hstd, crossProductEdge_simplex]

/-- The actual chain realization of the formal edge product followed by
addition is the native singular edge cross product followed by addition. -/
theorem affineTorusChain_edgeCrossProduct (n q : ℕ)
    (a : FormalChains (Fin n → ℤ) 2) (b : FormalChains (Fin n → ℤ) (q + 1)) :
    affineTorusChain n (q + 1)
        (formalMap (fun x : (Fin n → ℤ) × (Fin n → ℤ) => x.1 + x.2) (q + 2)
          (formalEdgeCrossProduct q a b)) =
      inducedChain (additionMap (ProductTorus n)) (q + 1)
        (crossProductEdge (ProductTorus n) (ProductTorus n) q
          (affineTorusChain n 1 a) (affineTorusChain n q b)) := by
  have h : integerBilinearPostcompose (formalEdgeCrossProduct q)
        ((affineTorusChain n (q + 1)).comp
          (formalMap (fun x : (Fin n → ℤ) × (Fin n → ℤ) => x.1 + x.2) (q + 2))) =
      integerBilinearPrecompose
        (integerBilinearPostcompose (crossProductEdge (ProductTorus n) (ProductTorus n) q)
          (inducedChain (additionMap (ProductTorus n)) (q + 1)))
        (affineTorusChain n 1) (affineTorusChain n q) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.comp_apply, affineTorusChain_simplex]
    exact affineTorusChain_edgeCrossProduct_simplex n q v w
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Compatibility with the exact formal period product used in the cup calculation. -/
theorem affineTorusChain_formalPeriodProduct (q : ℕ)
    (a : FormalChains Lattice 2) (b : FormalChains Lattice (q + 1)) :
    affineTorusChain 4 (q + 1) (formalPeriodProduct q a b) =
      inducedChain (additionMap (ProductTorus 4)) (q + 1)
        (crossProductEdge (ProductTorus 4) (ProductTorus 4) q
          (affineTorusChain 4 1 a) (affineTorusChain 4 q b)) :=
  affineTorusChain_edgeCrossProduct 4 q a b

/-- An integral edge beginning at zero realizes the marked positive period loop. -/
theorem affineTorusChain_periodEdge (n : ℕ) (x : Fin n → ℤ) :
    affineTorusChain n 1 (formalSimplex ![0, x]) = pathChain (coordinatePeriodLoop n x) := by
  rw [affineTorusChain_simplex, affineTorusSimplex_one]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_zero]
  rfl

/-- The original formal period edge realizes the actual marked path chain. -/
theorem affineTorusChain_formalPeriodEdge (x : Lattice) :
    affineTorusChain 4 1 (formalPeriodEdge x) = pathChain (coordinatePeriodLoop 4 x) :=
  affineTorusChain_periodEdge 4 x

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
