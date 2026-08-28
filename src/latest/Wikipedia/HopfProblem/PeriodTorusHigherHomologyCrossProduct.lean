import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDegreeZero
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinearMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormal
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyAffineProduct

/-!
# Actual singular cross products with a one-chain

The universal formal edge product is realized in the product of standard
simplices and pushed forward by each pair of singular simplices. Thus the
result is an operation on Mathlib's actual singular chains, not a substitute
chain model. Its naturality and affine realization identities are proved here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Cross product of an actual singular one-chain with an actual singular `n`-chain. -/
def crossProductEdge (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Chains X 1 →ₗ[ℤ] Chains Y n →ₗ[ℤ] Chains (X × Y) (n + 1) :=
  chainBilinearLift X Y 1 n fun σ τ => inducedChain (σ.prodMap τ) (n + 1)
    (productAffineChainMap 1 n (n + 1)
      (formalEdgeCrossProduct n (formalSimplex (stdVertices 1))
        (formalSimplex (stdVertices n))))

@[simp] theorem crossProductEdge_simplex (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (σ : SingularSimplex X 1) (τ : SingularSimplex Y n) :
    crossProductEdge X Y n (simplexChain X 1 σ) (simplexChain Y n τ) =
      inducedChain (σ.prodMap τ) (n + 1)
        (productAffineChainMap 1 n (n + 1)
          (formalEdgeCrossProduct n (formalSimplex (stdVertices 1))
            (formalSimplex (stdVertices n)))) :=
  chainBilinearLift_simplex X Y 1 n _ σ τ

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Naturality of the actual edge cross product under arbitrary continuous maps. -/
theorem crossProductEdge_natural (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : Chains X 1) (b : Chains Y n) :
    inducedChain (f.prodMap g) (n + 1) (crossProductEdge X Y n a b) =
      crossProductEdge X' Y' n (inducedChain f 1 a) (inducedChain g n b) := by
  have h : integerBilinearPostcompose (crossProductEdge X Y n)
        (inducedChain (f.prodMap g) (n + 1)) =
      integerBilinearPrecompose (crossProductEdge X' Y' n)
        (inducedChain f 1) (inducedChain g n) := by
    apply chainBilinearMap_ext X Y 1 n
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      inducedChain_simplex, crossProductEdge_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Affine simplex maps send standard vertices to their defining vertices. -/
theorem affineSimplex_stdVertices_image {n p : ℕ} (v : Fin (n + 1) → Simplex p) :
    affineSimplex v ∘ stdVertices n = v := by
  funext i
  exact affineSimplex_vertex v i

/-- A product affine simplex with constant first coordinate is literal point insertion. -/
theorem productAffineSimplex_point_left {n p q : ℕ} (a : Simplex p)
    (v : Fin (n + 1) → Simplex q) :
    productAffineSimplex (fun i => (a, v i)) =
      (crossInsertLeft a).comp (affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
  rfl

/-- The analogous literal insertion in the right coordinate. -/
theorem productAffineSimplex_point_right {n p q : ℕ}
    (v : Fin (n + 1) → Simplex p) (b : Simplex q) :
    productAffineSimplex (fun i => (v i, b)) =
      (crossInsertRight b).comp (affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
  rfl

/-- The actual degree-zero product realizes the formal point product. -/
theorem crossProductZeroLeft_affineChainMap (p q n : ℕ)
    (a : FormalChains (Simplex p) 1) (b : FormalChains (Simplex q) (n + 1)) :
    crossProductZeroLeft (Simplex p) (Simplex q) n
        (affineChainMap p 0 a) (affineChainMap q n b) =
      productAffineChainMap p q n (formalPointCrossProduct n a b) := by
  have h : integerBilinearPrecompose (crossProductZeroLeft (Simplex p) (Simplex q) n)
        (affineChainMap p 0) (affineChainMap q n) =
      integerBilinearPostcompose (formalPointCrossProduct n) (productAffineChainMap p q n) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      affineChainMap_simplex, crossProductZeroLeft_simplex]
    have hv : zeroSimplexValue (affineSimplex v) = v 0 := affineSimplex_vertex v 0
    rw [hv]
    calc
      _ = productAffineChainMap p q n (formalSimplex (fun i => (v 0, w i))) := by
        rw [productAffineChainMap_simplex, productAffineSimplex_point_left]
      _ = _ := congrArg (productAffineChainMap p q n)
        (formalPointCrossProduct_simplex n v w).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The actual edge cross product realizes the formal edge product. -/
theorem crossProductEdge_affineChainMap (p q n : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) (n + 1)) :
    crossProductEdge (Simplex p) (Simplex q) n
        (affineChainMap p 1 a) (affineChainMap q n b) =
      productAffineChainMap p q (n + 1) (formalEdgeCrossProduct n a b) := by
  have h : integerBilinearPrecompose (crossProductEdge (Simplex p) (Simplex q) n)
        (affineChainMap p 1) (affineChainMap q n) =
      integerBilinearPostcompose (formalEdgeCrossProduct n)
        (productAffineChainMap p q (n + 1)) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      affineChainMap_simplex, crossProductEdge_simplex]
    rw [inducedChain_productAffineChainMap]
    change productAffineChainMap p q (n + 1)
      (formalMap (Prod.map (affineSimplex v) (affineSimplex w)) (n + 2)
        (formalEdgeCrossProduct n (formalSimplex (stdVertices 1))
          (formalSimplex (stdVertices n)))) = _
    rw [formalMap_edgeCrossProduct, formalMap_simplex, formalMap_simplex,
      affineSimplex_stdVertices_image, affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
