import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProduct

/-!
# Boundary formulas for actual singular edge cross products

The formulas are proved first on realized formal affine chains and then on
arbitrary singular simplices by naturality. They give the usual Leibniz sign
for a left factor of degree one, including the separate degree-zero endpoint.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The degree-zero boundary formula on realized formal chains. -/
theorem crossProductEdge_boundary_zero_affine (p q : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) 1) :
    ((singularComplex (Simplex p × Simplex q)).d 1 0).hom
        (crossProductEdge (Simplex p) (Simplex q) 0
          (affineChainMap p 1 a) (affineChainMap q 0 b)) =
      crossProductZeroLeft (Simplex p) (Simplex q) 0
        (((singularComplex (Simplex p)).d 1 0).hom (affineChainMap p 1 a))
        (affineChainMap q 0 b) := by
  rw [crossProductEdge_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_edgeCrossProduct_zero, affineChainMap_boundary,
    crossProductZeroLeft_affineChainMap]

/-- The signed product-boundary formula on realized formal chains. -/
theorem crossProductEdge_boundary_affine (p q n : ℕ)
    (a : FormalChains (Simplex p) 2) (b : FormalChains (Simplex q) (n + 2)) :
    ((singularComplex (Simplex p × Simplex q)).d (n + 2) (n + 1)).hom
        (crossProductEdge (Simplex p) (Simplex q) (n + 1)
          (affineChainMap p 1 a) (affineChainMap q (n + 1) b)) =
      crossProductZeroLeft (Simplex p) (Simplex q) (n + 1)
          (((singularComplex (Simplex p)).d 1 0).hom (affineChainMap p 1 a))
          (affineChainMap q (n + 1) b) -
        crossProductEdge (Simplex p) (Simplex q) n (affineChainMap p 1 a)
          (((singularComplex (Simplex q)).d (n + 1) n).hom (affineChainMap q (n + 1) b)) := by
  rw [crossProductEdge_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_edgeCrossProduct, map_sub, affineChainMap_boundary,
    affineChainMap_boundary, crossProductZeroLeft_affineChainMap,
    crossProductEdge_affineChainMap]

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The boundary of an actual one-chain crossed with a zero-chain. -/
theorem crossProductEdge_boundary_zero (a : Chains X 1) (b : Chains Y 0) :
    ((singularComplex (X × Y)).d 1 0).hom (crossProductEdge X Y 0 a b) =
      crossProductZeroLeft X Y 0 (((singularComplex X).d 1 0).hom a) b := by
  have h : integerBilinearPostcompose (crossProductEdge X Y 0)
        ((singularComplex (X × Y)).d 1 0).hom =
      integerBilinearPrecompose (crossProductZeroLeft X Y 0)
        ((singularComplex X).d 1 0).hom LinearMap.id := by
    apply chainBilinearMap_ext X Y 1 0
    intro σ τ
    have hstd := crossProductEdge_boundary_zero_affine 1 0
      (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices 0))
    have hστ := congrArg (inducedChain (σ.prodMap τ) 0) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.id_apply, inducedChain_boundary, crossProductEdge_natural,
      crossProductZeroLeft_natural, affineChainMap_stdVertices, inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- The actual singular-chain Leibniz rule with a degree-one left factor. -/
theorem crossProductEdge_boundary (n : ℕ) (a : Chains X 1) (b : Chains Y (n + 1)) :
    ((singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductEdge X Y (n + 1) a b) =
      crossProductZeroLeft X Y (n + 1) (((singularComplex X).d 1 0).hom a) b -
        crossProductEdge X Y n a (((singularComplex Y).d (n + 1) n).hom b) := by
  have h : integerBilinearPostcompose (crossProductEdge X Y (n + 1))
        ((singularComplex (X × Y)).d (n + 2) (n + 1)).hom =
      integerBilinearPrecompose (crossProductZeroLeft X Y (n + 1))
          ((singularComplex X).d 1 0).hom LinearMap.id -
        integerBilinearPrecompose (crossProductEdge X Y n) LinearMap.id
          ((singularComplex Y).d (n + 1) n).hom := by
    apply chainBilinearMap_ext X Y 1 (n + 1)
    intro σ τ
    have hstd := crossProductEdge_boundary_affine 1 (n + 1) n
      (formalSimplex (stdVertices 1)) (formalSimplex (stdVertices (n + 1)))
    have hστ := congrArg (inducedChain (σ.prodMap τ) (n + 1)) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.sub_apply, LinearMap.id_apply, map_sub, inducedChain_boundary,
      crossProductEdge_natural, crossProductZeroLeft_natural,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

/-- Crossing two actual cycles produces an actual cycle. -/
theorem crossProductEdge_cycle (n : ℕ) (a : Chains X 1) (b : Chains Y n)
    (ha : ((singularComplex X).d 1 0).hom a = 0)
    (hb : ((singularComplex Y).d n (n - 1)).hom b = 0) :
    ((singularComplex (X × Y)).d (n + 1) n).hom (crossProductEdge X Y n a b) = 0 := by
  cases n with
  | zero =>
      have h := crossProductEdge_boundary_zero a b
      rw [ha, map_zero, LinearMap.zero_apply] at h
      exact h
  | succ n =>
      have hb' : ((singularComplex Y).d (n + 1) n).hom b = 0 := by
        simpa only [Nat.succ_sub_one] using hb
      simp only [crossProductEdge_boundary, ha, hb', map_zero, LinearMap.zero_apply, sub_self]

/-- With a closed left factor, the edge cross product anticommutes with boundaries. -/
theorem crossProductEdge_boundary_of_left_cycle (n : ℕ) (a : Chains X 1)
    (ha : ((singularComplex X).d 1 0).hom a = 0) (b : Chains Y (n + 1)) :
    ((singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductEdge X Y (n + 1) a b) =
      -crossProductEdge X Y n a (((singularComplex Y).d (n + 1) n).hom b) := by
  simp only [crossProductEdge_boundary, ha, map_zero, LinearMap.zero_apply, zero_sub]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
