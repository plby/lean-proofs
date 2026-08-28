import Wikipedia.HopfProblem.SingularMayerVietorisSubdivision

/-!
# The subdivision homotopy on actual singular chains

The universal formal homotopy is evaluated as affine singular simplices and
pushed forward by each singular simplex. Its formal telescoping identity gives
the genuine singular-chain identity `d H + H d = id - sd^k`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

/-- The explicit homotopy from `k` subdivisions to the identity on actual chains. -/
def subdivisionHomotopy (X : Type) [TopologicalSpace X] (k n : ℕ) :
    Chains X n →ₗ[ℤ] Chains X (n + 1) :=
  chainLift X n fun σ => inducedChain σ (n + 1)
    (affineChainMap n (n + 1)
      (formalSubdivisionIteratedHomotopy (simplexCenter n) k (n + 1)
        (formalSimplex (stdVertices n))))

@[simp] theorem subdivisionHomotopy_simplex (X : Type) [TopologicalSpace X] (k n : ℕ)
    (σ : SingularSimplex X n) :
    subdivisionHomotopy X k n (simplexChain X n σ) = inducedChain σ (n + 1)
      (affineChainMap n (n + 1)
        (formalSubdivisionIteratedHomotopy (simplexCenter n) k (n + 1)
          (formalSimplex (stdVertices n)))) :=
  chainLift_simplex X n _ σ

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Naturality of the actual homotopy under every continuous map. -/
theorem inducedChain_subdivisionHomotopy (f : C(X, Y)) (k n : ℕ) (c : Chains X n) :
    inducedChain f (n + 1) (subdivisionHomotopy X k n c) =
      subdivisionHomotopy Y k n (inducedChain f n c) := by
  have h : (inducedChain f (n + 1)).comp (subdivisionHomotopy X k n) =
      (subdivisionHomotopy Y k n).comp (inducedChain f n) := by
    apply chainMap_ext X n
    intro σ
    simp only [LinearMap.comp_apply, subdivisionHomotopy_simplex, inducedChain_simplex]
    rw [inducedChain_comp]
    rfl
  exact LinearMap.congr_fun h c

/-- Evaluation of affine chains intertwines the formal and actual homotopies. -/
theorem subdivisionHomotopy_affineChainMap (p k n : ℕ)
    (c : FormalChains (Simplex p) (n + 1)) :
    subdivisionHomotopy (Simplex p) k n (affineChainMap p n c) =
      affineChainMap p (n + 1)
        (formalSubdivisionIteratedHomotopy (simplexCenter p) k (n + 1) c) := by
  have h : (subdivisionHomotopy (Simplex p) k n).comp (affineChainMap p n) =
      (affineChainMap p (n + 1)).comp
        (formalSubdivisionIteratedHomotopy (simplexCenter p) k (n + 1)) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, affineChainMap_simplex, subdivisionHomotopy_simplex]
    rw [inducedChain_affineChainMap,
      formalMap_subdivisionIteratedHomotopy (simplexCenter n) (simplexCenter p)
        (affineSimplex v) (affineSimplex_preserves_center v),
      formalMap_simplex, affineSimplex_comp_stdVertices]
  exact LinearMap.congr_fun h c

/-- In degree zero the augmented formal term disappears after evaluation. -/
theorem subdivisionHomotopy_boundary_zero_affineChainMap (p k : ℕ)
    (c : FormalChains (Simplex p) 1) :
    ((singularComplex (Simplex p)).d 1 0).hom
        (subdivisionHomotopy (Simplex p) k 0 (affineChainMap p 0 c)) =
      affineChainMap p 0 c - subdivision (Simplex p) k 0 (affineChainMap p 0 c) := by
  rw [subdivisionHomotopy_affineChainMap, affineChainMap_boundary,
    subdivision_affineChainMap, ← map_sub]
  apply congrArg (affineChainMap p 0)
  simpa only [formalSubdivisionIteratedHomotopy_degree_zero, add_zero] using
    formalSubdivisionIteratedHomotopy_boundary (simplexCenter p) k 0 c

/-- The chain-homotopy identity on evaluated affine chains. -/
theorem subdivisionHomotopy_boundary_affineChainMap (p k n : ℕ)
    (c : FormalChains (Simplex p) (n + 2)) :
    ((singularComplex (Simplex p)).d (n + 2) (n + 1)).hom
        (subdivisionHomotopy (Simplex p) k (n + 1) (affineChainMap p (n + 1) c)) +
      subdivisionHomotopy (Simplex p) k n
        (((singularComplex (Simplex p)).d (n + 1) n).hom (affineChainMap p (n + 1) c)) =
      affineChainMap p (n + 1) c -
        subdivision (Simplex p) k (n + 1) (affineChainMap p (n + 1) c) := by
  rw [subdivisionHomotopy_affineChainMap, affineChainMap_boundary,
    affineChainMap_boundary, subdivisionHomotopy_affineChainMap,
    subdivision_affineChainMap, ← map_add, ← map_sub]
  exact congrArg (affineChainMap p (n + 1))
    (formalSubdivisionIteratedHomotopy_boundary (simplexCenter p) k (n + 1) c)

/-- The actual degree-zero singular-chain homotopy identity. -/
theorem subdivisionHomotopy_boundary_zero (k : ℕ) (c : Chains X 0) :
    ((singularComplex X).d 1 0).hom (subdivisionHomotopy X k 0 c) =
      c - subdivision X k 0 c := by
  have h : (((singularComplex X).d 1 0).hom).comp (subdivisionHomotopy X k 0) =
      LinearMap.id - subdivision X k 0 := by
    apply chainMap_ext X 0
    intro σ
    have hstd := subdivisionHomotopy_boundary_zero_affineChainMap 0 k
      (formalSimplex (stdVertices 0))
    have hσ := congrArg (inducedChain σ 0) hstd
    simpa only [map_sub, inducedChain_boundary, inducedChain_subdivisionHomotopy,
      inducedChain_subdivision, affineChainMap_stdVertices, inducedChain_simplex,
      ContinuousMap.comp_id, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply] using hσ
  exact LinearMap.congr_fun h c

/-- The full actual singular-chain homotopy identity `d H + H d = id - sd^k`. -/
theorem subdivisionHomotopy_boundary (k n : ℕ) (c : Chains X (n + 1)) :
    ((singularComplex X).d (n + 2) (n + 1)).hom
        (subdivisionHomotopy X k (n + 1) c) +
      subdivisionHomotopy X k n (((singularComplex X).d (n + 1) n).hom c) =
      c - subdivision X k (n + 1) c := by
  have h : (((singularComplex X).d (n + 2) (n + 1)).hom).comp
          (subdivisionHomotopy X k (n + 1)) +
        (subdivisionHomotopy X k n).comp (((singularComplex X).d (n + 1) n).hom) =
      LinearMap.id - subdivision X k (n + 1) := by
    apply chainMap_ext X (n + 1)
    intro σ
    have hstd := subdivisionHomotopy_boundary_affineChainMap (n + 1) k n
      (formalSimplex (stdVertices (n + 1)))
    have hσ := congrArg (inducedChain σ (n + 1)) hstd
    simpa only [map_add, map_sub, inducedChain_boundary,
      inducedChain_subdivisionHomotopy, inducedChain_subdivision,
      affineChainMap_stdVertices, inducedChain_simplex, ContinuousMap.comp_id,
      LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.id_apply] using hσ
  exact LinearMap.congr_fun h c

/-- Every actual cycle differs from its subdivision by the boundary of this homotopy. -/
theorem subdivisionHomotopy_boundary_of_cycle (k n : ℕ) (c : Chains X n)
    (hc : ((singularComplex X).d n (n - 1)).hom c = 0) :
    ((singularComplex X).d (n + 1) n).hom (subdivisionHomotopy X k n c) =
      c - subdivision X k n c := by
  cases n with
  | zero => exact subdivisionHomotopy_boundary_zero k c
  | succ n =>
      have hc' : ((singularComplex X).d (n + 1) n).hom c = 0 := by
        simpa only [Nat.succ_sub_one] using hc
      simpa only [hc', map_zero, add_zero] using subdivisionHomotopy_boundary k n c

end Wikipedia.HopfProblem.SingularMayerVietoris
