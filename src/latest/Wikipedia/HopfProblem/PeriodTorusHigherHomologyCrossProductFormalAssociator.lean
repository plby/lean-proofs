import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalTriangleSupport
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalAssociatorAxes

/-!
# The ordered-chain associator defect

For two edge factors and an arbitrary third factor, compare the two
parenthesizations of the ordered cross product after identifying the vertex
products by their canonical associativity map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W Z V' W' Z' M : Type*}

/-- Trilinear maps of formal chains are determined by triples of simplices. -/
theorem formalChains_trilinear_ext {n m l : ℕ} [AddCommGroup M] [Module ℤ M]
    {f g : FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ]
      FormalChains Z l →ₗ[ℤ] M}
    (h : ∀ v w z, f (formalSimplex v) (formalSimplex w) (formalSimplex z) =
      g (formalSimplex v) (formalSimplex w) (formalSimplex z)) : f = g := by
  apply formalChains_ext
  intro v
  apply formalChains_bilinear_ext
  exact h v

/-- Extend a function on triples of ordered simplices linearly in all inputs. -/
def formalTrilinearLift {n m l : ℕ} [AddCommGroup M] [Module ℤ M]
    (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M) :
    FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ] FormalChains Z l →ₗ[ℤ] M :=
  formalLift fun v => formalBilinearLift (f v)

@[simp] theorem formalTrilinearLift_simplex {n m l : ℕ}
    [AddCommGroup M] [Module ℤ M]
    (f : (Fin n → V) → (Fin m → W) → (Fin l → Z) → M)
    (v : Fin n → V) (w : Fin m → W) (z : Fin l → Z) :
    formalTrilinearLift f (formalSimplex v) (formalSimplex w) (formalSimplex z) =
      f v w z := by
  simp [formalTrilinearLift]

/-- The left-associated product minus the right-associated product. -/
def formalAssociatorDefect (q : ℕ) :
    FormalChains V 2 →ₗ[ℤ] FormalChains W 2 →ₗ[ℤ] FormalChains Z (q + 1) →ₗ[ℤ]
      FormalChains (V × (W × Z)) (q + 3) :=
  (formalEdgeCrossProduct 1).compr₂
      ((formalTriangleCrossProduct q).compr₂
        (formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 3))) -
    ((LinearMap.llcomp ℤ (FormalChains Z (q + 1)) (FormalChains (W × Z) (q + 2))
        (FormalChains (V × (W × Z)) (q + 3))).compl₂
      (formalEdgeCrossProduct q)).comp (formalEdgeCrossProduct (q + 1))

@[simp] theorem formalAssociatorDefect_apply (q : ℕ)
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z (q + 1)) :
    formalAssociatorDefect q a b c =
      formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 3)
          (formalTriangleCrossProduct q (formalEdgeCrossProduct 1 a b) c) -
        formalEdgeCrossProduct (q + 1) a (formalEdgeCrossProduct q b c) := rfl

/-- Both parenthesizations agree strictly when the third factor is a zero-chain. -/
@[simp] theorem formalAssociatorDefect_zero
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z 1) :
    formalAssociatorDefect 0 a b c = 0 := by
  rw [formalAssociatorDefect_apply, formalTriangleCrossProduct_point_right, sub_self]

/-- All first- and second-factor boundary terms cancel without cycle hypotheses. -/
theorem formalBoundary_associatorDefect (q : ℕ)
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z (q + 2)) :
    formalBoundary (q + 3) (formalAssociatorDefect (q + 1) a b c) =
      formalAssociatorDefect q a b (formalBoundary (q + 1) c) := by
  simp only [formalAssociatorDefect_apply, map_sub, ← formalMap_boundary,
    formalBoundary_triangleCrossProduct, formalBoundary_edgeCrossProduct,
    map_add, LinearMap.sub_apply, formalEdgeCrossProduct_point_middle]
  rw [formalEdgeCrossProduct_point_left (q + 1) (formalBoundary 1 a) b c]
  abel

/-- Vertexwise product maps commute with the product associativity map. -/
theorem formalMap_prodAssoc_naturality (f : V → V') (g : W → W') (h : Z → Z')
    (n : ℕ) (c : FormalChains ((V × W) × Z) n) :
    formalMap (Prod.map f (Prod.map g h)) n
        (formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n c) =
      formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n
        (formalMap (Prod.map (Prod.map f g) h) n c) := by
  have heq : (formalMap (Prod.map f (Prod.map g h)) n).comp
        (formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) n) =
      (formalMap (fun p : (V' × W') × Z' => (p.1.1, (p.1.2, p.2))) n).comp
        (formalMap (Prod.map (Prod.map f g) h) n) := by
    apply formalChains_ext
    intro v
    simp only [LinearMap.comp_apply, formalMap_simplex]
    rfl
  exact LinearMap.congr_fun heq c

/-- The associator defect is natural for arbitrary maps of all three vertex sets. -/
theorem formalMap_associatorDefect (f : V → V') (g : W → W') (h : Z → Z')
    (q : ℕ) (a : FormalChains V 2) (b : FormalChains W 2)
    (c : FormalChains Z (q + 1)) :
    formalMap (Prod.map f (Prod.map g h)) (q + 3) (formalAssociatorDefect q a b c) =
      formalAssociatorDefect q (formalMap f 2 a) (formalMap g 2 b)
        (formalMap h (q + 1) c) := by
  rw [formalAssociatorDefect_apply, map_sub, formalMap_prodAssoc_naturality,
    formalMap_triangleCrossProduct, formalMap_edgeCrossProduct,
    formalMap_edgeCrossProduct, formalMap_edgeCrossProduct]
  rfl

/-- Both parenthesizations remain inside the product of the three vertex supports. -/
theorem formalAssociatorDefect_mem_supported (q : ℕ)
    {S : Set V} {T : Set W} {U : Set Z}
    {a : FormalChains V 2} {b : FormalChains W 2} {c : FormalChains Z (q + 1)}
    (ha : a ∈ formalChainsSupported S 2) (hb : b ∈ formalChainsSupported T 2)
    (hc : c ∈ formalChainsSupported U (q + 1)) :
    formalAssociatorDefect q a b c ∈ formalChainsSupported (S ×ˢ (T ×ˢ U)) (q + 3) := by
  rw [formalAssociatorDefect_apply]
  apply Submodule.sub_mem
  · exact formalMap_mem_supported (S := (S ×ˢ T) ×ˢ U) (T := S ×ˢ (T ×ˢ U))
      (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2)))
      (fun _ hp => ⟨hp.1.1, hp.1.2, hp.2⟩)
      (formalTriangleCrossProduct_mem_supported q
        (formalEdgeCrossProduct_mem_supported 1 ha hb) hc)
  · exact formalEdgeCrossProduct_mem_supported (q + 1) ha
      (formalEdgeCrossProduct_mem_supported q hb hc)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
