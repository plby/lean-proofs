import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductFormalAssociator

/-!
# An explicit formal associator homotopy

For two edge inputs and a third chain of arbitrary degree, the associator defect
commutes with the boundary in the third input.  Coning recursively to the triple
of first vertices gives a natural homotopy, with support in the product of the
three vertex support sets.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open SingularMayerVietoris

variable {V W Z V' W' Z' U U' : Type*}

private def triplePostcomp {n m l r s : ℕ}
    (F : FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ]
      FormalChains Z l →ₗ[ℤ] FormalChains U r)
    (f : FormalChains U r →ₗ[ℤ] FormalChains U' s) :
    FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ]
      FormalChains Z l →ₗ[ℤ] FormalChains U' s :=
  F.compr₂ (LinearMap.llcomp ℤ (FormalChains Z l) (FormalChains U r)
    (FormalChains U' s) f)

private def triplePrecompLast {n m l l' r : ℕ}
    (F : FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ]
      FormalChains Z l →ₗ[ℤ] FormalChains U r)
    (f : FormalChains Z' l' →ₗ[ℤ] FormalChains Z l) :
    FormalChains V n →ₗ[ℤ] FormalChains W m →ₗ[ℤ]
      FormalChains Z' l' →ₗ[ℤ] FormalChains U r :=
  F.compr₂ ((LinearMap.llcomp ℤ (FormalChains Z' l') (FormalChains Z l)
    (FormalChains U r)).flip f)

/-- The explicit cone homotopy for the two parenthesizations of the edge products. -/
def formalAssociatorHomotopy : (q : ℕ) →
    FormalChains V 2 →ₗ[ℤ] FormalChains W 2 →ₗ[ℤ] FormalChains Z (q + 1) →ₗ[ℤ]
      FormalChains (V × (W × Z)) (q + 4)
  | 0 => 0
  | q + 1 => formalTrilinearLift fun v w z =>
      formalCone (v 0, (w 0, z 0)) (q + 4)
        (formalAssociatorDefect (q + 1)
            (formalSimplex v) (formalSimplex w) (formalSimplex z) -
          formalAssociatorHomotopy q (formalSimplex v) (formalSimplex w)
            (formalBoundary (q + 1) (formalSimplex z)))

@[simp] theorem formalAssociatorHomotopy_zero
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z 1) :
    formalAssociatorHomotopy 0 a b c = 0 := rfl

@[simp] theorem formalAssociatorHomotopy_simplex_succ (q : ℕ)
    (v : Fin 2 → V) (w : Fin 2 → W) (z : Fin (q + 2) → Z) :
    formalAssociatorHomotopy (q + 1)
        (formalSimplex v) (formalSimplex w) (formalSimplex z) =
      formalCone (v 0, (w 0, z 0)) (q + 4)
        (formalAssociatorDefect (q + 1)
            (formalSimplex v) (formalSimplex w) (formalSimplex z) -
          formalAssociatorHomotopy q (formalSimplex v) (formalSimplex w)
            (formalBoundary (q + 1) (formalSimplex z))) :=
  formalTrilinearLift_simplex _ _ _ _

/-- The homotopy identity in third geometric degree zero. -/
theorem formalAssociatorHomotopy_boundary_zero
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z 1) :
    formalBoundary 3 (formalAssociatorHomotopy 0 a b c) =
      formalAssociatorDefect 0 a b c := by
  rw [formalAssociatorHomotopy_zero, map_zero, formalAssociatorDefect_zero]

/-- The explicit associator homotopy identity `d Q + Q d = D`. -/
theorem formalAssociatorHomotopy_boundary : ∀ (q : ℕ)
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z (q + 2)),
    formalBoundary (q + 4) (formalAssociatorHomotopy (q + 1) a b c) +
        formalAssociatorHomotopy q a b (formalBoundary (q + 1) c) =
      formalAssociatorDefect (q + 1) a b c := by
  intro q
  induction q with
  | zero =>
      intro a b c
      have heq : triplePostcomp
            (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) 1)
            (formalBoundary 4) +
          triplePrecompLast (formalAssociatorHomotopy 0) (formalBoundary 1) =
            formalAssociatorDefect 1 := by
        apply formalChains_trilinear_ext
        intro v w z
        change formalBoundary 4
            (formalAssociatorHomotopy 1 (formalSimplex v) (formalSimplex w)
              (formalSimplex z)) +
            formalAssociatorHomotopy 0 (formalSimplex v) (formalSimplex w)
              (formalBoundary 1 (formalSimplex z)) =
          formalAssociatorDefect 1 (formalSimplex v) (formalSimplex w) (formalSimplex z)
        have hz : formalBoundary 3
            (formalAssociatorDefect 1 (formalSimplex v) (formalSimplex w)
                (formalSimplex z) -
              formalAssociatorHomotopy 0 (formalSimplex v) (formalSimplex w)
                (formalBoundary 1 (formalSimplex z))) = 0 := by
          rw [map_sub, formalBoundary_associatorDefect, formalAssociatorDefect_zero,
            formalAssociatorHomotopy_zero, map_zero, sub_self]
        rw [formalAssociatorHomotopy_simplex_succ, formalBoundary_cone,
          hz, map_zero, sub_zero, sub_add_cancel]
      exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c
  | succ q ih =>
      intro a b c
      have heq : triplePostcomp
            (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 2))
            (formalBoundary (q + 5)) +
          triplePrecompLast (formalAssociatorHomotopy (q + 1)) (formalBoundary (q + 2)) =
            formalAssociatorDefect (q + 2) := by
        apply formalChains_trilinear_ext
        intro v w z
        change formalBoundary (q + 5)
            (formalAssociatorHomotopy (q + 2) (formalSimplex v) (formalSimplex w)
              (formalSimplex z)) +
            formalAssociatorHomotopy (q + 1) (formalSimplex v) (formalSimplex w)
              (formalBoundary (q + 2) (formalSimplex z)) =
          formalAssociatorDefect (q + 2) (formalSimplex v) (formalSimplex w) (formalSimplex z)
        have hp : formalBoundary (q + 4)
            (formalAssociatorHomotopy (q + 1) (formalSimplex v) (formalSimplex w)
              (formalBoundary (q + 2) (formalSimplex z))) =
          formalAssociatorDefect (q + 1) (formalSimplex v) (formalSimplex w)
            (formalBoundary (q + 2) (formalSimplex z)) := by
          simpa only [formalBoundary_boundary, map_zero, add_zero] using
            ih (formalSimplex v) (formalSimplex w) (formalBoundary (q + 2) (formalSimplex z))
        have hz : formalBoundary (q + 4)
            (formalAssociatorDefect (q + 2) (formalSimplex v) (formalSimplex w)
                (formalSimplex z) -
              formalAssociatorHomotopy (q + 1) (formalSimplex v) (formalSimplex w)
                (formalBoundary (q + 2) (formalSimplex z))) = 0 := by
          rw [map_sub, formalBoundary_associatorDefect, hp, sub_self]
        rw [formalAssociatorHomotopy_simplex_succ, formalBoundary_cone,
          hz, map_zero, sub_zero, sub_add_cancel]
      exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

/-- For a cycle in the third input the associator defect is an explicit boundary. -/
theorem formalAssociatorHomotopy_boundary_of_cycle (q : ℕ)
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z (q + 2))
    (hc : formalBoundary (q + 1) c = 0) :
    formalBoundary (q + 4) (formalAssociatorHomotopy (q + 1) a b c) =
      formalAssociatorDefect (q + 1) a b c := by
  simpa only [hc, map_zero, add_zero] using formalAssociatorHomotopy_boundary q a b c

/-- The two parenthesizations differ by the boundary of the explicit homotopy. -/
theorem formalCrossProduct_associativity_boundary (q : ℕ)
    (a : FormalChains V 2) (b : FormalChains W 2) (c : FormalChains Z (q + 2))
    (hc : formalBoundary (q + 1) c = 0) :
    formalMap (fun p : (V × W) × Z => (p.1.1, (p.1.2, p.2))) (q + 4)
          (formalTriangleCrossProduct (q + 1) (formalEdgeCrossProduct 1 a b) c) -
        formalEdgeCrossProduct (q + 2) a (formalEdgeCrossProduct (q + 1) b c) =
      formalBoundary (q + 4) (formalAssociatorHomotopy (q + 1) a b c) :=
  (formalAssociatorHomotopy_boundary_of_cycle q a b c hc).symm

/-- Naturality of the cone homotopy for arbitrary maps of all three vertex sets. -/
theorem formalMap_associatorHomotopy (f : V → V') (g : W → W') (h : Z → Z') :
    ∀ (q : ℕ) (a : FormalChains V 2) (b : FormalChains W 2)
      (c : FormalChains Z (q + 1)),
    formalMap (Prod.map f (Prod.map g h)) (q + 4)
        (formalAssociatorHomotopy q a b c) =
      formalAssociatorHomotopy q (formalMap f 2 a) (formalMap g 2 b)
        (formalMap h (q + 1) c) := by
  intro q
  induction q with
  | zero =>
      intro a b c
      simp only [formalAssociatorHomotopy_zero, map_zero]
  | succ q ih =>
      intro a b c
      have heq : triplePostcomp
            (formalAssociatorHomotopy (V := V) (W := W) (Z := Z) (q + 1))
            (formalMap (Prod.map f (Prod.map g h)) (q + 5)) =
          ((triplePrecompLast (formalAssociatorHomotopy (q + 1))
            (formalMap h (q + 2))).compl₂ (formalMap g 2)).comp (formalMap f 2) := by
        apply formalChains_trilinear_ext
        intro v w z
        change formalMap (Prod.map f (Prod.map g h)) (q + 5)
            (formalAssociatorHomotopy (q + 1)
              (formalSimplex v) (formalSimplex w) (formalSimplex z)) =
          formalAssociatorHomotopy (q + 1)
            (formalMap f 2 (formalSimplex v)) (formalMap g 2 (formalSimplex w))
            (formalMap h (q + 2) (formalSimplex z))
        simp only [formalMap_simplex, formalAssociatorHomotopy_simplex_succ]
        rw [formalMap_cone]
        congr 1
        rw [map_sub, formalMap_associatorDefect, ih, formalMap_boundary,
          formalMap_simplex, formalMap_simplex, formalMap_simplex]
      exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun heq a) b) c

/-- The associator homotopy stays inside the product of the vertex support sets. -/
theorem formalAssociatorHomotopy_mem_supported {S : Set V} {T : Set W} {U : Set Z} :
    ∀ (q : ℕ) {a : FormalChains V 2} {b : FormalChains W 2}
      {c : FormalChains Z (q + 1)},
    a ∈ formalChainsSupported S 2 → b ∈ formalChainsSupported T 2 →
      c ∈ formalChainsSupported U (q + 1) →
    formalAssociatorHomotopy q a b c ∈
      formalChainsSupported (S ×ˢ (T ×ˢ U)) (q + 4) := by
  intro q
  induction q with
  | zero =>
      intro a b c _ _ _
      rw [formalAssociatorHomotopy_zero]
      exact Submodule.zero_mem _
  | succ q ih =>
      intro a b c ha hb hc
      apply formalLinearMap_mem_of_supported
        (((formalAssociatorHomotopy (q + 1)).flip b).flip c)
        (formalChainsSupported (S ×ˢ (T ×ˢ U)) (q + 5)) ha
      intro v hv
      apply formalLinearMap_mem_of_supported
        ((formalAssociatorHomotopy (q + 1) (formalSimplex v)).flip c)
        (formalChainsSupported (S ×ˢ (T ×ˢ U)) (q + 5)) hb
      intro w hw
      apply formalLinearMap_mem_of_supported
        (formalAssociatorHomotopy (q + 1) (formalSimplex v) (formalSimplex w))
        (formalChainsSupported (S ×ˢ (T ×ˢ U)) (q + 5)) hc
      intro z hz
      rw [formalAssociatorHomotopy_simplex_succ]
      apply formalCone_mem_supported (S := S ×ˢ (T ×ˢ U)) ⟨hv 0, hw 0, hz 0⟩
      apply Submodule.sub_mem
      · exact formalAssociatorDefect_mem_supported (q + 1)
          (formalSimplex_mem_supported hv) (formalSimplex_mem_supported hw)
          (formalSimplex_mem_supported hz)
      · exact ih (formalSimplex_mem_supported hv) (formalSimplex_mem_supported hw)
          (formalBoundary_mem_supported (q + 1) (formalSimplex_mem_supported hz))

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
