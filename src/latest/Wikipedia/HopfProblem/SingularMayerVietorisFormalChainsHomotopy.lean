import Wikipedia.HopfProblem.SingularMayerVietorisFormalChainsSubdivision

/-!
# An explicit homotopy from subdivision to the identity

The homotopy is constructed recursively by coning to the first vertex. Each
chain being coned is a cycle, by the already proved lower-dimensional homotopy
identity. No acyclicity or subdivision theorem is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {V W : Type*}

/-- The recursive prism chain between a simplex and its subdivision. -/
def formalSubdivisionHomotopy (center : FormalCenter V) :
    (n : ℕ) → FormalChains V n →ₗ[ℤ] FormalChains V (n + 1)
  | 0 => 0
  | n + 1 => formalLift fun v =>
      formalCone (v 0) (n + 1)
        (formalSimplex v - formalSubdivision center (n + 1) (formalSimplex v) -
          formalSubdivisionHomotopy center n (formalBoundary n (formalSimplex v)))

@[simp] theorem formalSubdivisionHomotopy_zero (center : FormalCenter V)
    (c : FormalChains V 0) : formalSubdivisionHomotopy center 0 c = 0 := rfl

@[simp] theorem formalSubdivisionHomotopy_simplex_succ (center : FormalCenter V)
    (n : ℕ) (v : Fin (n + 1) → V) :
    formalSubdivisionHomotopy center (n + 1) (formalSimplex v) =
      formalCone (v 0) (n + 1)
        (formalSimplex v - formalSubdivision center (n + 1) (formalSimplex v) -
          formalSubdivisionHomotopy center n (formalBoundary n (formalSimplex v))) :=
  formalLift_simplex _ _

/-- The augmented degree-zero homotopy identity. -/
theorem formalSubdivisionHomotopy_boundary_zero (center : FormalCenter V)
    (c : FormalChains V 0) :
    formalBoundary 0 (formalSubdivisionHomotopy center 0 c) =
      c - formalSubdivision center 0 c := by
  simp

/-- The explicit chain homotopy identity `d H + H d = id - sd`. -/
theorem formalSubdivisionHomotopy_boundary (center : FormalCenter V) :
    ∀ (n : ℕ) (c : FormalChains V (n + 1)),
      formalBoundary (n + 1) (formalSubdivisionHomotopy center (n + 1) c) +
          formalSubdivisionHomotopy center n (formalBoundary n c) =
        c - formalSubdivision center (n + 1) c := by
  intro n
  induction n with
  | zero =>
      intro c
      have h : (formalBoundary 1).comp (formalSubdivisionHomotopy center 1) +
          (formalSubdivisionHomotopy center 0).comp (formalBoundary 0) =
            LinearMap.id - formalSubdivision center 1 := by
        apply formalChains_ext
        intro v
        change formalBoundary 1 (formalSubdivisionHomotopy center 1 (formalSimplex v)) +
            formalSubdivisionHomotopy center 0 (formalBoundary 0 (formalSimplex v)) =
          formalSimplex v - formalSubdivision center 1 (formalSimplex v)
        have hc : formalBoundary 0
            (formalSimplex v - formalSubdivision center 1 (formalSimplex v) -
              formalSubdivisionHomotopy center 0 (formalBoundary 0 (formalSimplex v))) = 0 := by
          simp only [map_sub, formalBoundary_subdivision, formalSubdivision_zero,
            formalSubdivisionHomotopy_zero, sub_self, sub_zero]
        rw [formalSubdivisionHomotopy_simplex_succ, formalBoundary_cone, hc,
          map_zero, sub_zero, sub_add_cancel]
      exact LinearMap.congr_fun h c
  | succ n ih =>
      intro c
      have h : (formalBoundary (n + 2)).comp (formalSubdivisionHomotopy center (n + 2)) +
          (formalSubdivisionHomotopy center (n + 1)).comp (formalBoundary (n + 1)) =
            LinearMap.id - formalSubdivision center (n + 2) := by
        apply formalChains_ext
        intro v
        change formalBoundary (n + 2)
              (formalSubdivisionHomotopy center (n + 2) (formalSimplex v)) +
            formalSubdivisionHomotopy center (n + 1)
              (formalBoundary (n + 1) (formalSimplex v)) =
          formalSimplex v - formalSubdivision center (n + 2) (formalSimplex v)
        have hp : formalBoundary (n + 1)
              (formalSubdivisionHomotopy center (n + 1)
                (formalBoundary (n + 1) (formalSimplex v))) =
            formalBoundary (n + 1) (formalSimplex v) -
              formalSubdivision center (n + 1) (formalBoundary (n + 1) (formalSimplex v)) := by
          simpa only [formalBoundary_boundary, map_zero, add_zero] using
            ih (formalBoundary (n + 1) (formalSimplex v))
        have hc : formalBoundary (n + 1)
            (formalSimplex v - formalSubdivision center (n + 2) (formalSimplex v) -
              formalSubdivisionHomotopy center (n + 1)
                (formalBoundary (n + 1) (formalSimplex v))) = 0 := by
          rw [map_sub, map_sub, formalBoundary_subdivision, hp, sub_self]
        rw [formalSubdivisionHomotopy_simplex_succ, formalBoundary_cone, hc,
          map_zero, sub_zero, sub_add_cancel]
      exact LinearMap.congr_fun h c

/-- Naturality of the explicit homotopy for center-preserving vertex maps. -/
theorem formalMap_subdivisionHomotopy (center : FormalCenter V) (center' : FormalCenter W)
    (f : V → W) (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) :
    ∀ (n : ℕ) (c : FormalChains V n),
      formalMap f (n + 1) (formalSubdivisionHomotopy center n c) =
        formalSubdivisionHomotopy center' n (formalMap f n c) := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
      intro c
      have h : (formalMap f (n + 2)).comp (formalSubdivisionHomotopy center (n + 1)) =
          (formalSubdivisionHomotopy center' (n + 1)).comp (formalMap f (n + 1)) := by
        apply formalChains_ext
        intro v
        simp only [LinearMap.comp_apply, formalSubdivisionHomotopy_simplex_succ,
          formalMap_simplex]
        rw [formalMap_cone]
        congr 1
        rw [map_sub, map_sub, formalMap_simplex,
          formalMap_subdivision center center' f hf, ih,
          formalMap_boundary, formalMap_simplex]
      exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.SingularMayerVietoris
