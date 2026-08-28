import Wikipedia.HopfProblem.SingularMayerVietorisFormalChains

/-!
# Recursive subdivision of formal ordered chains

For any choice of a center for each nonempty ordered simplex, coning the
subdivided boundary to that center defines a chain map. Barycentric subdivision
is the case where the center is the arithmetic mean of the vertices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SingularMayerVietoris

variable {V W : Type*}

/-- A center selector for every nonempty ordered simplex. -/
abbrev FormalCenter (V : Type*) := ∀ n : ℕ, (Fin (n + 1) → V) → V

/-- Subdivision by recursively coning the subdivided boundary to its center. -/
def formalSubdivision (center : FormalCenter V) :
    (n : ℕ) → FormalChains V n →ₗ[ℤ] FormalChains V n
  | 0 => LinearMap.id
  | n + 1 => formalLift fun v =>
      formalCone (center n v) n
        (formalSubdivision center n (formalBoundary n (formalSimplex v)))

@[simp] theorem formalSubdivision_zero (center : FormalCenter V) (c : FormalChains V 0) :
    formalSubdivision center 0 c = c := rfl

@[simp] theorem formalSubdivision_simplex_succ (center : FormalCenter V)
    (n : ℕ) (v : Fin (n + 1) → V) :
    formalSubdivision center (n + 1) (formalSimplex v) =
      formalCone (center n v) n
        (formalSubdivision center n (formalBoundary n (formalSimplex v))) :=
  formalLift_simplex _ _

/-- Recursive subdivision commutes with the actual alternating formal boundary. -/
theorem formalBoundary_subdivision (center : FormalCenter V) :
    ∀ (n : ℕ) (c : FormalChains V (n + 1)),
      formalBoundary n (formalSubdivision center (n + 1) c) =
        formalSubdivision center n (formalBoundary n c) := by
  intro n
  induction n with
  | zero =>
      intro c
      have h : (formalBoundary 0).comp (formalSubdivision center 1) =
          (formalSubdivision center 0).comp (formalBoundary 0) := by
        apply formalChains_ext
        intro v
        simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ,
          formalBoundary_cone_zero]
      exact LinearMap.congr_fun h c
  | succ n ih =>
      intro c
      have h : (formalBoundary (n + 1)).comp (formalSubdivision center (n + 2)) =
          (formalSubdivision center (n + 1)).comp (formalBoundary (n + 1)) := by
        apply formalChains_ext
        intro v
        simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ]
        rw [formalBoundary_cone, ih, formalBoundary_boundary, map_zero, map_zero, sub_zero]
      exact LinearMap.congr_fun h c

/-- Naturality for maps which carry each chosen center to the corresponding center. -/
theorem formalMap_subdivision (center : FormalCenter V) (center' : FormalCenter W)
    (f : V → W) (hf : ∀ n v, f (center n v) = center' n (f ∘ v)) :
    ∀ (n : ℕ) (c : FormalChains V n),
      formalMap f n (formalSubdivision center n c) =
        formalSubdivision center' n (formalMap f n c) := by
  intro n
  induction n with
  | zero => intro c; rfl
  | succ n ih =>
      intro c
      have h : (formalMap f (n + 1)).comp (formalSubdivision center (n + 1)) =
          (formalSubdivision center' (n + 1)).comp (formalMap f (n + 1)) := by
        apply formalChains_ext
        intro v
        simp only [LinearMap.comp_apply, formalSubdivision_simplex_succ, formalMap_simplex]
        rw [formalMap_cone, ih, formalMap_boundary, formalMap_simplex, hf]
      exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.SingularMayerVietoris
