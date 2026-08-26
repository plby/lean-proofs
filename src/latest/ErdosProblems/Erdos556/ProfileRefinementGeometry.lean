import ErdosProblems.Erdos556.CubeMatchingGeometry
import ErdosProblems.Erdos556.CubeRetainedGeometry

/-! Finite cube facts used when a face is split into two parallel edge profiles. -/

namespace Erdos556

open Finset

theorem edge_profile_direction : ∀ p : CubeProfile, profileDimension p = 1 →
    ∃ a : Fin 3, ∀ l : Fin 4, evenCubeVertex l ∈ profileVertices p →
      matchingProfile l a = p := by decide

theorem edge_profile_even_vertex_unique : ∀ (p : CubeProfile) (l m : Fin 4),
    profileDimension p = 1 → evenCubeVertex l ∈ profileVertices p →
      evenCubeVertex m ∈ profileVertices p → l = m := by decide

theorem face_matching_profile_subset : ∀ (i a : Fin 3) (b : Bool) (l : Fin 4),
    a ≠ i → evenCubeVertex l ∈ profileVertices (cubeFace i b) →
      profileVertices (matchingProfile l a) ⊆ profileVertices (cubeFace i b) := by decide

theorem face_even_vertices_differ : ∀ (i k : Fin 3) (b : Bool) (l m : Fin 4),
    k ≠ i → l ≠ m → evenCubeVertex l ∈ profileVertices (cubeFace i b) →
      evenCubeVertex m ∈ profileVertices (cubeFace i b) →
      evenCubeVertex l k ≠ evenCubeVertex m k := by decide

theorem face_parallel_profiles_disjoint : ∀ (i a : Fin 3) (b : Bool) (l m : Fin 4),
    a ≠ i → l ≠ m → evenCubeVertex l ∈ profileVertices (cubeFace i b) →
      evenCubeVertex m ∈ profileVertices (cubeFace i b) →
      Disjoint (profileVertices (matchingProfile l a)) (profileVertices (matchingProfile m a)) := by decide

theorem face_parallel_unique_separator : ∀ (i a k z : Fin 3) (b : Bool) (l m : Fin 4),
    a ≠ i → k ≠ i → a ≠ k →
      evenCubeVertex l ∈ profileVertices (cubeFace i b) →
      evenCubeVertex m ∈ profileVertices (cubeFace i b) →
      uniqueProfileSeparator (matchingProfile l a) (matchingProfile m a) z → z = k := by decide

theorem profile_disjoint_has_opposite : ∀ p q : CubeProfile,
    Disjoint (profileVertices p) (profileVertices q) → ∃ i, profileOppositeAt p q i := by decide

theorem profile_fixed_of_refinement : ∀ p p' : CubeProfile, ∀ (i : Fin 3) (b : Bool),
    profileVertices p' ⊆ profileVertices p → p i = some b → p' i = some b := by decide

theorem profile_opposite_of_refinement (p q p' q' : CubeProfile) (i : Fin 3)
    (hp : profileVertices p' ⊆ profileVertices p) (hq : profileVertices q' ⊆ profileVertices q)
    (hopp : profileOppositeAt p q i) : profileOppositeAt p' q' i := by
  rcases hopp with ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
  · exact Or.inl ⟨profile_fixed_of_refinement p p' i false hp hp0,
      profile_fixed_of_refinement q q' i true hq hq1⟩
  · exact Or.inr ⟨profile_fixed_of_refinement p p' i true hp hp1,
      profile_fixed_of_refinement q q' i false hq hq0⟩

theorem unique_separator_of_disjoint_parent (p q p' q' : CubeProfile) (i : Fin 3)
    (hdis : Disjoint (profileVertices p) (profileVertices q))
    (hp : profileVertices p' ⊆ profileVertices p) (hq : profileVertices q' ⊆ profileVertices q)
    (hsep : uniqueProfileSeparator p' q' i) : uniqueProfileSeparator p q i := by
  obtain ⟨j, hj⟩ := profile_disjoint_has_opposite p q hdis
  have hji : j = i := by
    by_contra hji
    exact hsep.2 j hji (profile_opposite_of_refinement p q p' q' j hp hq hj)
  subst j
  refine ⟨hj, ?_⟩
  intro j hji hj
  exact hsep.2 j hji (profile_opposite_of_refinement p q p' q' j hp hq hj)

#print axioms unique_separator_of_disjoint_parent

end Erdos556
