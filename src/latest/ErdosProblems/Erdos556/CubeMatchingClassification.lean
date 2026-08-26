import ErdosProblems.Erdos556.CubeMatchingGeometry

/-! The nine perfect matchings of the cube yield exactly the two four-core patterns. -/

namespace Erdos556

open Finset

theorem cube_matching_direction_cases : ∀ d : Fin 4 → Fin 3,
    Function.Injective (fun i => oddCubeEnd i (d i)) →
    d = ![0, 0, 0, 0] ∨
    d = ![0, 1, 1, 0] ∨
    d = ![2, 0, 2, 0] ∨
    d = ![1, 0, 0, 1] ∨
    d = ![1, 1, 1, 1] ∨
    d = ![2, 2, 1, 1] ∨
    d = ![0, 2, 0, 2] ∨
    d = ![1, 1, 2, 2] ∨
    d = ![2, 2, 2, 2] := by decide

theorem canonical_cube_matching_patterns (d : Fin 4 → Fin 3)
    (hd : Function.Injective (fun i => oddCubeEnd i (d i))) :
    ∃ (s : Fin 4 → Fin 4) (k : Fin 3 → Fin 3), Function.Injective s ∧ Function.Injective k ∧
      (HasPatternOneSeparators (fun i => matchingProfile (s i) (d (s i))) k ∨
       HasPatternTwoSeparators (fun i => matchingProfile (s i) (d (s i))) k) := by
  rcases cube_matching_direction_cases d hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨![0, 2, 3, 1], ![1, 2, 0], by decide, by decide, ?_⟩
    exact Or.inl (by decide)
  · refine ⟨![0, 3, 1, 2], ![2, 1, 0], by decide, by decide, ?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0, 2, 1, 3], ![1, 0, 2], by decide, by decide, ?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0, 3, 1, 2], ![2, 0, 1], by decide, by decide, ?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0, 1, 3, 2], ![0, 2, 1], by decide, by decide, ?_⟩
    exact Or.inl (by decide)
  · refine ⟨![0, 1, 2, 3], ![0, 1, 2], by decide, by decide, ?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0, 2, 1, 3], ![1, 2, 0], by decide, by decide, ?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0, 1, 2, 3], ![0, 2, 1], by decide, by decide, ?_⟩
    exact Or.inr (by decide)
  · refine ⟨![0, 1, 2, 3], ![0, 1, 2], by decide, by decide, ?_⟩
    exact Or.inl (by decide)

theorem disjoint_cube_edges_have_four_core_pattern (p : Fin 4 → CubeProfile)
    (hdim : ∀ i, profileDimension (p i) = 1)
    (hdis : ∀ i j, i ≠ j → Disjoint (profileVertices (p i)) (profileVertices (p j))) :
    ∃ (s : Fin 4 → Fin 4) (k : Fin 3 → Fin 3), Function.Injective s ∧ Function.Injective k ∧
      (HasPatternOneSeparators (fun i => p (s i)) k ∨ HasPatternTwoSeparators (fun i => p (s i)) k) := by
  classical
  choose a b hab using fun i => matchingProfile_exists (p i) (hdim i)
  have ha : Function.Injective a := by
    intro i j hij
    by_contra hne
    have hd := hdis i j hne
    have hi : evenCubeVertex (a i) ∈ profileVertices (p i) := by
      rw [hab i]
      exact evenCubeVertex_mem_matchingProfile (a i) (b i)
    have hj : evenCubeVertex (a i) ∈ profileVertices (p j) := by
      rw [hab j, hij]
      exact evenCubeVertex_mem_matchingProfile (a j) (b j)
    exact (Finset.disjoint_left.mp hd hi) hj
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective a ⟨ha, (Finite.injective_iff_surjective).mp ha⟩
  let d : Fin 4 → Fin 3 := fun i => b (e.symm i)
  have hcanon (i : Fin 4) : p (e.symm i) = matchingProfile i (d i) := by
    rw [hab (e.symm i)]
    have hi : a (e.symm i) = i := e.apply_symm_apply i
    rw [hi]
  have hodds : Function.Injective (fun i => oddCubeEnd i (d i)) := by
    intro i j hij
    change oddCubeEnd i (d i) = oddCubeEnd j (d j) at hij
    by_contra hne
    have hd := hdis (e.symm i) (e.symm j) (e.symm.injective.ne hne)
    have hi : oddCubeEnd i (d i) ∈ profileVertices (p (e.symm i)) := by
      rw [hcanon i]
      exact oddCubeEnd_mem_matchingProfile i (d i)
    have hj : oddCubeEnd i (d i) ∈ profileVertices (p (e.symm j)) := by
      rw [hcanon j, hij]
      exact oddCubeEnd_mem_matchingProfile j (d j)
    exact (Finset.disjoint_left.mp hd hi) hj
  obtain ⟨s, k, hs, hk, hp⟩ := canonical_cube_matching_patterns d hodds
  refine ⟨fun i => e.symm (s i), k, e.symm.injective.comp hs, hk, ?_⟩
  have heq : (fun i => p (e.symm (s i))) = (fun i => matchingProfile (s i) (d (s i))) := by
    funext i
    exact hcanon (s i)
  rwa [heq]

#print axioms disjoint_cube_edges_have_four_core_pattern

end Erdos556
