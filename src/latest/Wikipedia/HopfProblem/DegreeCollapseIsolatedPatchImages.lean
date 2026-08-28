import Mathlib.Data.Set.Function

/-!
# The two source sides inside a branch-isolating target neighborhood

Inside the target neighborhood, the selected open patch has exactly the
image of its larger closed patch. The entire unselected source has exactly
the image of the other closed patch. These identities allow the ambient
two-sheet cancellation to control the actual source-selective move.
-/

open Set Function

namespace Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet

variable {X Y : Type*} {f : X → Y} {U V K L : Set X} {O : Set Y}

theorem isolated_patch_images (hUK : U ⊆ K) (hVL : V ⊆ L) (hKL : Disjoint K L)
    (hpre : f ⁻¹' O ⊆ U ∪ V) :
    (f '' U) ∩ O = (f '' K) ∩ O ∧ (f '' Uᶜ) ∩ O = (f '' L) ∩ O := by
  constructor
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨⟨x, hUK hx, rfl⟩, hy⟩
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨⟨x, ?_, rfl⟩, hy⟩
      rcases hpre hy with hxU | hxV
      · exact hxU
      · exact ((Set.disjoint_left.mp hKL) hx (hVL hxV)).elim
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      refine ⟨⟨x, ?_, rfl⟩, hy⟩
      rcases hpre hy with hxU | hxV
      · exact (hx hxU).elim
      · exact hVL hxV
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      exact ⟨⟨x, fun hxU => (Set.disjoint_left.mp hKL) (hUK hxU) hx, rfl⟩, hy⟩

theorem isolated_cross_intersection (hUK : U ⊆ K) (hVL : V ⊆ L) (hKL : Disjoint K L)
    (hpre : f ⁻¹' O ⊆ U ∪ V) :
    ((f '' U) ∩ (f '' Uᶜ)) ∩ O = ((f '' K) ∩ (f '' L)) ∩ O := by
  obtain ⟨h₁, h₂⟩ := isolated_patch_images hUK hVL hKL hpre
  have hset (A B : Set Y) : (A ∩ B) ∩ O = (A ∩ O) ∩ (B ∩ O) := by
    ext y
    simp only [mem_inter_iff]
    tauto
  rw [hset, h₁, h₂, ← hset]

end Wikipedia.HopfProblem.DegreeCollapse.SelectiveSheet
