import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionRetraction

/-!
# Straightening a homotopy relative to an inclusion

A homotopy on the ambient space can be made stationary on the included
space if its boundary paths have a jointly continuous contraction fixing
their endpoints. Homotopy extension is applied to the compact-open path
space. The extended endpoint motions are then concatenated to retain the
original ambient endpoints exactly.
-/

noncomputable section

universe u

open CategoryTheory unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem exists_relative_of_boundary_contraction {A B Z : TopCat.{u}}
    (i : A ⟶ B) (hi : HasHomotopyExtension i) {f₀ f₁ : C(B, Z)}
    (H : f₀.Homotopy f₁) (K : C(I × A, C(I, Z)))
    (hK0 : ∀ a, K (0, a) = PushoutHomotopy.familyPaths H.toContinuousMap (i a))
    (hK1 : ∀ a t, K (1, a) t = f₀ (i a))
    (hKe0 : ∀ s a, K (s, a) 0 = f₀ (i a))
    (hKe1 : ∀ s a, K (s, a) 1 = f₁ (i a)) :
    Nonempty (f₀.HomotopyRel f₁ (Set.range i)) := by
  obtain ⟨L, hL0, hLi⟩ := hi (TopCat.of C(I, Z))
    (PushoutHomotopy.familyPaths H.toContinuousMap).hom K hK0
  let last := L.comp ⟨fun b ↦ (1, b), continuous_const.prodMk continuous_id⟩
  let ev : I → C(C(I, Z), Z) := fun t ↦ ⟨fun p ↦ p t, continuous_eval_const t⟩
  let f₀' : C(B, Z) := (ev 0).comp last
  let f₁' : C(B, Z) := (ev 1).comp last
  let H₀ : f₀.HomotopyRel f₀' (Set.range i) :=
    { toContinuousMap := (ev 0).comp L
      map_zero_left := by
        intro b
        change L (0, b) 0 = f₀ b
        rw [hL0]
        exact H.map_zero_left b
      map_one_left := fun _ ↦ rfl
      prop' := by
        rintro t _ ⟨a, rfl⟩
        change L (t, i a) 0 = f₀ (i a)
        rw [hLi]
        exact hKe0 t a }
  let H₁ : f₁.HomotopyRel f₁' (Set.range i) :=
    { toContinuousMap := (ev 1).comp L
      map_zero_left := by
        intro b
        change L (0, b) 1 = f₁ b
        rw [hL0]
        exact H.map_one_left b
      map_one_left := fun _ ↦ rfl
      prop' := by
        rintro t _ ⟨a, rfl⟩
        change L (t, i a) 1 = f₁ (i a)
        rw [hLi]
        exact hKe1 t a }
  let M : f₀'.HomotopyRel f₁' (Set.range i) :=
    { toContinuousMap := last.uncurry.comp ⟨Prod.swap, continuous_swap⟩
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl
      prop' := by
        rintro t _ ⟨a, rfl⟩
        change L (1, i a) t = L (1, i a) 0
        rw [hLi, hK1, hK1] }
  exact ⟨(H₀.trans M).trans H₁.symm⟩

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
