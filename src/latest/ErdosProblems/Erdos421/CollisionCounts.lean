import ErdosProblems.Erdos421.TupleCollision

/-! # Bounding the union of coordinate collisions -/

namespace Erdos421

theorem left_coordinate_collision_card_le (n k N : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) :
    ((vinogradovSolutions (n + 2) k N 0).filter (fun p ↦ p.1 i = p.1 j)).card ≤
      repeatedIntegerCount n k N := by
  classical
  obtain ⟨e, he0, he1⟩ := exists_perm_two_points (Fin.natAdd n (0 : Fin 2))
    (Fin.natAdd n (1 : Fin 2)) i j (by simp) hij
  let f : ((Fin (n + 2) → Fin N) × (Fin (n + 2) → Fin N)) →
      ((Fin n → Fin N) × Fin N) × (Fin (n + 2) → Fin N) :=
    fun p ↦ (collisionData p.1 e, p.2)
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    obtain ⟨hpS, hpij⟩ := Finset.mem_filter.mp hp
    have hce : p.1 (e (Fin.natAdd n 0)) = p.1 (e (Fin.natAdd n 1)) := by
      rw [he0, he1]
      exact hpij
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change vinogradovSums k (repeatTuple (collisionData p.1 e)) = vinogradovSums k p.2
    rw [repeatTuple_collisionData p.1 e hce, vinogradovSums_comp_perm]
    exact sub_eq_zero.mp (Finset.mem_filter.mp hpS).2
  · intro p hp t ht h
    apply Prod.ext
    · apply collisionData_injective_on e
      · change p.1 (e (Fin.natAdd n 0)) = p.1 (e (Fin.natAdd n 1))
        rw [he0, he1]
        exact (Finset.mem_filter.mp hp).2
      · change t.1 (e (Fin.natAdd n 0)) = t.1 (e (Fin.natAdd n 1))
        rw [he0, he1]
        exact (Finset.mem_filter.mp ht).2
      · exact congrArg Prod.fst h
    · exact congrArg (fun z : ((Fin n → Fin N) × Fin N) × (Fin (n + 2) → Fin N) ↦ z.2) h

theorem right_coordinate_collision_card_le (n k N : ℕ) (i j : Fin (n + 2)) (hij : i ≠ j) :
    ((vinogradovSolutions (n + 2) k N 0).filter (fun p ↦ p.2 i = p.2 j)).card ≤
      repeatedIntegerCount n k N := by
  apply le_trans _ (left_coordinate_collision_card_le n k N i j hij)
  apply Finset.card_le_card_of_injOn Prod.swap
  · intro p hp
    obtain ⟨hpS, hpij⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hpij⟩
    apply sub_eq_zero.mpr
    exact (sub_eq_zero.mp (Finset.mem_filter.mp hpS).2).symm
  · exact fun _ _ _ _ h ↦ Prod.swap_injective h

end Erdos421
