import ErdosProblems.Erdos421.CollisionCounts

/-! # Removing the solutions with coordinate repetitions -/

namespace Erdos421

noncomputable def badVinogradovSolutions (s k N : ℕ) :
    Finset ((Fin s → Fin N) × (Fin s → Fin N)) := by
  classical
  exact (vinogradovSolutions s k N 0).filter
    (fun p ↦ ¬Function.Injective p.1 ∨ ¬Function.Injective p.2)

noncomputable def distinctVinogradovSolutions (s k N : ℕ) :
    Finset ((Fin s → Fin N) × (Fin s → Fin N)) := by
  classical
  exact (vinogradovSolutions s k N 0).filter
    (fun p ↦ Function.Injective p.1 ∧ Function.Injective p.2)

open scoped Classical in
theorem left_nondistinct_card_le (n k N : ℕ) :
    ((vinogradovSolutions (n + 2) k N 0).filter (fun p ↦ ¬Function.Injective p.1)).card ≤
      (n + 2) * (n + 1) * repeatedIntegerCount n k N := by
  classical
  let U := (Finset.univ : Finset (Fin (n + 2))).offDiag
  let T (ij : Fin (n + 2) × Fin (n + 2)) :=
    (vinogradovSolutions (n + 2) k N 0).filter (fun p ↦ p.1 ij.1 = p.1 ij.2)
  have hsub : (vinogradovSolutions (n + 2) k N 0).filter
      (fun p ↦ ¬Function.Injective p.1) ⊆ U.biUnion T := by
    intro p hp
    obtain ⟨hpS, hbad⟩ := Finset.mem_filter.mp hp
    simp only [Function.Injective, not_forall] at hbad
    obtain ⟨i, j, he, hij⟩ := hbad
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩, Finset.mem_filter.mpr ⟨hpS, he⟩⟩
  calc
    _ ≤ (U.biUnion T).card := Finset.card_le_card hsub
    _ ≤ ∑ ij ∈ U, (T ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ U, repeatedIntegerCount n k N := by
      apply Finset.sum_le_sum
      intro ij hij
      exact left_coordinate_collision_card_le n k N ij.1 ij.2 (Finset.mem_offDiag.mp hij).2.2
    _ = (n + 2) * (n + 1) * repeatedIntegerCount n k N := by
      rw [Finset.sum_const, smul_eq_mul]
      simp only [U, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      congr 1
      calc
        _ = (n + 2) * ((n + 2) - 1) := by rw [Nat.mul_sub_left_distrib, mul_one]
        _ = (n + 2) * (n + 1) := by congr 1

open scoped Classical in
theorem right_nondistinct_card_le (n k N : ℕ) :
    ((vinogradovSolutions (n + 2) k N 0).filter (fun p ↦ ¬Function.Injective p.2)).card ≤
      (n + 2) * (n + 1) * repeatedIntegerCount n k N := by
  classical
  apply le_trans _ (left_nondistinct_card_le n k N)
  apply Finset.card_le_card_of_injOn Prod.swap
  · intro p hp
    obtain ⟨hpS, hpbad⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hpbad⟩
    apply sub_eq_zero.mpr
    exact (sub_eq_zero.mp (Finset.mem_filter.mp hpS).2).symm
  · exact fun _ _ _ _ h ↦ Prod.swap_injective h

theorem badVinogradovSolutions_card_le (n k N : ℕ) :
    (badVinogradovSolutions (n + 2) k N).card ≤
      2 * ((n + 2) * (n + 1)) * repeatedIntegerCount n k N := by
  classical
  unfold badVinogradovSolutions
  rw [Finset.filter_or]
  apply le_trans (Finset.card_union_le _ _)
  have hl := left_nondistinct_card_le n k N
  have hr := right_nondistinct_card_le n k N
  nlinarith

theorem vinogradovCount_eq_bad_add_distinct (s k N : ℕ) :
    vinogradovCount s k N = (badVinogradovSolutions s k N).card +
      (distinctVinogradovSolutions s k N).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := vinogradovSolutions s k N 0)
    (p := fun p ↦ Function.Injective p.1 ∧ Function.Injective p.2)
  simpa only [not_and_or, vinogradovCount, badVinogradovSolutions, distinctVinogradovSolutions,
    add_comm] using h.symm

/-- Above an explicit interval threshold, the distinct-coordinate solutions
are at least half of all solutions of the complete system. -/
theorem vinogradovCount_le_two_distinct (n k N : ℕ)
    (hN : (4 * ((n + 2) * (n + 1))) ^ 2 < N) :
    vinogradovCount (n + 2) k N ≤ 2 * (distinctVinogradovSolutions (n + 2) k N).card := by
  by_contra h
  have hlt := Nat.lt_of_not_ge h
  have hpart := vinogradovCount_eq_bad_add_distinct (n + 2) k N
  have hb := badVinogradovSolutions_card_le n k N
  have hdom : vinogradovCount (n + 2) k N ≤
      (4 * ((n + 2) * (n + 1))) * repeatedIntegerCount n k N := by
    nlinarith
  have hsmall := repeatedInteger_dominance_forces_small_interval n k N
    (C := ((4 * ((n + 2) * (n + 1)) : ℕ) : ℝ)) (Nat.cast_nonneg _) (by exact_mod_cast hdom)
  have hsmallNat : N ≤ (4 * ((n + 2) * (n + 1))) ^ 2 := by exact_mod_cast hsmall
  exact hN.not_ge hsmallNat

theorem vinogradovCount_le_two_distinct_of_large (s k N : ℕ) (hs : 2 ≤ s)
    (hN : (4 * (s * (s - 1))) ^ 2 < N) :
    vinogradovCount s k N ≤ 2 * (distinctVinogradovSolutions s k N).card := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n + 2 := ⟨s - 2, (Nat.sub_add_cancel hs).symm⟩
  exact vinogradovCount_le_two_distinct n k N (by simpa using hN)

end Erdos421
