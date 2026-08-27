/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.DistinctEqualRemainders

/-! # The sharp uniform W2 count for genuine Erdős configurations -/

namespace Erdos207

open Finset

noncomputable section

theorem genuine_distinctEqualRemainderPairs_card_le_span
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {j : ℕ} (T T' : TripleOn V)
    (hconfig : ∀ E ∈ F, IsErdosConfigOn j E) (hj : 5 ≤ j) :
    (distinctEqualRemainderPairs F T T').card ≤
      (tripleSystemsExtendingWithSpan {T, T'} j).card := by
  apply card_le_card_of_injOn (fun p ↦ insert T' p.1)
  · intro p hp
    have h := mem_distinctEqualRemainderPairs_iff.mp hp
    have hspan := genuine_distinctEqualRemainderPairs_span_eq hconfig hj hp
    have hT'sub : T'.1 ⊆ verticesOn p.1 := by
      rw [hspan]
      intro x hx
      exact mem_biUnion.mpr ⟨T', h.2.2.2.2.1, hx⟩
    have hspanInsert : verticesOn (insert T' p.1) = verticesOn p.1 := by
      simp only [verticesOn, biUnion_insert]
      exact union_eq_right.mpr hT'sub
    apply mem_tripleSystemsExtendingWithSpan_iff.mpr
    refine ⟨?_, ?_⟩
    · exact insert_subset (mem_insert_of_mem h.2.2.2.1) (singleton_subset_iff.mpr (mem_insert_self _ _))
    · rw [hspanInsert, IsErdosConfig.vertices_card_eq (hconfig p.1 h.1) hj]
  · intro p hp q hq heq
    have hfirst : p.1 = q.1 := by
      have herase := congrArg (fun C : TripleSystemOn V ↦ C.erase T') heq
      simpa [distinctEqualRemainderPairs_cross_not_mem hp |>.1,
        distinctEqualRemainderPairs_cross_not_mem hq |>.1] using herase
    exact distinctEqualRemainderPairs_fst_injOn F T T' hp hq hfirst

theorem card_tripleSystemsExtendingWithSpan_le_of_four_le_root_span
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : TripleSystemOn V) (j : ℕ) (hroot : 4 ≤ (verticesOn R).card) :
    (tripleSystemsExtendingWithSpan R j).card ≤
      (2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4) := by
  have hbase : (univ \ verticesOn R : Finset V).card + 1 ≤ Fintype.card V + 1 :=
    Nat.add_le_add_right (card_le_univ _) 1
  have hexp : j - (verticesOn R).card ≤ j - 4 := by omega
  have hpow : ((univ \ verticesOn R : Finset V).card + 1) ^
      (j - (verticesOn R).card) ≤ (Fintype.card V + 1) ^ (j - 4) := by
    exact (pow_le_pow_left₀ zero_le hbase _).trans
      (pow_le_pow_right' (by omega) hexp)
  refine (card_tripleSystemsExtendingWithSpan_le R j).trans ?_
  rw [mul_assoc]
  apply Nat.mul_le_mul_left
  exact Nat.mul_le_mul (by omega) hpow

theorem card_genuine_distinctEqualRemainderPairs_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {j : ℕ} (T T' : TripleOn V)
    (hconfig : ∀ E ∈ F, IsErdosConfigOn j E) (hj : 5 ≤ j) :
    (distinctEqualRemainderPairs F T T').card ≤
      (2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 4) := by
  by_cases hTT' : T = T'
  · subst T'
    simp
  · exact (genuine_distinctEqualRemainderPairs_card_le_span T T' hconfig hj).trans
      (card_tripleSystemsExtendingWithSpan_le_of_four_le_root_span {T, T'} j
        (four_le_vertices_pair_of_ne hTT'))

end

end Erdos207
