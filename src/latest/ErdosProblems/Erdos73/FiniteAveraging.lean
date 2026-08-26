/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.IntervalSelection
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Finite averaging for common pregrill columns

All estimates are integral. No probability or asymptotic result is used.
-/

namespace Erdos73

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- There is a prescribed-size subset whose mean weight is no larger
than the mean weight of the full finite set, without division. -/
theorem exists_subset_card_eq_sum_average_le
    {I : Type*} (s : Finset I) (w : I → ℕ) (k : ℕ) (hk : k ≤ s.card) :
    ∃ J ⊆ s, J.card = k ∧ s.card * (∑ i ∈ J, w i) ≤ k * (∑ i ∈ s, w i) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases heq : k = s.card
    · exact ⟨s, Finset.Subset.refl _, heq.symm, by rw [heq]⟩
    · have hlt : k < s.card := lt_of_le_of_ne hk heq
      have hs : s.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le k) hlt)
      obtain ⟨i, hi, hmax⟩ := s.exists_max_image w hs
      have hecard := Finset.card_erase_add_one hi
      obtain ⟨J, hJ, hJcard, hJweight⟩ :=
        ih (s.erase i) (Finset.erase_ssubset hi) (by omega)
      have hJmax : (∑ j ∈ J, w j) ≤ k * w i := by
        calc
          (∑ j ∈ J, w j) ≤ ∑ _j ∈ J, w i :=
            Finset.sum_le_sum fun j hj ↦ hmax j (Finset.mem_of_mem_erase (hJ hj))
          _ = k * w i := by simp [hJcard]
      refine ⟨J, hJ.trans (Finset.erase_subset _ _), hJcard, ?_⟩
      calc
        s.card * (∑ j ∈ J, w j) =
            (s.erase i).card * (∑ j ∈ J, w j) + (∑ j ∈ J, w j) := by
          rw [← hecard, Nat.add_mul, Nat.one_mul]
        _ ≤ k * (∑ j ∈ s.erase i, w j) + k * w i := Nat.add_le_add hJweight hJmax
        _ = k * (∑ j ∈ s, w j) := by
          rw [← Nat.mul_add]
          exact congrArg (fun z ↦ k * z) (Finset.sum_erase_add s w hi)

/-- When each column misses at most a `1/(2*k)` fraction of the rows,
there are `k` distinct rows simultaneously meeting at least half the
columns. The statement uses only multiplication of natural numbers. -/
theorem exists_rows_common_half_columns
    {I K : Type*} [Fintype I] [Fintype K] (miss : I → K → Prop)
    (k : ℕ) (hkpos : 0 < k) (hk : k ≤ Fintype.card I)
    (hmiss : ∀ j, 2 * k * (Finset.univ.filter fun i ↦ miss i j).card ≤ Fintype.card I) :
    ∃ J : Finset I, ∃ C : Finset K,
      J.card = k ∧ Fintype.card K ≤ 2 * C.card ∧
        ∀ i ∈ J, ∀ j ∈ C, ¬ miss i j := by
  let w : I → ℕ := fun i ↦ (Finset.univ.filter fun j ↦ miss i j).card
  obtain ⟨J, _, hJcard, hJweight⟩ :=
    exists_subset_card_eq_sum_average_le Finset.univ w k (by simpa using hk)
  let bad : Finset K := J.biUnion fun i ↦ Finset.univ.filter fun j ↦ miss i j
  let C : Finset K := Finset.univ \ bad
  have hbad : bad.card ≤ ∑ i ∈ J, w i := Finset.card_biUnion_le
  have htotal : (∑ i : I, w i) =
      ∑ j : K, (Finset.univ.filter fun i ↦ miss i j).card := by
    exact Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := Finset.univ) (t := Finset.univ) miss
  have hweighted : Fintype.card I * bad.card ≤ k * (∑ i : I, w i) :=
    (Nat.mul_le_mul_left _ hbad).trans (by simpa using hJweight)
  have hdouble : Fintype.card I * (2 * bad.card) ≤ Fintype.card I * Fintype.card K := by
    calc
      Fintype.card I * (2 * bad.card) = 2 * (Fintype.card I * bad.card) := by ac_rfl
      _ ≤ 2 * (k * (∑ i : I, w i)) := Nat.mul_le_mul_left _ hweighted
      _ = ∑ j : K, 2 * k * (Finset.univ.filter fun i ↦ miss i j).card := by
        rw [htotal, ← Nat.mul_assoc, Finset.mul_sum]
      _ ≤ ∑ _j : K, Fintype.card I := Finset.sum_le_sum fun j _ ↦ hmiss j
      _ = Fintype.card I * Fintype.card K := by simp [Nat.mul_comm]
  have htwobad : 2 * bad.card ≤ Fintype.card K :=
    Nat.le_of_mul_le_mul_left hdouble (hkpos.trans_le hk)
  have hcardC : C.card + bad.card = Fintype.card K := by
    simpa [C] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
  refine ⟨J, C, hJcard, by omega, ?_⟩
  intro i hi j hj hij
  exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_biUnion.mpr
    ⟨i, hi, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩)

end
end Erdos73
