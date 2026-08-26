/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Encoding arbitrary finite coordinate orders by ranks bounded by the dimension.
Informal source: the ordering count in BBMST equation (30).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameDivisorProfiles
import ErdosProblems.Erdos1189.SqrtPrefixSums

namespace Erdos1189

open Finset

variable {β : Type*} [Fintype β]

def compressedRank (rank : β → ℕ) (i : β) : ℕ := (rankPrefix rank i).card

lemma rankPrefix_mono (rank : β → ℕ) {i j : β} (hij : rank i ≤ rank j) :
    rankPrefix rank i ⊆ rankPrefix rank j := by
  intro t ht
  exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp ht).2).trans_le hij⟩

lemma compressedRank_lt_iff (rank : β → ℕ) (i j : β) :
    compressedRank rank i < compressedRank rank j ↔ rank i < rank j := by
  constructor
  · intro h
    by_contra hnot
    have hsub := rankPrefix_mono rank (le_of_not_gt hnot)
    have hcard := card_le_card hsub
    exact Nat.not_lt_of_ge hcard h
  · intro hij
    apply card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨rankPrefix_mono rank hij.le, ?_⟩
    intro heq
    have hi : i ∈ rankPrefix rank j := mem_filter.mpr ⟨mem_univ _, hij⟩
    rw [← heq] at hi
    exact Nat.lt_irrefl _ (mem_filter.mp hi).2

lemma compressedRank_injective (rank : β → ℕ) (hinj : Function.Injective rank) :
    Function.Injective (compressedRank rank) := by
  intro i j hij
  apply hinj
  rcases lt_trichotomy (rank i) (rank j) with hlt | heq | hgt
  · have h := (compressedRank_lt_iff rank i j).mpr hlt
    omega
  · exact heq
  · have h := (compressedRank_lt_iff rank j i).mpr hgt
    omega

lemma compressedRank_lt_card (rank : β → ℕ) (i : β) :
    compressedRank rank i < Fintype.card β := by
  have hsub : rankPrefix rank i ⊂ univ := Finset.ssubset_iff_subset_ne.mpr
    ⟨subset_univ _, fun heq => by
      have hi : i ∈ rankPrefix rank i := heq.symm ▸ mem_univ i
      exact Nat.lt_irrefl _ (mem_filter.mp hi).2⟩
  simpa only [card_univ, compressedRank] using card_lt_card hsub

def boundedRank (rank : β → ℕ) (i : β) : Fin (Fintype.card β) :=
  ⟨compressedRank rank i, compressedRank_lt_card rank i⟩

lemma rankPrefix_compressedRank (rank : β → ℕ) (i : β) :
    rankPrefix (compressedRank rank) i = rankPrefix rank i := by
  ext j
  simp only [rankPrefix, mem_filter, mem_univ, true_and, compressedRank_lt_iff]

lemma prefixWeight_compressedRank (S : Finset β) (rank w : β → ℕ) (i : β) :
    prefixWeight S (compressedRank rank) w i = prefixWeight S rank w i := by
  unfold prefixWeight
  congr 1
  ext j
  simp only [mem_filter, compressedRank_lt_iff]

end Erdos1189
