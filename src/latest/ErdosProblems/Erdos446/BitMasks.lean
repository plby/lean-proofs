/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SlotOrder

/-!
# Erdős Problem 446: bit masks and their last difference

Each ordered divisor pair is represented by two Boolean masks on the prime
slots.  A non-diagonal pair has a last differing slot in lexicographic order.
Once that slot is fixed, the first mask is arbitrary everywhere and the
second mask is needed only through that slot; all later second bits equal the
first bits.  This gives the sharp bound `2^(B + L + 1)` where `B` is the total
number of slots and `L` the number preceding the distinguished slot.
-/

namespace Erdos446

open Finset
open scoped BigOperators

def DiagonalBits {k : ℕ} {b : ℕ → ℕ}
    (c : BlockSlot k b → Bool × Bool) : Prop :=
  ∀ s, (c s).1 = (c s).2

def LastDifferenceAt {k : ℕ} {b : ℕ → ℕ} (s : BlockSlot k b)
    (c : BlockSlot k b → Bool × Bool) : Prop :=
  (c s).1 ≠ (c s).2 ∧
    ∀ t, toLex s < toLex t → (c t).1 = (c t).2

noncomputable def diagonalBitMasks (k : ℕ) (b : ℕ → ℕ) :
    Finset (BlockSlot k b → Bool × Bool) := by
  classical
  exact Finset.univ.filter DiagonalBits

noncomputable def nondiagonalBitMasks (k : ℕ) (b : ℕ → ℕ) :
    Finset (BlockSlot k b → Bool × Bool) := by
  classical
  exact Finset.univ.filter (fun c ↦ ¬DiagonalBits c)

noncomputable def lastDifferenceBitMasks {k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b) : Finset (BlockSlot k b → Bool × Bool) := by
  classical
  exact Finset.univ.filter (LastDifferenceAt s)

private abbrev LastDifferenceEncoding {k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b) :=
  (BlockSlot k b → Bool) ×
    ({t : Lex (BlockSlot k b) // t ≤ toLex s} → Bool)

private def lastDifferenceEncoding {k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b)
    (x : {c : BlockSlot k b → Bool × Bool // LastDifferenceAt s c}) :
    LastDifferenceEncoding s :=
  (fun t ↦ (x.1 t).1,
    fun t ↦ (x.1 (ofLex t.1)).2)

private theorem lastDifferenceEncoding_injective {k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b) : Function.Injective (lastDifferenceEncoding s) := by
  intro x y hxy
  apply Subtype.ext
  funext t
  apply Prod.ext
  · exact congrFun (congrArg Prod.fst hxy) t
  · by_cases hle : toLex t ≤ toLex s
    · have hsecond := congrFun (congrArg Prod.snd hxy) ⟨toLex t, hle⟩
      change (x.1 (ofLex (toLex t))).2 =
        (y.1 (ofLex (toLex t))).2 at hsecond
      simpa only [ofLex_toLex] using hsecond
    · have hst : toLex s < toLex t := lt_of_not_ge hle
      rw [← x.2.2 t hst, ← y.2.2 t hst]
      exact congrFun (congrArg Prod.fst hxy) t

theorem card_lastDifferenceBitMasks_le {k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b) :
    (lastDifferenceBitMasks s).card ≤
      2 ^ (slotCount k b +
        ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) := by
  classical
  have hinj := lastDifferenceEncoding_injective s
  calc
    (lastDifferenceBitMasks s).card =
        Fintype.card {c : BlockSlot k b → Bool × Bool //
          LastDifferenceAt s c} := by
      rw [Fintype.card_subtype]
      rfl
    _ ≤ Fintype.card (LastDifferenceEncoding s) :=
      Fintype.card_le_of_injective (lastDifferenceEncoding s) hinj
    _ = 2 ^ (slotCount k b +
        ((∑ i ∈ Finset.range s.1.val, b i) + s.2.val) + 1) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
        card_blockSlot, card_slotsAtMost, card_earlierSlots]
      simp only [Fintype.card_bool]
      rw [← pow_add]
      congr 1

private def diagonalEncoding {k : ℕ} {b : ℕ → ℕ}
    (x : {c : BlockSlot k b → Bool × Bool // DiagonalBits c}) :
    BlockSlot k b → Bool := fun s ↦ (x.1 s).1

private theorem diagonalEncoding_injective {k : ℕ} {b : ℕ → ℕ} :
    Function.Injective (diagonalEncoding (k := k) (b := b)) := by
  intro x y hxy
  apply Subtype.ext
  funext s
  apply Prod.ext
  · exact congrFun hxy s
  · rw [← x.2 s, ← y.2 s]
    exact congrFun hxy s

theorem card_diagonalBitMasks_le (k : ℕ) (b : ℕ → ℕ) :
    (diagonalBitMasks k b).card ≤ 2 ^ slotCount k b := by
  classical
  calc
    (diagonalBitMasks k b).card =
        Fintype.card {c : BlockSlot k b → Bool × Bool // DiagonalBits c} := by
      rw [Fintype.card_subtype]
      rfl
    _ ≤ Fintype.card (BlockSlot k b → Bool) :=
      Fintype.card_le_of_injective diagonalEncoding diagonalEncoding_injective
    _ = 2 ^ slotCount k b := by
      rw [Fintype.card_fun, card_blockSlot]
      simp

/-- Every non-diagonal mask belongs to the class indexed by its last
differing slot. -/
theorem nondiagonalBitMasks_subset_biUnion_last (k : ℕ) (b : ℕ → ℕ) :
    nondiagonalBitMasks k b ⊆
      (Finset.univ : Finset (BlockSlot k b)).biUnion
        lastDifferenceBitMasks := by
  classical
  intro c hc
  rw [nondiagonalBitMasks, Finset.mem_filter] at hc
  have hex : ∃ t : Lex (BlockSlot k b),
      (c (ofLex t)).1 ≠ (c (ofLex t)).2 := by
    by_contra h
    push_neg at h
    exact hc.2 (fun s ↦ by simpa using h (toLex s))
  let D : Finset (Lex (BlockSlot k b)) :=
    Finset.univ.filter fun t ↦ (c (ofLex t)).1 ≠ (c (ofLex t)).2
  have hD : D.Nonempty := by
    obtain ⟨t, ht⟩ := hex
    exact ⟨t, by simp [D, ht]⟩
  let tmax := D.max' hD
  let smax : BlockSlot k b := ofLex tmax
  have hsmaxDiff : (c smax).1 ≠ (c smax).2 := by
    have htmem := Finset.max'_mem D hD
    simpa [D, smax, tmax] using (Finset.mem_filter.mp htmem).2
  have hsmaxLast : ∀ t, toLex smax < toLex t → (c t).1 = (c t).2 := by
    intro t hst
    by_contra hdiff
    have htD : toLex t ∈ D := by simp [D, hdiff]
    have hle := Finset.le_max' D (toLex t) htD
    have heq : toLex smax = tmax := by simp [smax]
    rw [heq] at hst
    exact (not_lt_of_ge hle) hst
  apply Finset.mem_biUnion.mpr
  refine ⟨smax, Finset.mem_univ _, ?_⟩
  rw [lastDifferenceBitMasks, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hsmaxDiff, hsmaxLast⟩

end Erdos446
