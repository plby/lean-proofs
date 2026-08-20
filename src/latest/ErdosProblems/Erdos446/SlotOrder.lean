/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.DistinguishedPrime
import Mathlib.Data.Sigma.Order

/-!
# Erdős Problem 446: lexicographic order of block slots

The largest-difference argument orders slots first by block and then within a
block.  The exact number of slots before `(i,j)` is the sum of the preceding
block sizes plus `j`; this is the exponent responsible for Ford's geometric
bit-mask sum.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The number of slots in a vector class. -/
def slotCount (k : ℕ) (b : ℕ → ℕ) : ℕ :=
  ∑ i : Fin k, b i

theorem card_blockSlot (k : ℕ) (b : ℕ → ℕ) :
    Fintype.card (BlockSlot k b) = slotCount k b := by
  rw [Fintype.card_sigma]
  simp [slotCount]

private theorem card_earlierSlots_fiber {k : ℕ} {b : ℕ → ℕ}
    (s : BlockSlot k b) (i : Fin k) :
    ((Finset.univ : Finset (Fin (b i))).filter
      (fun j ↦ toLex (Sigma.mk i j : BlockSlot k b) < toLex s)).card =
      if i < s.1 then b i else if i = s.1 then s.2.val else 0 := by
  rcases s with ⟨si, sj⟩
  rcases lt_trichotomy i si with hi | hi | hi
  · have hall (j : Fin (b i)) :
        toLex (Sigma.mk i j : BlockSlot k b) < toLex (Sigma.mk si sj) := by
      change Sigma.Lex (fun a b : Fin k ↦ a < b)
        (fun i (x y : Fin (b i)) ↦ x < y) ⟨i, j⟩ ⟨si, sj⟩
      exact @Sigma.Lex.left (Fin k) (fun i : Fin k ↦ Fin (b i))
        (fun a b : Fin k ↦ a < b) (fun _ x y ↦ x < y) i si j sj hi
    simp [hi, hall]
  · subst i
    have hiff (j : Fin (b si)) :
        toLex (Sigma.mk si j : BlockSlot k b) <
          toLex (Sigma.mk si sj) ↔ j < sj := by
      constructor
      · intro h
        cases h with
        | left _ _ hlt => exact (lt_irrefl _ hlt).elim
        | right _ _ hlt => exact hlt
      · intro h
        change Sigma.Lex (fun a b : Fin k ↦ a < b)
          (fun i (x y : Fin (b i)) ↦ x < y) ⟨si, j⟩ ⟨si, sj⟩
        exact @Sigma.Lex.right (Fin k) (fun i : Fin k ↦ Fin (b i))
          (fun a b : Fin k ↦ a < b) (fun _ x y ↦ x < y) si j sj h
    simp only [lt_self_iff_false, ↓reduceIte, hiff]
    simpa [Nat.min_eq_left sj.isLt.le] using
      (Fin.card_filter_val_lt (n := b si) (m := sj.val))
  · have hne : i ≠ si := ne_of_gt hi
    have hnlt : ¬i < si := not_lt_of_ge hi.le
    have hnot (j : Fin (b i)) :
        ¬toLex (Sigma.mk i j : BlockSlot k b) <
          toLex (Sigma.mk si sj) := by
      intro h
      cases h with
      | left _ _ hlt => exact hnlt hlt
      | right _ _ hlt => exact hne rfl
    simp [hne, hnlt, hnot]

/-- Exact cardinality of the strict initial segment preceding a slot. -/
theorem card_earlierSlots {k : ℕ} {b : ℕ → ℕ} (s : BlockSlot k b) :
    Fintype.card {t : Lex (BlockSlot k b) // t < toLex s} =
      (∑ i ∈ Finset.range s.1.val, b i) + s.2.val := by
  rw [Fintype.card_subtype]
  change ((Finset.univ.sigma (fun i : Fin k ↦ Finset.univ)).filter
    (fun t : BlockSlot k b ↦ toLex t < toLex s)).card = _
  rw [Finset.filter_sigma' Finset.univ (fun i : Fin k ↦ Finset.univ)
    (fun i j ↦ toLex (Sigma.mk i j : BlockSlot k b) < toLex s)]
  rw [Finset.card_sigma]
  simp_rw [card_earlierSlots_fiber s]
  have hltSum :
      (∑ i : Fin k, if i < s.1 then b i else 0) =
        ∑ n ∈ Finset.range s.1.val, b n := by
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun i hi ↦ i.val)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_range.mpr hi
    · intro i hi j hj hij
      exact Fin.ext hij
    · intro n hn
      have hnlt : n < s.1.val := Finset.mem_range.mp hn
      let i : Fin k := ⟨n, hnlt.trans s.1.isLt⟩
      refine ⟨i, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnlt
    · intro i hi
      rfl
  calc
    (∑ i : Fin k,
        if i < s.1 then b i else if i = s.1 then s.2.val else 0) =
        (∑ i : Fin k, if i < s.1 then b i else 0) +
          ∑ i : Fin k, if i = s.1 then s.2.val else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rcases lt_trichotomy i s.1 with h | h | h
      · simp [h, ne_of_lt h]
      · subst i
        simp
      · simp [not_lt_of_ge h.le, ne_of_gt h]
    _ = (∑ n ∈ Finset.range s.1.val, b n) + s.2.val := by
      rw [hltSum]
      simp

theorem card_slotsAtMost {k : ℕ} {b : ℕ → ℕ} (s : BlockSlot k b) :
    Fintype.card {t : Lex (BlockSlot k b) // t ≤ toLex s} =
      Fintype.card {t : Lex (BlockSlot k b) // t < toLex s} + 1 := by
  let P : Lex (BlockSlot k b) → Prop := fun t ↦ t < toLex s
  let Q : Lex (BlockSlot k b) → Prop := fun t ↦ t = toLex s
  have hpred : (fun t : Lex (BlockSlot k b) ↦ t ≤ toLex s) =
      fun t ↦ P t ∨ Q t := by
    funext t
    apply propext
    exact le_iff_lt_or_eq
  calc
    Fintype.card {t : Lex (BlockSlot k b) // t ≤ toLex s} =
        Fintype.card {t : Lex (BlockSlot k b) // P t ∨ Q t} :=
      Fintype.card_congr (Equiv.subtypeEquivProp hpred)
    _ = Fintype.card {t : Lex (BlockSlot k b) // P t} +
        Fintype.card {t : Lex (BlockSlot k b) // Q t} := by
      apply Fintype.card_subtype_or_disjoint P Q
      change Disjoint ({t | P t} : Set (Lex (BlockSlot k b)))
        ({t | Q t} : Set (Lex (BlockSlot k b)))
      rw [Set.disjoint_left]
      intro t ht hq
      exact ht.ne hq
    _ = Fintype.card {t : Lex (BlockSlot k b) // t < toLex s} + 1 := by
      simp [P, Q]

end Erdos446
