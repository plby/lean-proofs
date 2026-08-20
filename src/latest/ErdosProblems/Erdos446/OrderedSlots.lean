/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.DivisorSubsets

/-!
# Erdős Problem 446: ordered prime slots

For a vector class with `b i` primes selected from the `i`th block, every
selection can be ordered in `b i !` ways.  This file records the corresponding
dependent array of slots and proves the elementary range and weight identities
needed for Ford's largest-differing-prime argument.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The ordered positions occupied by the selected primes. -/
abbrev BlockSlot (k : ℕ) (b : ℕ → ℕ) :=
  Σ i : Fin k, Fin (b i)

/-- One permutation for the selected primes in every block. -/
abbrev BlockPermutations (k : ℕ) (b : ℕ → ℕ) :=
  ∀ i : Fin k, Equiv.Perm (Fin (b i))

/-- A block choice together with a close pair of subsets of its union. -/
abbrev CloseBlockChoice (M k : ℕ) (b : ℕ → ℕ) :=
  Σ T : ↥(blockChoiceTuples M k b),
    ↥(subsetClosePairs (choiceUnion T.1))

/-- Enumerate every selected block subset in the order prescribed by `σ`. -/
noncomputable def orderedPrime {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) (s : BlockSlot k b) : ℕ :=
  (T.1 s.1).orderEmbOfFin
    ((mem_blockChoiceTuples.mp T.2 s.1).2) (σ s.1 s.2)

/-- The two bits record membership in the two divisor subsets. -/
noncomputable def orderedBits {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b)
    (σ : BlockPermutations k b) (s : BlockSlot k b) : Bool × Bool :=
  (decide (orderedPrime x.1 σ s ∈ x.2.1.1),
    decide (orderedPrime x.1 σ s ∈ x.2.1.2))

theorem orderedPrime_mem_choice {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) (s : BlockSlot k b) :
    orderedPrime T σ s ∈ T.1 s.1 := by
  exact Finset.orderEmbOfFin_mem _ _ _

theorem orderedPrime_mem_block {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) (s : BlockSlot k b) :
    orderedPrime T σ s ∈ primeBlock (M + s.1) :=
  (mem_blockChoiceTuples.mp T.2 s.1).1 (orderedPrime_mem_choice T σ s)

theorem orderedPrime_prime {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) (s : BlockSlot k b) :
    (orderedPrime T σ s).Prime :=
  (mem_primeBlock.mp (orderedPrime_mem_block T σ s)).1

theorem image_orderedPrime_block {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) (i : Fin k) :
    Finset.univ.image (fun j : Fin (b i) ↦
      orderedPrime T σ ⟨i, j⟩) = T.1 i := by
  calc
    Finset.univ.image (fun j : Fin (b i) ↦
        orderedPrime T σ ⟨i, j⟩) =
        Finset.univ.image
          ((T.1 i).orderEmbOfFin
            ((mem_blockChoiceTuples.mp T.2 i).2)) := by
      ext p
      simp only [Finset.mem_image, Finset.mem_univ, true_and,
        orderedPrime]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨σ i j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨(σ i).symm j, by simp⟩
    _ = T.1 i := Finset.image_orderEmbOfFin_univ _ _

theorem prod_orderedPrime_block {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) (i : Fin k) :
    (∏ j : Fin (b i), 1 / (orderedPrime T σ ⟨i, j⟩ : ℝ)) =
      selectionWeight (T.1 i) := by
  rw [selectionWeight]
  rw [← Finset.prod_image
    (s := (Finset.univ : Finset (Fin (b i))))
    (g := fun j : Fin (b i) ↦ orderedPrime T σ ⟨i, j⟩)
    (f := fun p : ℕ ↦ 1 / (p : ℝ))]
  · rw [image_orderedPrime_block]
  · intro x _ y _ hxy
    apply (σ i).injective
    apply ((T.1 i).orderEmbOfFin
      ((mem_blockChoiceTuples.mp T.2 i).2)).injective
    exact hxy

theorem prod_orderedPrime {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) :
    (∏ s : BlockSlot k b, 1 / (orderedPrime T σ s : ℝ)) =
      selectionWeight (choiceUnion T.1) := by
  rw [Fintype.prod_sigma]
  simp_rw [prod_orderedPrime_block T σ]
  exact (selectionWeight_choiceUnion T.2).symm

theorem orderedPrime_injective {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) :
    Function.Injective (orderedPrime T σ) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  have hij : i = j := by
    by_contra hne
    have hdisj := primeBlock_pairwise_disjoint
      (i := M + i) (j := M + j) (by
        intro h
        apply hne
        apply Fin.ext
        omega)
    exact (Finset.disjoint_left.mp hdisj)
      (orderedPrime_mem_block T σ ⟨i, x⟩)
      (hxy ▸ orderedPrime_mem_block T σ ⟨j, y⟩)
  subst j
  have hxy' : x = y := by
    apply (σ i).injective
    apply ((T.1 i).orderEmbOfFin
      ((mem_blockChoiceTuples.mp T.2 i).2)).injective
    exact hxy
  subst y
  rfl

theorem image_orderedPrime {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    (σ : BlockPermutations k b) :
    Finset.univ.image (orderedPrime T σ) = choiceUnion T.1 := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr
      ⟨s.1, Finset.mem_univ _, orderedPrime_mem_choice T σ s⟩
  · intro hp
    obtain ⟨i, hi, hpTi⟩ := Finset.mem_biUnion.mp hp
    have hpImage : p ∈ Finset.univ.image (fun j : Fin (b i) ↦
        orderedPrime T σ ⟨i, j⟩) := by
      rw [image_orderedPrime_block]
      exact hpTi
    obtain ⟨j, hj, hpj⟩ := Finset.mem_image.mp hpImage
    exact Finset.mem_image.mpr ⟨⟨i, j⟩, Finset.mem_univ _, hpj⟩

/-- Recover from an ordered configuration the primes whose selected bit is
`true`. -/
def bitSubset {k : ℕ} {b : ℕ → ℕ}
    (v : BlockSlot k b → ℕ) (c : BlockSlot k b → Bool × Bool)
    (first : Bool) : Finset ℕ :=
  Finset.univ.filter (fun s ↦ if first then (c s).1 else (c s).2) |>.image v

theorem bitSubset_orderedBits_first {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b) (σ : BlockPermutations k b) :
    bitSubset (orderedPrime x.1 σ) (orderedBits x σ) true = x.2.1.1 := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    simpa [bitSubset, orderedBits] using hs
  · intro hp
    have hpUnion : p ∈ choiceUnion x.1.1 :=
      (mem_subsetClosePairs.mp x.2.2).1 hp
    rw [← image_orderedPrime x.1 σ] at hpUnion
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp hpUnion
    refine Finset.mem_image.mpr ⟨s, ?_, hsp⟩
    simpa [bitSubset, orderedBits, hsp] using hp

theorem bitSubset_orderedBits_second {M k : ℕ} {b : ℕ → ℕ}
    (x : CloseBlockChoice M k b) (σ : BlockPermutations k b) :
    bitSubset (orderedPrime x.1 σ) (orderedBits x σ) false = x.2.1.2 := by
  ext p
  constructor
  · intro hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hp
    simpa [bitSubset, orderedBits] using hs
  · intro hp
    have hpUnion : p ∈ choiceUnion x.1.1 :=
      (mem_subsetClosePairs.mp x.2.2).2.1 hp
    rw [← image_orderedPrime x.1 σ] at hpUnion
    obtain ⟨s, hs, hsp⟩ := Finset.mem_image.mp hpUnion
    refine Finset.mem_image.mpr ⟨s, ?_, hsp⟩
    simpa [bitSubset, orderedBits, hsp] using hp

/-- The ordered primes together with their two subset-membership bits. -/
noncomputable def orderedConfiguration {M k : ℕ} {b : ℕ → ℕ}
    (z : CloseBlockChoice M k b × BlockPermutations k b) :
    (BlockSlot k b → ℕ) × (BlockSlot k b → Bool × Bool) :=
  (orderedPrime z.1.1 z.2, orderedBits z.1 z.2)

theorem blockChoice_eq_of_orderedPrime_eq {M k : ℕ} {b : ℕ → ℕ}
    {T U : ↥(blockChoiceTuples M k b)}
    {σ τ : BlockPermutations k b}
    (h : orderedPrime T σ = orderedPrime U τ) : T = U := by
  apply Subtype.ext
  funext i
  rw [← image_orderedPrime_block T σ i,
    ← image_orderedPrime_block U τ i]
  congr 1
  funext j
  exact congrFun h ⟨i, j⟩

theorem blockPermutations_eq_of_orderedPrime_eq {M k : ℕ} {b : ℕ → ℕ}
    (T : ↥(blockChoiceTuples M k b))
    {σ τ : BlockPermutations k b}
    (h : orderedPrime T σ = orderedPrime T τ) : σ = τ := by
  funext i
  apply Equiv.ext
  intro j
  apply ((T.1 i).orderEmbOfFin
    ((mem_blockChoiceTuples.mp T.2 i).2)).injective
  exact congrFun h ⟨i, j⟩

theorem orderedConfiguration_injective {M k : ℕ} {b : ℕ → ℕ} :
    Function.Injective
      (orderedConfiguration (M := M) (k := k) (b := b)) := by
  rintro ⟨⟨T, DE⟩, σ⟩ ⟨⟨U, EF⟩, τ⟩ hxy
  have hprime : orderedPrime T σ = orderedPrime U τ :=
    congrArg Prod.fst hxy
  have hbits : orderedBits ⟨T, DE⟩ σ = orderedBits ⟨U, EF⟩ τ :=
    congrArg Prod.snd hxy
  have hT : T = U := blockChoice_eq_of_orderedPrime_eq hprime
  subst U
  have hDEval : DE.1 = EF.1 := by
    apply Prod.ext
    · rw [← bitSubset_orderedBits_first ⟨T, DE⟩ σ,
        ← bitSubset_orderedBits_first ⟨T, EF⟩ τ, hprime, hbits]
    · rw [← bitSubset_orderedBits_second ⟨T, DE⟩ σ,
        ← bitSubset_orderedBits_second ⟨T, EF⟩ τ, hprime, hbits]
  have hDE : DE = EF := Subtype.ext hDEval
  subst EF
  have hστ : σ = τ := blockPermutations_eq_of_orderedPrime_eq T hprime
  subst τ
  rfl

end Erdos446
