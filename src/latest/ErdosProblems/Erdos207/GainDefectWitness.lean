/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatWitness

/-! # Indexed witnesses and exact remainder sizes for the fourth nibble moment -/

namespace Erdos207

open Finset

noncomputable section

structure GainDefectWitness
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W)) (T : W) (z : ℕ) where
  first : Finset W
  second : Finset W
  omitted : Finset W
  first_mem : first ∈ F
  second_mem : second ∈ G
  root_mem : T ∈ first
  omitted_subset : omitted ⊆ first.erase T
  omitted_card : omitted.card = z
  second_root_card : (second ∩ insert T omitted).card = 2
  not_subset : ¬ second ⊆ first

instance {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) : Finite (GainDefectWitness F G T z) :=
  Finite.of_injective (fun w : GainDefectWitness F G T z ↦ (w.first, w.second, w.omitted))
    (by intro w u h; cases w; cases u; simp_all)

noncomputable instance {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T : W) (z : ℕ) : Fintype (GainDefectWitness F G T z) :=
  Fintype.ofFinite _

namespace GainDefectWitness

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T : W} {z : ℕ}

def omittedRoot (w : GainDefectWitness F G T z) : Finset W := insert T w.omitted
def leftRemainder (w : GainDefectWitness F G T z) : Finset W := w.first \ w.omittedRoot
def rightRemainder (w : GainDefectWitness F G T z) : Finset W := w.second \ w.omittedRoot
def remainder (w : GainDefectWitness F G T z) : Finset W := w.leftRemainder ∪ w.rightRemainder

theorem root_not_mem_omitted (w : GainDefectWitness F G T z) : T ∉ w.omitted := by
  intro h
  exact (mem_erase.mp (w.omitted_subset h)).1 rfl

theorem omittedRoot_subset_first (w : GainDefectWitness F G T z) : w.omittedRoot ⊆ w.first :=
  insert_subset w.root_mem (w.omitted_subset.trans (erase_subset T w.first))

theorem omittedRoot_card (w : GainDefectWitness F G T z) : w.omittedRoot.card = z + 1 := by
  rw [omittedRoot, card_insert_of_notMem w.root_not_mem_omitted, w.omitted_card]

theorem leftRemainder_card (w : GainDefectWitness F G T z) :
    w.leftRemainder.card = w.first.card - (z + 1) := by
  rw [leftRemainder, card_sdiff_of_subset w.omittedRoot_subset_first, w.omittedRoot_card]

theorem rightRemainder_card (w : GainDefectWitness F G T z) :
    w.rightRemainder.card = w.second.card - 2 := by
  rw [rightRemainder, card_sdiff, inter_comm, omittedRoot, w.second_root_card]

theorem remainder_eq_sdiff (w : GainDefectWitness F G T z) :
    w.remainder = (w.first ∪ w.second) \ w.omittedRoot := by
  ext x
  simp only [remainder, leftRemainder, rightRemainder, mem_union, mem_sdiff]
  tauto

theorem remainder_card (w : GainDefectWitness F G T z) :
    w.remainder.card = (w.first.card - (z + 1)) + (w.second.card - 2) -
      (w.leftRemainder ∩ w.rightRemainder).card := by
  have h := card_union_add_card_inter w.leftRemainder w.rightRemainder
  rw [w.leftRemainder_card, w.rightRemainder_card] at h
  change (w.leftRemainder ∪ w.rightRemainder).card = _
  omega

theorem remainder_sdiff_card (w : GainDefectWitness F G T z) (H : Finset W)
    (hH : H ⊆ w.remainder) :
    (w.remainder \ H).card = (w.first.card - (z + 1)) + (w.second.card - 2) -
      (w.leftRemainder ∩ w.rightRemainder).card - H.card := by
  rw [card_sdiff_of_subset hH, w.remainder_card]

theorem disjoint_omittedRoot_remainder (w : GainDefectWitness F G T z) :
    Disjoint w.omittedRoot w.remainder := by
  rw [w.remainder_eq_sdiff]
  exact disjoint_sdiff_self_right

theorem root_not_mem_remainder (w : GainDefectWitness F G T z) : T ∉ w.remainder :=
  fun h ↦ disjoint_left.mp w.disjoint_omittedRoot_remainder (mem_insert_self _ _) h

theorem inter_card (w : GainDefectWitness F G T z) :
    (w.first ∩ w.second).card = (w.leftRemainder ∩ w.rightRemainder).card + 2 := by
  have hset : (w.first ∩ w.second) \ w.omittedRoot = w.leftRemainder ∩ w.rightRemainder := by
    ext x
    simp only [mem_sdiff, mem_inter, leftRemainder, rightRemainder]
    tauto
  have hroot : (w.first ∩ w.second) ∩ w.omittedRoot = w.second ∩ w.omittedRoot := by
    ext x
    simp only [mem_inter]
    constructor
    · tauto
    · rintro ⟨hxS, hxO⟩
      exact ⟨⟨w.omittedRoot_subset_first hxO, hxS⟩, hxO⟩
  have h := card_sdiff_add_card_inter (w.first ∩ w.second) w.omittedRoot
  rw [hset, hroot, omittedRoot, w.second_root_card] at h
  omega

end GainDefectWitness

end

end Erdos207
