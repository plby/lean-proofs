/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TwoFamilyRootExposure

/-! # Indexed two-configuration witnesses for the third nibble moment -/

namespace Erdos207

open Finset

noncomputable section

/-- Source data `(bridge, first, second)`. Cross-root exclusions still allow
the two fixed roots to be equal, but the configurations must be distinct. -/
structure CommonThreatWitness
    {W : Type*} [DecidableEq W] (F G : Finset (Finset W)) (T T' : W) where
  bridge : W
  first : Finset W
  second : Finset W
  first_mem : first ∈ F
  second_mem : second ∈ G
  first_root : T ∈ first
  second_root : T' ∈ second
  bridge_first : bridge ∈ first
  bridge_second : bridge ∈ second
  bridge_ne_first : bridge ≠ T
  bridge_ne_second : bridge ≠ T'
  first_cross : T' ∈ first → T' = T
  second_cross : T ∈ second → T = T'
  different : first ≠ second

instance {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) : Finite (CommonThreatWitness F G T T') :=
  Finite.of_injective (fun w : CommonThreatWitness F G T T' ↦ (w.bridge, w.first, w.second))
    (by intro w z h; cases w; cases z; simp_all)

noncomputable instance {W : Type*} [Fintype W] [DecidableEq W]
    (F G : Finset (Finset W)) (T T' : W) : Fintype (CommonThreatWitness F G T T') :=
  Fintype.ofFinite _

namespace CommonThreatWitness

variable {W : Type*} [DecidableEq W] {F G : Finset (Finset W)} {T T' : W}

def leftRemainder (w : CommonThreatWitness F G T T') : Finset W :=
  (w.first.erase T).erase w.bridge

def rightRemainder (w : CommonThreatWitness F G T T') : Finset W :=
  (w.second.erase T').erase w.bridge

def remainder (w : CommonThreatWitness F G T T') : Finset W :=
  w.leftRemainder ∪ w.rightRemainder

theorem leftRemainder_card (w : CommonThreatWitness F G T T') :
    w.leftRemainder.card = w.first.card - 2 := by
  rw [leftRemainder, card_erase_of_mem (mem_erase.mpr ⟨w.bridge_ne_first, w.bridge_first⟩),
    card_erase_of_mem w.first_root]
  omega

theorem rightRemainder_card (w : CommonThreatWitness F G T T') :
    w.rightRemainder.card = w.second.card - 2 := by
  rw [rightRemainder, card_erase_of_mem (mem_erase.mpr ⟨w.bridge_ne_second, w.bridge_second⟩),
    card_erase_of_mem w.second_root]
  omega

theorem first_not_mem_remainder (w : CommonThreatWitness F G T T') : T ∉ w.remainder := by
  intro h
  rcases mem_union.mp h with h | h
  · exact (mem_erase.mp (mem_erase.mp h).2).1 rfl
  · have hdata := mem_erase.mp (mem_erase.mp h).2
    exact hdata.1 (w.second_cross hdata.2)

theorem second_not_mem_remainder (w : CommonThreatWitness F G T T') : T' ∉ w.remainder := by
  intro h
  rcases mem_union.mp h with h | h
  · have hdata := mem_erase.mp (mem_erase.mp h).2
    exact hdata.1 (w.first_cross hdata.2)
  · exact (mem_erase.mp (mem_erase.mp h).2).1 rfl

theorem bridge_not_mem_remainder (w : CommonThreatWitness F G T T') :
    w.bridge ∉ w.remainder := by
  intro h
  rcases mem_union.mp h with h | h <;> exact (mem_erase.mp h).1 rfl

theorem remainder_eq_sdiff (w : CommonThreatWitness F G T T') :
    w.remainder = (w.first ∪ w.second) \ {T, T', w.bridge} := by
  ext x
  constructor
  · intro hx
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · rcases mem_union.mp hx with hl | hr
      · exact mem_union_left _ (mem_of_mem_erase (mem_of_mem_erase hl))
      · exact mem_union_right _ (mem_of_mem_erase (mem_of_mem_erase hr))
    · intro hroot
      simp only [mem_insert, mem_singleton] at hroot
      rcases hroot with rfl | rfl | rfl
      · exact w.first_not_mem_remainder hx
      · exact w.second_not_mem_remainder hx
      · exact w.bridge_not_mem_remainder hx
  · intro hx
    obtain ⟨hmem, hnot⟩ := mem_sdiff.mp hx
    have hxT : x ≠ T := by intro h; exact hnot (by simp [h])
    have hxT' : x ≠ T' := by intro h; exact hnot (by simp [h])
    have hxb : x ≠ w.bridge := by intro h; exact hnot (by simp [h])
    rcases mem_union.mp hmem with hl | hr
    · exact mem_union_left _ (mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxT, hl⟩⟩)
    · exact mem_union_right _ (mem_erase.mpr ⟨hxb, mem_erase.mpr ⟨hxT', hr⟩⟩)

theorem remainder_card (w : CommonThreatWitness F G T T') :
    w.remainder.card = (w.first.card - 2) + (w.second.card - 2) -
      (w.leftRemainder ∩ w.rightRemainder).card := by
  have h := card_union_add_card_inter w.leftRemainder w.rightRemainder
  rw [w.leftRemainder_card, w.rightRemainder_card] at h
  change (w.leftRemainder ∪ w.rightRemainder).card = _
  omega

theorem remainder_sdiff_card (w : CommonThreatWitness F G T T') (H : Finset W)
    (hH : H ⊆ w.remainder) :
    (w.remainder \ H).card = (w.first.card - 2) + (w.second.card - 2) -
      (w.leftRemainder ∩ w.rightRemainder).card - H.card := by
  rw [card_sdiff_of_subset hH, w.remainder_card]

end CommonThreatWitness

/-- The finite inclusion--exclusion identity behind the sum of exposed root
sizes in source Lemma 8.2(3). -/
theorem card_inter_add_card_inter_union_of_subset
    {W : Type*} [DecidableEq W] (A B H : Finset W) (hH : H ⊆ A ∪ B) :
    (A ∩ H).card + (B ∩ (A ∪ H)).card = H.card + (A ∩ B).card := by
  have hcover : (A ∩ H) ∪ (B ∩ H) = H := by
    ext x
    simp only [mem_union, mem_inter]
    constructor
    · tauto
    · intro hx
      rcases mem_union.mp (hH hx) with hA | hB <;> tauto
  have hunion : (A ∩ B) ∪ (B ∩ H) = B ∩ (A ∪ H) := by
    ext x
    simp only [mem_union, mem_inter]
    tauto
  have hcross : (A ∩ H) ∩ (B ∩ H) = (A ∩ B) ∩ (B ∩ H) := by
    ext x
    simp only [mem_inter]
    tauto
  have h₁ := card_union_add_card_inter (A ∩ H) (B ∩ H)
  have h₂ := card_union_add_card_inter (A ∩ B) (B ∩ H)
  rw [hcover, hcross] at h₁
  rw [hunion] at h₂
  omega

end

end Erdos207
