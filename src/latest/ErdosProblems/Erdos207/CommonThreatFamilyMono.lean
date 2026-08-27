/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CommonThreatFamilyUnion

/-! # Removing singleton families and enlarging common-threat witness families -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

namespace CommonThreatWitness

theorem first_card_ge_two {W : Type*} [DecidableEq W]
    {F G : Finset (Finset W)} {T T' : W} (w : CommonThreatWitness F G T T') :
    2 ≤ w.first.card := by
  have h : ({T, w.bridge} : Finset W) ⊆ w.first :=
    insert_subset w.first_root (singleton_subset_iff.mpr w.bridge_first)
  have hc := card_le_card h
  simpa [Ne.symm w.bridge_ne_first] using hc

theorem second_card_ge_two {W : Type*} [DecidableEq W]
    {F G : Finset (Finset W)} {T T' : W} (w : CommonThreatWitness F G T T') :
    2 ≤ w.second.card := by
  have h : ({T', w.bridge} : Finset W) ⊆ w.second :=
    insert_subset w.second_root (singleton_subset_iff.mpr w.bridge_second)
  have hc := card_le_card h
  simpa [Ne.symm w.bridge_ne_second] using hc

def mapFamilies {W : Type*} [DecidableEq W]
    {F G F' G' : Finset (Finset W)} {T T' : W}
    (hF : ∀ E ∈ F, 2 ≤ E.card → E ∈ F') (hG : ∀ E ∈ G, 2 ≤ E.card → E ∈ G')
    (w : CommonThreatWitness F G T T') : CommonThreatWitness F' G' T T' :=
  { w with first_mem := hF w.first w.first_mem w.first_card_ge_two,
           second_mem := hG w.second w.second_mem w.second_card_ge_two }

theorem mapFamilies_injective {W : Type*} [DecidableEq W]
    {F G F' G' : Finset (Finset W)} {T T' : W}
    (hF : ∀ E ∈ F, 2 ≤ E.card → E ∈ F') (hG : ∀ E ∈ G, 2 ≤ E.card → E ∈ G') :
    Function.Injective (mapFamilies (T := T) (T' := T') hF hG) := by
  intro w u h
  exact ext_data w u (congrArg (fun w ↦ w.bridge) h)
    (congrArg (fun w ↦ w.first) h) (congrArg (fun w ↦ w.second) h)

@[simp] theorem mapFamilies_remainder {W : Type*} [DecidableEq W]
    {F G F' G' : Finset (Finset W)} {T T' : W}
    (hF : ∀ E ∈ F, 2 ≤ E.card → E ∈ F') (hG : ∀ E ∈ G, 2 ≤ E.card → E ∈ G')
    (w : CommonThreatWitness F G T T') : (mapFamilies hF hG w).remainder = w.remainder := rfl

end CommonThreatWitness

theorem extensionWeight_commonThreat_mono
    {W : Type*} [Fintype W] [DecidableEq W]
    {F G F' G' : Finset (Finset W)} (T T' : W) (p : W → ℝ≥0) (H : Finset W)
    (hF : ∀ E ∈ F, 2 ≤ E.card → E ∈ F') (hG : ∀ E ∈ G, 2 ≤ E.card → E ∈ G') :
    extensionWeight (fun w : CommonThreatWitness F G T T' ↦ w.remainder) p H ≤
      extensionWeight (fun w : CommonThreatWitness F' G' T T' ↦ w.remainder) p H := by
  apply sum_le_sum_of_injective_code (CommonThreatWitness.mapFamilies hF hG)
    (CommonThreatWitness.mapFamilies_injective hF hG)
  intro w
  exact le_rfl

theorem selectedCount_commonThreat_mono
    {W : Type*} [Fintype W] [DecidableEq W]
    {F G F' G' : Finset (Finset W)} (T T' : W) (A : Finset W)
    (hF : ∀ E ∈ F, 2 ≤ E.card → E ∈ F') (hG : ∀ E ∈ G, 2 ≤ E.card → E ∈ G') :
    selectedCount (fun w : CommonThreatWitness F G T T' ↦ w.remainder) A ≤
      selectedCount (fun w : CommonThreatWitness F' G' T T' ↦ w.remainder) A := by
  apply sum_le_sum_of_injective_code (CommonThreatWitness.mapFamilies hF hG)
    (CommonThreatWitness.mapFamilies_injective hF hG)
  intro w
  exact le_rfl

end

end Erdos207
