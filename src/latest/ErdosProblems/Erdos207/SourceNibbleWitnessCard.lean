/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceNibbleMixedWeights

/-! # Polynomial witness counts for the additive local-degree moment error -/

namespace Erdos207

open Finset

noncomputable section

theorem sourceNibbleCoordinates_card
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T : TripleOn V}
    (huniform : ∀ E ∈ F, E.card = j' - 2) (hpacking : ∀ E ∈ F, IsPackingOn E)
    (hj : 4 ≤ j) (hjj : j ≤ j')
    {x : TripleSystemOn V × TripleSystemOn V} (hx : x ∈ sourceNibbleCodes W F T j j') :
    (sourceNibbleCoordinates T x).card = (j' - j) + 3 * (j - 3) := by
  rw [sourceNibbleCoordinates, card_disjSum, (sourceNibbleCode_data hx).2.2.2.1,
    sourceNibbleRemaining_edge_card huniform hpacking hj hjj hx]

theorem sourceNibbleCoordinates_card_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell j j' : ℕ}
    {W : Vortex V ell} {F : ForbiddenFamilyOn V} {T : TripleOn V}
    (huniform : ∀ E ∈ F, E.card = j' - 2) (hpacking : ∀ E ∈ F, IsPackingOn E)
    (hj : 4 ≤ j) (hjj : j ≤ j')
    {x : TripleSystemOn V × TripleSystemOn V} (hx : x ∈ sourceNibbleCodes W F T j j') :
    (sourceNibbleCoordinates T x).card ≤ 3 * j' := by
  rw [sourceNibbleCoordinates_card huniform hpacking hj hjj hx]
  omega

theorem card_terminalRemainderChoices_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (C : TripleSystemOn V) (f : ℕ) :
    (terminalRemainderChoices W C f).card ≤ 2 ^ C.card := by
  rw [← card_powerset]
  apply card_le_card
  intro A hA
  exact mem_powerset.mpr (mem_terminalRemainderChoices_iff.mp hA).1

theorem card_terminalOmissionCodes_le
    {V A : Type*} [Fintype V] [DecidableEq V] [DecidableEq A] {ell : ℕ}
    (W : Vortex V ell) (I : Finset A) (C : A → TripleSystemOn V) (f m : ℕ)
    (hcard : ∀ x ∈ I, (C x).card ≤ m) :
    (terminalOmissionCodes W I C f).card ≤ I.card * 2 ^ m := by
  unfold terminalOmissionCodes
  apply card_biUnion_le.trans
  calc
    _ ≤ ∑ _x ∈ I, 2 ^ m := by
      apply sum_le_sum
      intro x hx
      exact card_image_le.trans ((card_terminalRemainderChoices_le W (C x) f).trans
        (Nat.pow_le_pow_right (by omega) (hcard x hx)))
    _ = _ := by simp

theorem card_sourceNibbleCodes_le_family_mul
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ)
    (huniform : ∀ E ∈ F, E.card = j' - 2) :
    (sourceNibbleCodes W F T j j').card ≤ F.card * 2 ^ (j' - 3) := by
  apply (card_terminalOmissionCodes_le W (familyExtensions F {T}) (fun E ↦ E \ {T})
    (j' - j) (j' - 3) ?_).trans
  · exact Nat.mul_le_mul_right _ (card_le_card (filter_subset _ _))
  · intro E hE
    have hm := mem_familyExtensions_iff.mp hE
    rw [card_sdiff_of_subset hm.2, huniform E hm.1, card_singleton]
    omega

theorem card_sourceNibbleCodes_le_polynomial
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (F : ForbiddenFamilyOn V) (T : TripleOn V) (j j' : ℕ)
    (huniform : ∀ E ∈ F, E.card = j' - 2) :
    (sourceNibbleCodes W F T j j').card ≤ 2 ^ j' * (Fintype.card V + 1) ^ (3 * j') := by
  have hF : F.card ≤ (Fintype.card (TripleOn V)) ^ (j' - 2) := by
    have hsub : F ⊆ (univ : Finset (TripleOn V)).powersetCard (j' - 2) :=
      fun E hE ↦ mem_powersetCard.mpr ⟨subset_univ E, huniform E hE⟩
    exact (card_le_card hsub).trans (by
      simpa only [card_powersetCard, card_univ] using
        (Nat.choose_le_pow (Fintype.card (TripleOn V)) (j' - 2)))
  have htri : Fintype.card (TripleOn V) ≤ Fintype.card V ^ 3 := by
    rw [show Fintype.card (TripleOn V) = Nat.choose (Fintype.card V) 3 from Fintype.card_finset_len 3]
    exact Nat.choose_le_pow _ _
  have hF' : F.card ≤ (Fintype.card V + 1) ^ (3 * j') := by
    apply (hF.trans (Nat.pow_le_pow_left htri _)).trans
    rw [← pow_mul]
    apply (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
    exact Nat.pow_le_pow_right (by omega) (by omega)
  apply (card_sourceNibbleCodes_le_family_mul W F T j j' huniform).trans
  simpa only [mul_comm] using Nat.mul_le_mul hF' (Nat.pow_le_pow_right (by omega) (Nat.sub_le j' 3))

end

end Erdos207
