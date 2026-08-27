/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedTwoAwayWitness
import ErdosProblems.Erdos207.UniformExtensionWeight

/-! # Fixed-size localized witness weights and the fully exposed endpoint -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def localizedTwoAwayMapFamily
    {V : Type*} [DecidableEq V] {F G : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V} (hFG : F ⊆ G)
    (w : LocalizedTwoAwayWitness V F T a b U) : LocalizedTwoAwayWitness V G T a b U :=
  ⟨⟨w.1.1, hFG w.1.2.1, w.1.2.2⟩, w.2⟩

theorem localizedTwoAwayMapFamily_injective
    {V : Type*} [DecidableEq V] {F G : ForbiddenFamilyOn V}
    {T : TripleOn V} {a b : V} {U : Finset V} (hFG : F ⊆ G) :
    Function.Injective (localizedTwoAwayMapFamily (T := T) (a := a) (b := b) (U := U) hFG) := by
  intro w z hwz
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun v ↦ v.1.1) hwz

theorem localizedTwoAwayRemainder_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {a b : V} {U : Finset V} {c : ℕ}
    (hcard : ∀ C ∈ F, C.card = c) (w : LocalizedTwoAwayWitness V F T a b U) :
    (localizedTwoAwayRemainder w).card = c - 2 := by
  have hT : T ∈ w.1.1.1.erase w.1.1.2 :=
    mem_erase.mpr ⟨w.1.2.2.2.2.symm, w.1.2.2.2.1⟩
  rw [localizedTwoAwayRemainder, twoAwayThreatRemainder, card_erase_of_mem hT,
    card_erase_of_mem w.1.2.2.1, hcard _ w.1.2.1, Nat.sub_sub]

abbrev ActiveLocalizedTwoAwayWitness
    (V : Type*) [DecidableEq V] (F : ForbiddenFamilyOn V)
    (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V) :=
  {w : LocalizedTwoAwayWitness V F T a b U // R ⊆ localizedTwoAwayRemainder w}

noncomputable instance instFintypeActiveLocalizedTwoAwayWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V) :
    Fintype (ActiveLocalizedTwoAwayWitness V F T a b U R) := Fintype.ofFinite _

theorem extensionWeight_localizedTwoAway_constant
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V)
    (c : ℕ) (hcard : ∀ C ∈ F, C.card = c) (p : ℝ≥0) :
    extensionWeight (fun w : LocalizedTwoAwayWitness V F T a b U ↦ localizedTwoAwayRemainder w)
      (constantTripleWeight p) R =
        (Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) : ℝ≥0) * p ^ (c - 2 - R.card) := by
  classical
  unfold extensionWeight
  calc
    _ = ∑ w : LocalizedTwoAwayWitness V F T a b U,
        if R ⊆ localizedTwoAwayRemainder w then p ^ (c - 2 - R.card) else 0 := by
      apply sum_congr rfl
      intro w _
      by_cases hR : R ⊆ localizedTwoAwayRemainder w
      · rw [if_pos hR, if_pos hR, setWeight_constantTripleWeight, card_sdiff_of_subset hR,
          localizedTwoAwayRemainder_card hcard]
      · rw [if_neg hR, if_neg hR]
    _ = _ := by rw [Fintype.card_subtype, ← sum_filter]; simp

theorem card_activeLocalizedTwoAway_full_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {q c : ℕ} {H : SimpleGraph V} {B : TripleSystemOn V} {X U : Finset V}
    {F : ForbiddenFamilyOn V} {T : TripleOn V} {a b : V} (hab : a ≠ b) (R : TripleSystemOn V)
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B)
    (hcard : ∀ C ∈ F, C.card = c) (hR : R.card = c - 2)
    (hsep : AbsorberSeparatedLevel H X B U)
    (hrootLocal : HasPaddedAbsorberRootLocalization q X B) :
    Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) ≤ 45 * (R.card + 1) + 28 := by
  let f : ActiveLocalizedTwoAwayWitness V F T a b U R →
      LocalizedTwoAwayRemainderFiber V (absorberErdosForbiddenConfigurationsOn q B) T a b U R :=
    fun w ↦ ⟨localizedTwoAwayMapFamily hF w.1, by
      change localizedTwoAwayRemainder w.1 = R
      exact (eq_of_subset_of_card_le w.2 (by rw [localizedTwoAwayRemainder_card hcard, hR])).symm⟩
  have hinj : Function.Injective f := by
    intro w z h
    apply Subtype.ext
    exact localizedTwoAwayMapFamily_injective hF (congrArg Subtype.val h)
  exact (Fintype.card_le_of_injective f hinj).trans
    (card_localizedTwoAwayRemainderFiber_le hab R hsep hrootLocal)

theorem card_activeLocalizedTwoAway_eq_zero_of_large_root
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (T : TripleOn V) (a b : V) (U : Finset V) (R : TripleSystemOn V)
    (c : ℕ) (hcard : ∀ C ∈ F, C.card = c) (hR : c - 2 < R.card) :
    Fintype.card (ActiveLocalizedTwoAwayWitness V F T a b U R) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun w ↦ ?_⟩
  have hle := card_le_card w.2
  rw [localizedTwoAwayRemainder_card hcard] at hle
  omega

end

end Erdos207
