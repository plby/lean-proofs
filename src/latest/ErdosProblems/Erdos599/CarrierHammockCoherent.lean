/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CarrierHammockClosure
import ErdosProblems.Erdos599.RegularRows

/-!
# Prefix-causal coherent choices for increasing carrier-hammock eligibility

At each stage extend the union of earlier choices to a bounded maximal-up-to
hammock. The selector is total on arbitrary eligibility data and always
bounded. For increasing data it retains every earlier choice. Since the
index cardinal equals the cap, the complete union is maximal up to that
same cap among all eventually eligible routes.
-/

noncomputable section

namespace Erdos599.Blueprint.CarrierHammock

open Cardinal Set Order Ladder
open CardinalInduction.RegularRows

universe u

variable {Route V : Type u} {good : Set Route}
variable {carrier : Route → Set V} {ends : Set V} {rho : Cardinal.{u}}

theorem exists_maximalUpTo_superset (hrho : aleph0 ≤ rho)
    {K : Set Route} (hK : Admissible good carrier ends K) (hKcard : #K ≤ rho) :
    ∃ H : Set Route, K ⊆ H ∧
      MaximalUpTo {J | Admissible good carrier ends J} rho H := by
  obtain ⟨M, hKM, hM⟩ := exists_maximal_superset hK
  by_cases hsmall : #M ≤ rho
  · exact ⟨M, hKM, maximalUpTo_of_maximal hM.1 hM hsmall⟩
  · have hlarge : succ rho ≤ #M := succ_le_of_lt (lt_of_not_ge hsmall)
    obtain ⟨a, ha⟩ := Cardinal.le_mk_iff_exists_set.mp ((le_succ rho).trans hlarge)
    obtain ⟨b, hb⟩ := Cardinal.le_mk_iff_exists_set.mp hlarge
    let A : Set Route := Subtype.val '' a
    let B : Set Route := Subtype.val '' b
    have hAM : A ⊆ M := by rintro q ⟨r, _, rfl⟩; exact r.2
    have hBM : B ⊆ M := by rintro q ⟨r, _, rfl⟩; exact r.2
    have hAcard : #A = rho :=
      (Cardinal.mk_image_eq_of_injOn Subtype.val a Set.injOn_subtype_val).trans ha
    have hBcard : #B = succ rho :=
      (Cardinal.mk_image_eq_of_injOn Subtype.val b Set.injOn_subtype_val).trans hb
    have hHcard : #(K ∪ A : Set Route) = rho := by
      apply le_antisymm
      · exact (Cardinal.mk_union_le K A).trans
          (Cardinal.add_le_of_le hrho hKcard hAcard.le)
      · rw [← hAcard]
        exact Cardinal.mk_subtype_mono Set.subset_union_right
    exact ⟨K ∪ A, Set.subset_union_left,
      maximalUpTo_of_large (hM.1.subset (Set.union_subset hKM hAM)) hHcard
        (hM.1.subset hBM) hBcard⟩

def seededExtension (good : Set Route) (carrier : Route → Set V)
    (ends : Set V) (rho : Cardinal.{u}) (K : Set Route) : Set Route := by
  classical
  exact if h : aleph0 ≤ rho ∧ Admissible good carrier ends K ∧ #K ≤ rho then
    (exists_maximalUpTo_superset h.1 h.2.1 h.2.2).choose
  else ∅

theorem seededExtension_spec (hrho : aleph0 ≤ rho)
    {K : Set Route} (hK : Admissible good carrier ends K) (hKcard : #K ≤ rho) :
    K ⊆ seededExtension good carrier ends rho K ∧
      MaximalUpTo {J | Admissible good carrier ends J} rho
        (seededExtension good carrier ends rho K) := by
  rw [seededExtension, dif_pos ⟨hrho, hK, hKcard⟩]
  exact (exists_maximalUpTo_superset hrho hK hKcard).choose_spec

theorem seededExtension_card_le (hrho : aleph0 ≤ rho) (K : Set Route) :
    #(seededExtension good carrier ends rho K) ≤ rho := by
  by_cases h : Admissible good carrier ends K ∧ #K ≤ rho
  · exact (seededExtension_spec hrho h.1 h.2).2.card_le
  · rw [seededExtension, dif_neg (fun h' ↦ h h'.2)]
    simp

namespace Coherent

variable (good : Stage rho → Set Route) (carrier : Route → Set V) (ends : Set V)

def priorUnion (a : Stage rho) (prior : ∀ b : Stage rho, b < a → Set Route) : Set Route :=
  ⋃ b : Set.Iio a, prior b.1 b.2

def chosenAt (a : Stage rho) : Set Route :=
  WellFounded.fix wellFounded_lt
    (fun b prior ↦ seededExtension (good b) carrier ends rho (priorUnion b prior)) a

theorem chosenAt_eq (a : Stage rho) :
    chosenAt good carrier ends a =
      seededExtension (good a) carrier ends rho
        (priorUnion a (fun b _ ↦ chosenAt good carrier ends b)) :=
  WellFounded.fix_eq wellFounded_lt
    (fun b prior ↦ seededExtension (good b) carrier ends rho (priorUnion b prior)) a

theorem chosenAt_card_le (hrho : aleph0 ≤ rho) (a : Stage rho) :
    #(chosenAt good carrier ends a) ≤ rho := by
  rw [chosenAt_eq]
  exact seededExtension_card_le hrho _

/-- No future eligibility data are inspected by the actual selector. -/
theorem chosenAt_congr_le (good' : Stage rho → Set Route) :
    ∀ a : Stage rho, (∀ b, b ≤ a → good b = good' b) →
      chosenAt good carrier ends a = chosenAt good' carrier ends a := by
  intro a
  apply WellFounded.induction wellFounded_lt a
  intro a ih hprefix
  rw [chosenAt_eq, chosenAt_eq, hprefix a le_rfl]
  apply congrArg (seededExtension (good' a) carrier ends rho)
  apply Set.iUnion_congr
  intro b
  exact ih b.1 b.2 (fun c hcb ↦ hprefix c (hcb.trans b.2.le))

theorem chosenAt_spec (hrho : aleph0 ≤ rho) (hmono : Monotone good) :
    ∀ a : Stage rho,
      MaximalUpTo {J | Admissible (good a) carrier ends J} rho
        (chosenAt good carrier ends a) ∧
      ∀ b, b < a → chosenAt good carrier ends b ⊆ chosenAt good carrier ends a := by
  intro a
  apply WellFounded.induction wellFounded_lt a
  intro a ih
  let K := priorUnion a (fun b _ ↦ chosenAt good carrier ends b)
  have hK : Admissible (good a) carrier ends K := by
    constructor
    · intro q hq
      obtain ⟨b, hqb⟩ := Set.mem_iUnion.mp hq
      exact hmono b.2.le ((ih b.1 b.2).1.mem.1 hqb)
    · intro q hq r hr hqr
      obtain ⟨b, hqb⟩ := Set.mem_iUnion.mp hq
      obtain ⟨c, hrc⟩ := Set.mem_iUnion.mp hr
      rcases lt_trichotomy b.1 c.1 with hbc | hbc | hcb
      · exact (ih c.1 c.2).1.mem.2 ((ih c.1 c.2).2 b.1 hbc hqb) hrc hqr
      · have hsub : b = c := Subtype.ext hbc
        subst c
        exact (ih b.1 b.2).1.mem.2 hqb hrc hqr
      · exact (ih b.1 b.2).1.mem.2 hqb ((ih b.1 b.2).2 c.1 hcb hrc) hqr
  have hKcard : #K ≤ rho :=
    mk_iUnion_stageSet_le hrho
      (fun b : Set.Iio a ↦ chosenAt good carrier ends b.1)
      (fun b ↦ chosenAt_card_le good carrier ends hrho b.1)
  have hspec := seededExtension_spec hrho hK hKcard
  rw [chosenAt_eq]
  exact ⟨hspec.2, fun b hba q hq ↦ hspec.1 (Set.mem_iUnion.mpr ⟨⟨b, hba⟩, hq⟩)⟩

theorem chosenAt_monotone (hrho : aleph0 ≤ rho) (hmono : Monotone good) :
    Monotone (chosenAt good carrier ends) := by
  intro a b hab
  rcases hab.eq_or_lt with rfl | hab
  · exact Set.Subset.rfl
  · exact (chosenAt_spec good carrier ends hrho hmono b).2 a hab

def total : Set Route := ⋃ a : Stage rho, chosenAt good carrier ends a

theorem chosenAt_subset_total (a : Stage rho) :
    chosenAt good carrier ends a ⊆ total good carrier ends :=
  fun _ hq ↦ Set.mem_iUnion.mpr ⟨a, hq⟩

theorem total_card_le (hrho : aleph0 ≤ rho) : #(total good carrier ends) ≤ rho := by
  let R : RowSystem rho Route :=
    ⟨chosenAt good carrier ends, chosenAt_card_le good carrier ends hrho⟩
  exact R.mk_carrier_le hrho

theorem total_admissible (hrho : aleph0 ≤ rho) (hmono : Monotone good) :
    Admissible (⋃ a, good a) carrier ends (total good carrier ends) := by
  constructor
  · intro q hq
    obtain ⟨a, hqa⟩ := Set.mem_iUnion.mp hq
    exact Set.mem_iUnion.mpr ⟨a, (chosenAt_spec good carrier ends hrho hmono a).1.mem.1 hqa⟩
  · intro q hq r hr hqr
    obtain ⟨a, hqa⟩ := Set.mem_iUnion.mp hq
    obtain ⟨b, hrb⟩ := Set.mem_iUnion.mp hr
    have hchosen := chosenAt_monotone good carrier ends hrho hmono
    exact (chosenAt_spec good carrier ends hrho hmono (max a b)).1.mem.2
      (hchosen (le_max_left a b) hqa) (hchosen (le_max_right a b) hrb) hqr

/-- The full union, not an independently selected limiting family, has the
required global maximal-up-to property. -/
theorem total_maximalUpTo (hrho : aleph0 ≤ rho) (hmono : Monotone good) :
    MaximalUpTo {J | Admissible (⋃ a, good a) carrier ends J} rho
      (total good carrier ends) := by
  have htotal := total_admissible good carrier ends hrho hmono
  have hcard := total_card_le good carrier ends hrho
  by_cases hmax : ∀ a, Maximal (Admissible (good a) carrier ends)
      (chosenAt good carrier ends a)
  · apply maximalUpTo_of_maximal htotal _ hcard
    refine ⟨htotal, ?_⟩
    intro K hK htotalK q hqK
    obtain ⟨a, hqa⟩ := Set.mem_iUnion.mp (hK.1 hqK)
    have hinsert : Admissible (good a) carrier ends
        (insert q (chosenAt good carrier ends a)) :=
      ⟨Set.insert_subset hqa (hmax a).1.1,
        hK.2.subset (Set.insert_subset hqK
          ((chosenAt_subset_total good carrier ends a).trans htotalK))⟩
    have hqChosen := (hmax a).2 hinsert (Set.subset_insert q _) (Set.mem_insert q _)
    exact chosenAt_subset_total good carrier ends a hqChosen
  · push Not at hmax
    obtain ⟨a, ha⟩ := hmax
    rcases (chosenAt_spec good carrier ends hrho hmono a).1 with hsmall | hlarge
    · exact False.elim (ha hsmall.2.1)
    · have htotalCard : #(total good carrier ends) = rho := by
        apply le_antisymm hcard
        exact hlarge.2.1.ge.trans
          (Cardinal.mk_subtype_mono (chosenAt_subset_total good carrier ends a))
      obtain ⟨K, hK, hKcard⟩ := hlarge.2.2
      exact maximalUpTo_of_large htotal htotalCard
        (show Admissible (⋃ b, good b) carrier ends K from
          ⟨fun q hq ↦ Set.mem_iUnion.mpr ⟨a, hK.1 hq⟩, hK.2⟩) hKcard

#print axioms chosenAt_congr_le
#print axioms chosenAt_spec
#print axioms total_maximalUpTo

end Coherent
end Erdos599.Blueprint.CarrierHammock
