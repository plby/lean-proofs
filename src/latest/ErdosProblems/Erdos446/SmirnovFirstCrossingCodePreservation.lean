/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovFirstCrossingFiberCard

/-!
# Erdős Problem 446: preservation of a first-crossing code

A word realizing a valid first-crossing code has the same first crossing.
This makes fibers belonging to distinct valid codes disjoint, even after the
alphabet is enlarged.
-/

namespace Erdos446

open Finset

theorem lt_iff_lt_of_localCrossingCode_eq {k v V r h : ℕ}
    (x i : Fin k) (j : Fin v) (j' : Fin V) (hh : h < r)
    (heq : localCrossingCode r x i j = localCrossingCode r x i j') :
    j.val < h ↔ j'.val < h := by
  by_cases hj : j.val < r - 1 ∨ (j.val = r - 1 ∧ i ≤ x)
  · by_cases hj' : j'.val < r - 1 ∨ (j'.val = r - 1 ∧ i ≤ x)
    · have hv : j.val = j'.val := by
        simpa [localCrossingCode, hj, hj'] using heq
      omega
    · simp [localCrossingCode, hj, hj'] at heq
  · by_cases hj' : j'.val < r - 1 ∨ (j'.val = r - 1 ∧ i ≤ x)
    · simp [localCrossingCode, hj, hj'] at heq
    · constructor <;> intro hlt
      · exfalso
        apply hj
        left
        omega
      · exfalso
        apply hj'
        left
        omega

theorem wordPrefix_eq_of_mem_crossingCode_of_lt {k u v V h : ℕ}
    (F : FailedWord k u v) {g : Fin k → Fin V}
    (hg : g ∈ wordsWithCrossingCode V (firstCrossingCode F))
    (hh : h < firstFailedSlot u F.1) :
    wordPrefix g h = wordPrefix F.1 h := by
  unfold wordPrefix
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact lt_iff_lt_of_localCrossingCode_eq
    (firstCrossingLabel F) i (g i) (F.1 i) hh
      ((mem_wordsWithCrossingCode.mp hg i).trans rfl)

theorem wordPrefix_crossing_le_of_mem_crossingCode {k u v V : ℕ}
    (F : FailedWord k u v) {g : Fin k → Fin V}
    (hg : g ∈ wordsWithCrossingCode V (firstCrossingCode F)) :
    u + firstFailedSlot u F.1 ≤ wordPrefix g (firstFailedSlot u F.1) := by
  let A := (Finset.univ : Finset (Fin k)).filter fun i ↦
    (firstCrossingCode F).entries i ≠ none
  let B := (Finset.univ : Finset (Fin k)).filter fun i ↦
    (g i).val < firstFailedSlot u F.1
  have hAB : A ⊆ B := by
    intro i hi
    have hne : (firstCrossingCode F).entries i ≠ none := by
      simpa [A] using hi
    have hcode := mem_wordsWithCrossingCode.mp hg i
    have hlocal : localCrossingCode (firstCrossingCode F).slot
        (firstCrossingCode F).label i (g i) ≠ none := by
      rw [hcode]
      exact hne
    have hcond := (localCrossingCode_ne_none_iff _ _ _).mp hlocal
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    change (g i).val < firstFailedSlot u F.1
    change (g i).val < firstFailedSlot u F.1 - 1 ∨
      ((g i).val = firstFailedSlot u F.1 - 1 ∧ i ≤ firstCrossingLabel F) at hcond
    have hr : 1 ≤ firstFailedSlot u F.1 := (firstFailedSlot_spec F.2).1
    rcases hcond with hlt | ⟨heq, _⟩
    · omega
    · omega
  have hcard := Finset.card_le_card hAB
  change A.card ≤ wordPrefix g (firstFailedSlot u F.1) at hcard
  rw [show A.card = u + firstFailedSlot u F.1 by
    simpa [A] using card_firstCrossingCode_some F] at hcard
  exact hcard

theorem not_wordBarrier_of_mem_crossingCode {k u v V : ℕ}
    (F : FailedWord k u v) (hrV : firstFailedSlot u F.1 ≤ V)
    {g : Fin k → Fin V}
    (hg : g ∈ wordsWithCrossingCode V (firstCrossingCode F)) :
    ¬ SatisfiesWordBarrier u g := by
  intro hgood
  have hlt := hgood (firstFailedSlot u F.1)
    (firstFailedSlot_spec F.2).1 hrV
  have hge := wordPrefix_crossing_le_of_mem_crossingCode F hg
  omega

theorem firstFailedSlot_eq_of_mem_crossingCode {k u v V : ℕ}
    (F : FailedWord k u v) (hrV : firstFailedSlot u F.1 ≤ V)
    {g : Fin k → Fin V}
    (hg : g ∈ wordsWithCrossingCode V (firstCrossingCode F)) :
    firstFailedSlot u g = firstFailedSlot u F.1 := by
  let G : FailedWord k u V := ⟨g, not_wordBarrier_of_mem_crossingCode F hrV hg⟩
  have hGspec : 1 ≤ firstFailedSlot u g ∧ firstFailedSlot u g ≤ V ∧
      u + firstFailedSlot u g ≤ wordPrefix g (firstFailedSlot u g) := by
    simpa [G] using firstFailedSlot_spec G.2
  have hFspec := firstFailedSlot_spec F.2
  have hcross := wordPrefix_crossing_le_of_mem_crossingCode F hg
  by_cases hlt : firstFailedSlot u g < firstFailedSlot u F.1
  · have hpref := wordPrefix_eq_of_mem_crossingCode_of_lt F hg hlt
    have hbefore := wordBarrier_before_firstFailedSlot F.2 hGspec.1 hlt
    rw [← hpref] at hbefore
    omega
  · have hle : firstFailedSlot u F.1 ≤ firstFailedSlot u g := by omega
    by_cases hgt : firstFailedSlot u F.1 < firstFailedSlot u g
    · have hbefore := wordBarrier_before_firstFailedSlot G.2 hFspec.1 hgt
      change wordPrefix g (firstFailedSlot u F.1) <
        u + firstFailedSlot u F.1 at hbefore
      omega
    · omega

theorem eq_orderIsoOfFin_of_card_filter_le {k : ℕ}
    (S : Finset (Fin k)) (x : Fin k) (hx : x ∈ S) (j : Fin S.card)
    (hcard : (S.filter fun y ↦ y ≤ x).card = j.val + 1) :
    (S.orderIsoOfFin rfl j).1 = x := by
  let e := S.orderIsoOfFin rfl
  let ix : Fin S.card := e.symm ⟨x, hx⟩
  have hrank := card_filter_le_orderIso S ix
  have heix : (e ix).1 = x := by simp [e, ix]
  rw [heix, hcard] at hrank
  have hij : ix = j := by
    apply Fin.ext
    omega
  rw [← hij]
  exact heix

theorem localCrossingCode_eq_some_boundary_iff {k v r : ℕ}
    (x i : Fin k) (j : Fin v) (hi : i ≤ x) :
    localCrossingCode r x i j = some (r - 1) ↔ j.val = r - 1 := by
  by_cases hcond : j.val < r - 1 ∨ (j.val = r - 1 ∧ i ≤ x)
  · simp [localCrossingCode, hcond]
  · constructor
    · intro h
      simp [localCrossingCode, hcond] at h
    · intro h
      exfalso
      exact hcond (Or.inr ⟨h, hi⟩)

theorem boundary_eq_iff_of_localCrossingCode_eq {k v V r : ℕ}
    (x i : Fin k) (j : Fin v) (j' : Fin V) (hi : i ≤ x)
    (heq : localCrossingCode r x i j = localCrossingCode r x i j') :
    j.val = r - 1 ↔ j'.val = r - 1 := by
  rw [← localCrossingCode_eq_some_boundary_iff x i j hi,
    heq, localCrossingCode_eq_some_boundary_iff x i j' hi]

theorem firstCrossingLabel_eq_of_rank {k u v : ℕ}
    (G : FailedWord k u v) (x : Fin k)
    (hx : x ∈ wordSlotLabels G.1 (firstFailedSlot u G.1 - 1))
    (hcard : ((wordSlotLabels G.1 (firstFailedSlot u G.1 - 1)).filter
      fun i ↦ i ≤ x).card =
        u + firstFailedSlot u G.1 -
          wordPrefix G.1 (firstFailedSlot u G.1 - 1)) :
    firstCrossingLabel G = x := by
  let d := u + firstFailedSlot u G.1 -
    wordPrefix G.1 (firstFailedSlot u G.1 - 1)
  let S := wordSlotLabels G.1 (firstFailedSlot u G.1 - 1)
  have hd : 0 < d := by simpa [d] using crossingDeficit_pos G.2
  have hdS : d ≤ S.card := by
    simpa [d, S] using crossingDeficit_le_slotCard G.2
  have heq := eq_orderIsoOfFin_of_card_filter_le S x (by simpa [S] using hx)
    ⟨d - 1, by omega⟩
  have hcard' : (S.filter fun i ↦ i ≤ x).card = (d - 1) + 1 := by
    have hc : (S.filter fun i ↦ i ≤ x).card = d := by
      simpa [S, d] using hcard
    omega
  have hrank := heq hcard'
  change (S.orderIsoOfFin rfl ⟨d - 1, by omega⟩).1 = x at hrank
  simpa [firstCrossingLabel, d, S] using hrank

theorem firstCrossingLabel_eq_of_mem_crossingCode {k u v V : ℕ}
    (F : FailedWord k u v) (hrV : firstFailedSlot u F.1 ≤ V)
    {g : Fin k → Fin V}
    (hg : g ∈ wordsWithCrossingCode V (firstCrossingCode F)) :
    firstCrossingLabel
        (⟨g, not_wordBarrier_of_mem_crossingCode F hrV hg⟩ : FailedWord k u V) =
      firstCrossingLabel F := by
  let G : FailedWord k u V :=
    ⟨g, not_wordBarrier_of_mem_crossingCode F hrV hg⟩
  let r := firstFailedSlot u F.1
  let x := firstCrossingLabel F
  have hrpos : 1 ≤ r := by simpa [r] using (firstFailedSlot_spec F.2).1
  have hslot : firstFailedSlot u G.1 = r := by
    simpa [G, r] using firstFailedSlot_eq_of_mem_crossingCode F hrV hg
  have hpref : wordPrefix g (r - 1) = wordPrefix F.1 (r - 1) := by
    apply wordPrefix_eq_of_mem_crossingCode_of_lt F hg
    omega
  have hfiltered :
      (wordSlotLabels g (r - 1)).filter (fun i ↦ i ≤ x) =
        (wordSlotLabels F.1 (r - 1)).filter (fun i ↦ i ≤ x) := by
    ext i
    simp only [wordSlotLabels, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ≤ x
    · simp only [hi, and_true]
      exact boundary_eq_iff_of_localCrossingCode_eq x i (g i) (F.1 i) hi
        ((mem_wordsWithCrossingCode.mp hg i).trans rfl)
    · simp [hi]
  have hxF : x ∈ wordSlotLabels F.1 (r - 1) := by
    simpa [x, r] using firstCrossingLabel_mem_slot F
  have hxG : x ∈ wordSlotLabels G.1 (firstFailedSlot u G.1 - 1) := by
    rw [hslot]
    change x ∈ wordSlotLabels g (r - 1)
    have hvalF : (F.1 x).val = r - 1 := by
      simpa [wordSlotLabels] using hxF
    have hvalG : (g x).val = r - 1 :=
      (boundary_eq_iff_of_localCrossingCode_eq x x (g x) (F.1 x) le_rfl
        ((mem_wordsWithCrossingCode.mp hg x).trans rfl)).2 hvalF
    simpa [wordSlotLabels] using hvalG
  apply firstCrossingLabel_eq_of_rank G x hxG
  rw [hslot]
  change ((wordSlotLabels g (r - 1)).filter fun i ↦ i ≤ x).card =
    u + r - wordPrefix g (r - 1)
  rw [hfiltered, hpref]
  simpa [x, r] using card_slotLabels_le_firstCrossingLabel F

theorem firstCrossingCode_eq_of_mem_crossingCode {k u v V : ℕ}
    (F : FailedWord k u v) (hrV : firstFailedSlot u F.1 ≤ V)
    {g : Fin k → Fin V}
    (hg : g ∈ wordsWithCrossingCode V (firstCrossingCode F)) :
    firstCrossingCode
        (⟨g, not_wordBarrier_of_mem_crossingCode F hrV hg⟩ : FailedWord k u V) =
      firstCrossingCode F := by
  let G : FailedWord k u V :=
    ⟨g, not_wordBarrier_of_mem_crossingCode F hrV hg⟩
  have hslot : firstFailedSlot u G.1 = firstFailedSlot u F.1 := by
    simpa [G] using firstFailedSlot_eq_of_mem_crossingCode F hrV hg
  have hlabel : firstCrossingLabel G = firstCrossingLabel F := by
    simpa [G] using firstCrossingLabel_eq_of_mem_crossingCode F hrV hg
  have hentries : (firstCrossingCode G).entries =
      (firstCrossingCode F).entries := by
    funext i
    change localCrossingCode (firstFailedSlot u G.1)
      (firstCrossingLabel G) i (G.1 i) =
        localCrossingCode (firstFailedSlot u F.1)
          (firstCrossingLabel F) i (F.1 i)
    rw [hslot, hlabel]
    exact (mem_wordsWithCrossingCode.mp hg i).trans rfl
  have hslotC : (firstCrossingCode G).slot =
      (firstCrossingCode F).slot := hslot
  have hlabelC : (firstCrossingCode G).label =
      (firstCrossingCode F).label := hlabel
  cases hCG : firstCrossingCode G with
  | mk rG xG eG =>
      cases hCF : firstCrossingCode F with
      | mk rF xF eF =>
          simp only [hCG, hCF] at hslotC hlabelC hentries ⊢
          subst rF
          subst xF
          subst eF
          rfl

end Erdos446
