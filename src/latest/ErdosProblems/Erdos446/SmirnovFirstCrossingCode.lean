/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovFirstCrossingFiberRatio

/-!
# Erdős Problem 446: finite first-crossing codes

A crossing code freezes the crossing prefix of a labelled word and leaves
all later letters independent.  The last theorem identifies the cardinality
of a code fiber with the product of its one-letter fibers.
-/

namespace Erdos446

open Finset

/-- The contribution of one labelled letter to a crossing-prefix code. -/
def localCrossingCode {v : ℕ} (r : ℕ) (x i : Fin k) (j : Fin v) : Option ℕ :=
  if (j.val < r - 1 ∨ (j.val = r - 1 ∧ i ≤ x)) then some j.val else none

/-- Common codomain for first-crossing data at different alphabet sizes. -/
structure FirstCrossingCode (k : ℕ) where
  slot : ℕ
  label : Fin k
  entries : Fin k → Option ℕ
deriving DecidableEq

/-- The code attached to a bad word. -/
noncomputable def firstCrossingCode {k u v : ℕ}
    (F : FailedWord k u v) : FirstCrossingCode k where
  slot := firstFailedSlot u F.1
  label := firstCrossingLabel F
  entries := fun i ↦ localCrossingCode (firstFailedSlot u F.1)
    (firstCrossingLabel F) i (F.1 i)

/-- Words over an alphabet of size `v` realizing a fixed crossing code. -/
noncomputable def wordsWithCrossingCode {k : ℕ} (v : ℕ)
    (C : FirstCrossingCode k) : Finset (Fin k → Fin v) := by
  classical
  exact Finset.univ.filter fun f ↦
    ∀ i, localCrossingCode C.slot C.label i (f i) = C.entries i

theorem mem_wordsWithCrossingCode {k v : ℕ} {C : FirstCrossingCode k}
    {f : Fin k → Fin v} :
    f ∈ wordsWithCrossingCode v C ↔
      ∀ i, localCrossingCode C.slot C.label i (f i) = C.entries i := by
  classical
  simp [wordsWithCrossingCode]

theorem word_mem_own_firstCrossingCode {k u v : ℕ}
    (F : FailedWord k u v) :
    F.1 ∈ wordsWithCrossingCode v (firstCrossingCode F) := by
  rw [mem_wordsWithCrossingCode]
  intro i
  rfl

theorem localCrossingCode_ne_none_iff {k v r : ℕ}
    (x i : Fin k) (j : Fin v) :
    localCrossingCode r x i j ≠ none ↔
      j.val < r - 1 ∨ (j.val = r - 1 ∧ i ≤ x) := by
  unfold localCrossingCode
  by_cases h : j.val < r - 1 ∨ (j.val = r - 1 ∧ i ≤ x)
  · simp [h]
  · simp [h]

theorem card_firstCrossingCode_some {k u v : ℕ}
    (F : FailedWord k u v) :
    ((Finset.univ : Finset (Fin k)).filter fun i ↦
      (firstCrossingCode F).entries i ≠ none).card =
        u + firstFailedSlot u F.1 := by
  classical
  let r := firstFailedSlot u F.1
  let x := firstCrossingLabel F
  let A := (Finset.univ : Finset (Fin k)).filter fun i ↦ (F.1 i).val < r - 1
  let B := (wordSlotLabels F.1 (r - 1)).filter fun i ↦ i ≤ x
  have hset : ((Finset.univ : Finset (Fin k)).filter fun i ↦
      (firstCrossingCode F).entries i ≠ none) = A ∪ B := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    change localCrossingCode r x i (F.1 i) ≠ none ↔ _
    rw [localCrossingCode_ne_none_iff]
    simp only [A, B, wordSlotLabels, Finset.mem_filter,
      Finset.mem_univ, true_and]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    have hiA' : (F.1 i).val < r - 1 := by simpa [A] using hiA
    have hiB' : (F.1 i).val = r - 1 := by
      change i ∈ (wordSlotLabels F.1 (r - 1)).filter (fun i ↦ i ≤ x) at hiB
      have hmem := (Finset.mem_filter.mp hiB).1
      simpa [wordSlotLabels] using hmem
    omega
  rw [hset, Finset.card_union_of_disjoint hdisj]
  have hA : A.card = wordPrefix F.1 (r - 1) := by rfl
  have hB : B.card = u + r - wordPrefix F.1 (r - 1) := by
    simpa [B, r, x] using card_slotLabels_le_firstCrossingLabel F
  rw [hA, hB]
  have hprev : wordPrefix F.1 (r - 1) ≤ u + r := by
    have hp := crossingDeficit_pos F.2
    change 0 < u + r - wordPrefix F.1 (r - 1) at hp
    omega
  omega

theorem card_firstCrossingCode_none {k u v : ℕ}
    (F : FailedWord k u v) :
    ((Finset.univ : Finset (Fin k)).filter fun i ↦
      (firstCrossingCode F).entries i = none).card =
        k - (u + firstFailedSlot u F.1) := by
  have hsome := card_firstCrossingCode_some F
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k)))
    (p := fun i ↦ (firstCrossingCode F).entries i = none)
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  have hnot : ((Finset.univ : Finset (Fin k)).filter fun i ↦
      ¬ (firstCrossingCode F).entries i = none).card =
      u + firstFailedSlot u F.1 := by
    simpa only [ne_eq] using hsome
  rw [hnot] at hpartition
  omega

/-- Letters allowed at one coordinate of a fixed crossing code. -/
abbrev CrossingCodeLetter {k : ℕ} (v : ℕ) (C : FirstCrossingCode k)
    (i : Fin k) :=
  {j : Fin v // localCrossingCode C.slot C.label i j = C.entries i}

noncomputable def finFilterLtEquiv {a v : ℕ} (ha : a ≤ v) :
    ↑((Finset.univ : Finset (Fin v)).filter fun j ↦ j.val < a) ≃ Fin a where
  toFun j := ⟨j.1.val, (Finset.mem_filter.mp j.2).2⟩
  invFun j := ⟨⟨j.val, j.isLt.trans_le ha⟩, by simp⟩
  left_inv j := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv j := by apply Fin.ext; rfl

theorem card_filter_fin_ge {a v : ℕ} (ha : a ≤ v) :
    ((Finset.univ : Finset (Fin v)).filter fun j ↦ a ≤ j.val).card = v - a := by
  have hlt : ((Finset.univ : Finset (Fin v)).filter fun j ↦ j.val < a).card = a := by
    calc
      ((Finset.univ : Finset (Fin v)).filter fun j ↦ j.val < a).card =
          Fintype.card ↑((Finset.univ : Finset (Fin v)).filter fun j ↦ j.val < a) :=
        (Fintype.card_coe _).symm
      _ = Fintype.card (Fin a) := Fintype.card_congr (finFilterLtEquiv ha)
      _ = a := Fintype.card_fin a
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin v))) (p := fun j ↦ a ≤ j.val)
  simp only [Finset.card_univ, Fintype.card_fin] at hpartition
  have hnot : ((Finset.univ : Finset (Fin v)).filter fun j ↦ ¬ a ≤ j.val).card = a := by
    convert hlt using 1
    congr 1
    ext j
    simp
  rw [hnot] at hpartition
  omega

theorem card_crossingCodeLetter_some {k u v V : ℕ}
    (F : FailedWord k u v) (hV : v ≤ V) {i : Fin k}
    (hi : (firstCrossingCode F).entries i ≠ none) :
    Fintype.card (CrossingCodeLetter V (firstCrossingCode F) i) = 1 := by
  rw [Fintype.card_eq_one_iff]
  let jV : Fin V := ⟨(F.1 i).val, (F.1 i).isLt.trans_le hV⟩
  have hjV : localCrossingCode (firstCrossingCode F).slot
      (firstCrossingCode F).label i jV = (firstCrossingCode F).entries i := by
    rfl
  refine ⟨⟨jV, hjV⟩, ?_⟩
  intro y
  apply Subtype.ext
  apply Fin.ext
  have hcode : localCrossingCode (firstCrossingCode F).slot
      (firstCrossingCode F).label i y.1 =
        localCrossingCode (firstCrossingCode F).slot
          (firstCrossingCode F).label i jV := y.2.trans hjV.symm
  have hyn : localCrossingCode (firstCrossingCode F).slot
      (firstCrossingCode F).label i y.1 ≠ none := by
    intro hy
    apply hi
    exact y.2.symm.trans hy
  have hjvn : localCrossingCode (firstCrossingCode F).slot
      (firstCrossingCode F).label i jV ≠ none := by
    intro hj
    apply hi
    exact hjV.symm.trans hj
  have hycond := (localCrossingCode_ne_none_iff _ _ _).mp hyn
  have hjcond := (localCrossingCode_ne_none_iff _ _ _).mp hjvn
  have hySome : localCrossingCode (firstCrossingCode F).slot
      (firstCrossingCode F).label i y.1 = some y.1.val := by
    simp [localCrossingCode, hycond]
  have hjSome : localCrossingCode (firstCrossingCode F).slot
      (firstCrossingCode F).label i jV = some jV.val := by
    simp [localCrossingCode, hjcond]
  rw [hySome, hjSome] at hcode
  exact Option.some.inj hcode

theorem card_crossingCodeLetter_none_after {k u v V : ℕ}
    (F : FailedWord k u v) (hV : firstFailedSlot u F.1 - 1 ≤ V)
    {i : Fin k} (hi : (firstCrossingCode F).label < i)
    (hnone : (firstCrossingCode F).entries i = none) :
    Fintype.card (CrossingCodeLetter V (firstCrossingCode F) i) =
      V - (firstFailedSlot u F.1 - 1) := by
  rw [Fintype.card_subtype]
  rw [show {j ∈ (Finset.univ : Finset (Fin V)) |
      localCrossingCode (firstCrossingCode F).slot
        (firstCrossingCode F).label i j = (firstCrossingCode F).entries i} =
      Finset.univ.filter (fun j ↦ firstFailedSlot u F.1 - 1 ≤ j.val) by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hnone]
    change localCrossingCode (firstFailedSlot u F.1)
      (firstCrossingLabel F) i j = none ↔ _
    unfold localCrossingCode
    change firstCrossingLabel F < i at hi
    have hnotle : ¬ i ≤ firstCrossingLabel F := by omega
    simp [hnotle]
    ]
  exact card_filter_fin_ge hV

theorem card_crossingCodeLetter_none_before {k u v V : ℕ}
    (F : FailedWord k u v) (hV : firstFailedSlot u F.1 ≤ V)
    {i : Fin k} (hi : i ≤ (firstCrossingCode F).label)
    (hnone : (firstCrossingCode F).entries i = none) :
    Fintype.card (CrossingCodeLetter V (firstCrossingCode F) i) =
      V - firstFailedSlot u F.1 := by
  rw [Fintype.card_subtype]
  rw [show {j ∈ (Finset.univ : Finset (Fin V)) |
      localCrossingCode (firstCrossingCode F).slot
        (firstCrossingCode F).label i j = (firstCrossingCode F).entries i} =
      Finset.univ.filter (fun j ↦ firstFailedSlot u F.1 ≤ j.val) by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hnone]
    change localCrossingCode (firstFailedSlot u F.1)
      (firstCrossingLabel F) i j = none ↔ _
    unfold localCrossingCode
    change i ≤ firstCrossingLabel F at hi
    simp [hi]
    have hr : 1 ≤ firstFailedSlot u F.1 := (firstFailedSlot_spec F.2).1
    omega
    ]
  exact card_filter_fin_ge hV

/-- A code fiber is a Cartesian product of its independent one-letter
fibers. -/
noncomputable def wordsWithCrossingCodeEquiv {k v : ℕ}
    (C : FirstCrossingCode k) :
    ↑(wordsWithCrossingCode v C) ≃
      ((i : Fin k) → CrossingCodeLetter v C i) where
  toFun f i := ⟨f.1 i, (mem_wordsWithCrossingCode.mp f.2) i⟩
  invFun g := ⟨fun i ↦ (g i).1, mem_wordsWithCrossingCode.mpr fun i ↦ (g i).2⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    rfl
  right_inv g := by
    funext i
    apply Subtype.ext
    rfl

theorem card_wordsWithCrossingCode_eq_prod {k v : ℕ}
    (C : FirstCrossingCode k) :
    (wordsWithCrossingCode v C).card =
      ∏ i : Fin k, Fintype.card (CrossingCodeLetter v C i) := by
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr (wordsWithCrossingCodeEquiv C)).trans
    Fintype.card_pi

end Erdos446
