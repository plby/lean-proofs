/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovFirstCrossingCodePreservation

/-!
# Erdős Problem 446: summing the finite first-crossing comparison

The truncated alphabet has `v-(2w+2)` letters.  Every word over it crosses
the barrier.  We partition those words by their first-crossing codes, enlarge
each code fiber to the full alphabet, and sum the fiberwise exponential
comparison.
-/

namespace Erdos446

open Finset

theorem exp_mul_card_crossingCode_truncated_le_full
    {k u v w : ℕ} (hrel : u + v = k + w) (htrunc : 2 * w + 2 ≤ v)
    (F : FailedWord k u (v - (2 * w + 2))) :
    Real.exp (2 * (w : ℝ) + 2) *
        (wordsWithCrossingCode (v - (2 * w + 2))
          (firstCrossingCode F)).card ≤
      (wordsWithCrossingCode v (firstCrossingCode F)).card := by
  let t := v - (2 * w + 2)
  let r := firstFailedSlot u F.1
  let N := k - (u + r)
  let p := crossingSuffixAfterCount F
  have hrT : r ≤ t := by
    simpa [r, t] using (firstFailedSlot_spec F.2).2.1
  have htV : t ≤ v := by omega
  have hrV : r ≤ v := hrT.trans htV
  have hpN : p ≤ N := by
    simpa [p, N, r] using crossingSuffixAfterCount_le F
  have hwN : w + 2 ≤ N := by
    dsimp [N, r, t] at *
    omega
  have hrpos : 1 ≤ r := by
    simpa [r] using (firstFailedSlot_spec F.2).1
  have htadd : t + (2 * w + 2) = v := by
    dsimp [t]
    exact Nat.sub_add_cancel htrunc
  have hurk : u + r ≤ k := by omega
  have hNadd : N + (u + r) = k := by
    dsimp [N]
    exact Nat.sub_add_cancel hurk
  have hlowAfter : t - (r - 1) = N - w - 1 := by
    omega
  have hlowBefore : t - r = N - w - 2 := by
    omega
  have hfullAfter : v - (r - 1) = N + w + 1 := by
    omega
  have hfullBefore : v - r = N + w := by
    omega
  have hexp : k - (u + firstFailedSlot u F.1) - crossingSuffixAfterCount F =
      N - p := by rfl
  have hpdef : crossingSuffixAfterCount F = p := rfl
  rw [card_wordsWithCrossingCode_eq_suffix_powers F le_rfl hrT,
    card_wordsWithCrossingCode_eq_suffix_powers F htV hrV]
  simp only [Nat.cast_mul, Nat.cast_pow]
  rw [hlowAfter, hlowBefore, hfullAfter, hfullBefore, hexp, hpdef]
  convert exp_mul_truncated_suffix_le_full_suffix hwN hpN using 1
  all_goals ring_nf

theorem not_wordBarrier_of_terminal_prefix {k u t : ℕ}
    (ht : 0 < t) (hut : u + t ≤ k) (f : Fin k → Fin t) :
    ¬ SatisfiesWordBarrier u f := by
  intro hgood
  have hlt := hgood t ht le_rfl
  rw [wordPrefix_eq_k_of_length_le f le_rfl] at hlt
  omega

/-- A word on a sufficiently short alphabet, regarded canonically as a
failed word. -/
noncomputable def terminalFailedWord {k u t : ℕ}
    (ht : 0 < t) (hut : u + t ≤ k) (f : Fin k → Fin t) :
    FailedWord k u t :=
  ⟨f, not_wordBarrier_of_terminal_prefix ht hut f⟩

/-- First-crossing code of a word on the truncated alphabet. -/
noncomputable def terminalCrossingCode {k u t : ℕ}
    (ht : 0 < t) (hut : u + t ≤ k) (f : Fin k → Fin t) :
    FirstCrossingCode k :=
  firstCrossingCode (terminalFailedWord ht hut f)

theorem wordsWithCrossingCode_eq_terminalCodeFiber {k u t : ℕ}
    (ht : 0 < t) (hut : u + t ≤ k) {C : FirstCrossingCode k}
    (hC : C ∈ (Finset.univ : Finset (Fin k → Fin t)).image
      (terminalCrossingCode ht hut)) :
    wordsWithCrossingCode t C =
      (Finset.univ : Finset (Fin k → Fin t)).filter
        (fun f ↦ terminalCrossingCode ht hut f = C) := by
  classical
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hC
  ext g
  rw [mem_wordsWithCrossingCode]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hg
    have hgmem : g ∈ wordsWithCrossingCode t
        (firstCrossingCode (terminalFailedWord ht hut f)) :=
      mem_wordsWithCrossingCode.mpr hg
    have hrT : firstFailedSlot u (terminalFailedWord ht hut f).1 ≤ t :=
      (firstFailedSlot_spec (terminalFailedWord ht hut f).2).2.1
    have hpres := firstCrossingCode_eq_of_mem_crossingCode
      (terminalFailedWord ht hut f) hrT hgmem
    simpa [terminalCrossingCode, terminalFailedWord] using hpres
  · intro hcode
    have hown := word_mem_own_firstCrossingCode (terminalFailedWord ht hut g)
    have hcode' : firstCrossingCode (terminalFailedWord ht hut g) =
        firstCrossingCode (terminalFailedWord ht hut f) := by
      simpa [terminalCrossingCode] using hcode
    have hown' := mem_wordsWithCrossingCode.mp hown
    intro i
    have hi := hown' i
    change localCrossingCode (firstCrossingCode (terminalFailedWord ht hut g)).slot
      (firstCrossingCode (terminalFailedWord ht hut g)).label i (g i) =
        (firstCrossingCode (terminalFailedWord ht hut g)).entries i at hi
    rw [hcode'] at hi
    simpa [terminalCrossingCode] using hi

theorem exp_mul_truncated_words_le_card_failedBarrierWords
    {k u v w : ℕ} (hrel : u + v = k + w) (htrunc : 2 * w + 2 ≤ v) :
    Real.exp (2 * (w : ℝ) + 2) *
        ((v - (2 * w + 2) : ℕ) : ℝ) ^ k ≤
      (failedBarrierWords k u v).card := by
  classical
  let t := v - (2 * w + 2)
  have htadd : t + (2 * w + 2) = v := by
    dsimp [t]
    exact Nat.sub_add_cancel htrunc
  have hut : u + t ≤ k := by omega
  have hkpos : 0 < k := by omega
  by_cases htzero : t = 0
  · have hzero : ((t : ℝ) ^ k) = 0 := by simp [htzero, hkpos.ne']
    change Real.exp (2 * (w : ℝ) + 2) * (t : ℝ) ^ k ≤ _
    rw [hzero, mul_zero]
    positivity
  · have htpos : 0 < t := Nat.pos_of_ne_zero htzero
    let code : (Fin k → Fin t) → FirstCrossingCode k :=
      terminalCrossingCode htpos hut
    let codes : Finset (FirstCrossingCode k) :=
      (Finset.univ : Finset (Fin k → Fin t)).image code
    have hlowSum : t ^ k =
        ∑ C ∈ codes, (wordsWithCrossingCode t C).card := by
      calc
        t ^ k = (Finset.univ : Finset (Fin k → Fin t)).card := by simp
        _ = ∑ C ∈ codes,
            ((Finset.univ : Finset (Fin k → Fin t)).filter
              (fun f ↦ code f = C)).card := by
          simpa [codes] using Finset.card_eq_sum_card_image code
            (Finset.univ : Finset (Fin k → Fin t))
        _ = ∑ C ∈ codes, (wordsWithCrossingCode t C).card := by
          apply Finset.sum_congr rfl
          intro C hC
          have hC' : C ∈ (Finset.univ : Finset (Fin k → Fin t)).image
              (terminalCrossingCode htpos hut) := by
            simpa only [codes, code] using hC
          rw [wordsWithCrossingCode_eq_terminalCodeFiber htpos hut hC']
    have hfiber : ∀ C ∈ codes,
        Real.exp (2 * (w : ℝ) + 2) *
            (wordsWithCrossingCode t C).card ≤
          (wordsWithCrossingCode v C).card := by
      intro C hC
      have hC' : C ∈ (Finset.univ : Finset (Fin k → Fin t)).image code := by
        simpa only [codes] using hC
      obtain ⟨f, _, hcode⟩ := Finset.mem_image.mp hC'
      rw [← hcode]
      simpa [t, code, terminalCrossingCode] using
        exp_mul_card_crossingCode_truncated_le_full hrel htrunc
          (terminalFailedWord htpos hut f)
    have hpair : (codes : Set (FirstCrossingCode k)).PairwiseDisjoint
        (fun C ↦ wordsWithCrossingCode v C) := by
      intro C hC D hD hCD
      change Disjoint (wordsWithCrossingCode v C) (wordsWithCrossingCode v D)
      rw [Finset.disjoint_left]
      intro g hgC hgD
      have hCfin : C ∈ codes := by exact hC
      have hDfin : D ∈ codes := by exact hD
      have hC' : C ∈ (Finset.univ : Finset (Fin k → Fin t)).image code := by
        simpa only [codes] using hCfin
      have hD' : D ∈ (Finset.univ : Finset (Fin k → Fin t)).image code := by
        simpa only [codes] using hDfin
      obtain ⟨fC, _, hcodeC⟩ := Finset.mem_image.mp hC'
      obtain ⟨fD, _, hcodeD⟩ := Finset.mem_image.mp hD'
      have hrCv : firstFailedSlot u (terminalFailedWord htpos hut fC).1 ≤ v :=
        ((firstFailedSlot_spec (terminalFailedWord htpos hut fC).2).2.1).trans
          (by dsimp [t] at *; omega)
      have hrDv : firstFailedSlot u (terminalFailedWord htpos hut fD).1 ≤ v :=
        ((firstFailedSlot_spec (terminalFailedWord htpos hut fD).2).2.1).trans
          (by dsimp [t] at *; omega)
      have hcodeC' : firstCrossingCode (terminalFailedWord htpos hut fC) = C := by
        simpa [code, terminalCrossingCode] using hcodeC
      have hcodeD' : firstCrossingCode (terminalFailedWord htpos hut fD) = D := by
        simpa [code, terminalCrossingCode] using hcodeD
      have hpresC := firstCrossingCode_eq_of_mem_crossingCode
        (terminalFailedWord htpos hut fC) hrCv (by
          rw [hcodeC']
          exact hgC)
      have hpresD := firstCrossingCode_eq_of_mem_crossingCode
        (terminalFailedWord htpos hut fD) hrDv (by
          rw [hcodeD']
          exact hgD)
      apply hCD
      rw [← hcodeC', ← hcodeD']
      exact hpresC.symm.trans hpresD
    let upperUnion : Finset (Fin k → Fin v) :=
      codes.biUnion (wordsWithCrossingCode v)
    have hupperCard : upperUnion.card =
        ∑ C ∈ codes, (wordsWithCrossingCode v C).card := by
      simpa [upperUnion] using Finset.card_biUnion hpair
    have hupperSub : upperUnion ⊆ failedBarrierWords k u v := by
      intro g hg
      obtain ⟨C, hC, hgC⟩ := Finset.mem_biUnion.mp (by
        simpa [upperUnion] using hg)
      have hC' : C ∈ (Finset.univ : Finset (Fin k → Fin t)).image code := by
        simpa only [codes] using hC
      obtain ⟨f, _, hcode⟩ := Finset.mem_image.mp hC'
      have hcode' : firstCrossingCode (terminalFailedWord htpos hut f) = C := by
        simpa [code, terminalCrossingCode] using hcode
      rw [mem_failedBarrierWords]
      apply not_wordBarrier_of_mem_crossingCode (terminalFailedWord htpos hut f)
      · exact ((firstFailedSlot_spec (terminalFailedWord htpos hut f).2).2.1).trans
          (by dsimp [t] at *; omega)
      · rw [hcode']
        exact hgC
    have hcardUpper : upperUnion.card ≤
        (failedBarrierWords k u v).card := Finset.card_le_card hupperSub
    change Real.exp (2 * (w : ℝ) + 2) * (t : ℝ) ^ k ≤ _
    calc
      Real.exp (2 * (w : ℝ) + 2) * (t : ℝ) ^ k =
          ∑ C ∈ codes, Real.exp (2 * (w : ℝ) + 2) *
            (wordsWithCrossingCode t C).card := by
        rw [← Nat.cast_pow, hlowSum, Nat.cast_sum]
        simp [Finset.mul_sum]
      _ ≤ ∑ C ∈ codes, ((wordsWithCrossingCode v C).card : ℝ) := by
        exact Finset.sum_le_sum fun C hC ↦ hfiber C hC
      _ = (upperUnion.card : ℝ) := by
        exact_mod_cast hupperCard.symm
      _ ≤ ((failedBarrierWords k u v).card : ℝ) := by
        exact_mod_cast hcardUpper

end Erdos446
