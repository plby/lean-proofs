/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBankSignedStrictCount
import ErdosProblems.Erdos207.SourceVortexWellSpread
import ErdosProblems.Erdos207.VortexAbsorberSingletonCount

/-! # Summing source-correct profile bounds over exact bank classes -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def bankProfiledCover
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q j : ℕ) (B R : TripleSystemOn V)
    (banks : Finset (TripleSystemOn V)) (t : VortexProfile ell) : ForbiddenFamilyOn V :=
  (Icc 5 q).biUnion fun rho ↦
    banks.biUnion fun K ↦ exactBankProfiledExtensions W rho j B R K t

theorem card_bankProfiledCover_mul_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V)
    (banks : Finset (TripleSystemOn V)) (t : VortexProfile ell) (a b : ℝ≥0)
    (hcount : ∀ rho ∈ Icc 5 q, ∀ K ∈ banks,
      a * ((exactBankProfiledExtensions W rho j B R K t).card : ℝ≥0) ≤
        (exactBankVortexCoefficient rho ell : ℝ≥0) * b) :
    a * ((bankProfiledCover W q j B R banks t).card : ℝ≥0) ≤
      banks.card * (exactBankVortexOrderCoefficient q ell : ℝ≥0) * b := by
  have hcover : (bankProfiledCover W q j B R banks t).card ≤
      ∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        (exactBankProfiledExtensions W rho j B R K t).card := by
    exact card_biUnion_le.trans (sum_le_sum fun _ _ ↦ card_biUnion_le)
  have hcover' : ((bankProfiledCover W q j B R banks t).card : ℝ≥0) ≤
      ∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        ((exactBankProfiledExtensions W rho j B R K t).card : ℝ≥0) := by
    exact_mod_cast hcover
  calc
    _ ≤ a * (∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        ((exactBankProfiledExtensions W rho j B R K t).card : ℝ≥0)) :=
      mul_le_mul_of_nonneg_left hcover' zero_le
    _ = ∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        a * ((exactBankProfiledExtensions W rho j B R K t).card : ℝ≥0) := by
      simp only [mul_sum]
    _ ≤ ∑ rho ∈ Icc 5 q, ∑ _K ∈ banks,
        (exactBankVortexCoefficient rho ell : ℝ≥0) * b :=
      sum_le_sum fun rho hr ↦ sum_le_sum (hcount rho hr)
    _ = _ := by
      simp only [sum_const, nsmul_eq_mul, exactBankVortexOrderCoefficient, Nat.cast_sum,
        mul_sum, sum_mul, mul_assoc]

theorem card_bankProfiledCover_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V)
    (banks : Finset (TripleSystemOn V)) (t : VortexProfile ell)
    (hj : 3 ≤ j) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hterminal : 0 < W.terminalSize) :
    ((bankProfiledCover W q j B R banks t).card : ℝ≥0) ≤
      banks.card * (exactBankVortexOrderCoefficient q ell : ℝ≥0) *
        W.sourceProfileScale (j - vortexRootExponent j R.card) t := by
  simpa only [one_mul] using card_bankProfiledCover_mul_le W B R banks t 1
    (W.sourceProfileScale (j - vortexRootExponent j R.card) t) (by
      intro rho hr K _hK
      by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
      · obtain ⟨S, hS⟩ := hF
        have hjrho := exactBank_index_order_le hj (mem_exactBankProfiledExtensions_iff.mp hS).1
        rw [one_mul, W.le_mul_sourceProfileScale_iff _ _ _ _ hterminal]
        exact_mod_cast card_exactBankProfiledExtensions_mul_terminal_pow_le
          W t (mem_Icc.mp hr).1 hj hjrho hR hRcard hterminal
      · simp only [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero, mul_zero, zero_le])

theorem card_bankProfiledCover_singleton_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V)
    (banks : Finset (TripleSystemOn V)) (t : VortexProfile ell)
    (hj : 4 ≤ j) (hRcard : R.card = 1)
    (hbanks : ∀ K ∈ banks, K.Nonempty) (hterminal : 0 < W.terminalSize) :
    ((bankProfiledCover W q j B R banks t).card : ℝ≥0) ≤
      banks.card * (exactBankVortexOrderCoefficient q ell : ℝ≥0) * W.sourceProfileScale (j - 4) t := by
  simpa only [one_mul] using card_bankProfiledCover_mul_le W B R banks t 1
    (W.sourceProfileScale (j - 4) t) (by
      intro rho hr K hK
      by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
      · obtain ⟨S, hS⟩ := hF
        have hjrho := exactBank_index_order_le (by omega : 3 ≤ j)
          (mem_exactBankProfiledExtensions_iff.mp hS).1
        rw [one_mul, W.le_mul_sourceProfileScale_iff _ _ _ _ hterminal]
        exact_mod_cast card_exactBankProfiledExtensions_mul_terminal_pow_le_singleton_nonempty
          W t (mem_Icc.mp hr).1 hj hjrho hRcard (hbanks K hK) hterminal
      · simp only [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero, mul_zero, zero_le])

theorem card_bankProfiledCover_mul_root_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {m q j : ℕ}
    (W : Vortex V (m + 1)) (B R : TripleSystemOn V)
    (banks : Finset (TripleSystemOn V)) (t : VortexProfile (m + 1))
    (hj : 4 ≤ j) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hbanks : ∀ K ∈ banks, K.Nonempty) (ht0 : 0 < t 0) (hterminal : 0 < W.terminalSize) :
    ((W.U 0).card : ℝ≥0) * (bankProfiledCover W q j B R banks t).card ≤
      banks.card * (exactBankVortexOrderCoefficient q (m + 1) : ℝ≥0) *
        (W.terminalSize * W.sourceProfileScale (j - vortexRootExponent j R.card) t) := by
  apply card_bankProfiledCover_mul_le
  intro rho hr K hK
  by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
  · obtain ⟨S, hS⟩ := hF
    have hjrho := exactBank_index_order_le (by omega : 3 ≤ j)
      (mem_exactBankProfiledExtensions_iff.mp hS).1
    rw [← mul_assoc, W.le_mul_sourceProfileScale_iff _ _ _ _ hterminal]
    have h := card_exactBankProfiledExtensions_mul_root_terminal_pow_le_nonempty_bank
      (B := B) W t (mem_Icc.mp hr).1 hj hjrho hR hRcard (hbanks K hK) ht0 hterminal
    rw [pow_succ] at h
    have h' : (W.U 0).card * (exactBankProfiledExtensions W rho j B R K t).card *
        W.terminalSize ^ t.mass ≤
        (exactBankVortexCoefficient rho (m + 1) * W.terminalSize) *
          W.terminalSize ^ (j - vortexRootExponent j R.card) * W.profileScale t := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    exact_mod_cast h'
  · simp only [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero, mul_zero, zero_le]

theorem card_bankProfiledCover_singleton_mul_root_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {m q j : ℕ}
    (W : Vortex V (m + 1)) (B R : TripleSystemOn V)
    (banks : Finset (TripleSystemOn V)) (t : VortexProfile (m + 1))
    (hj : 4 ≤ j) (hRcard : R.card = 1)
    (hbanks : ∀ K ∈ banks, K.Nonempty) (ht0 : 0 < t 0) (hterminal : 0 < W.terminalSize) :
    ((W.U 0).card : ℝ≥0) * (bankProfiledCover W q j B R banks t).card ≤
      banks.card * (exactBankVortexOrderCoefficient q (m + 1) : ℝ≥0) * W.sourceProfileScale (j - 3) t := by
  apply card_bankProfiledCover_mul_le
  intro rho hr K hK
  by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
  · obtain ⟨S, hS⟩ := hF
    have hjrho := exactBank_index_order_le (by omega : 3 ≤ j)
      (mem_exactBankProfiledExtensions_iff.mp hS).1
    rw [W.le_mul_sourceProfileScale_iff _ _ _ _ hterminal]
    exact_mod_cast card_exactBankProfiledExtensions_mul_root_terminal_pow_le_singleton_nonempty
      W t (mem_Icc.mp hr).1 hj hjrho hRcard (hbanks K hK) ht0 hterminal
  · simp only [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero, mul_zero, zero_le]

end

end Erdos207
