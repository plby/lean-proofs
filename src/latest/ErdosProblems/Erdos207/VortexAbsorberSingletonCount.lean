/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBankStrictCount
import ErdosProblems.Erdos207.AbsorberWellSpread
import ErdosProblems.Erdos207.VortexInducedCount
import ErdosProblems.Erdos207.VortexInducedWellSpread
import ErdosProblems.Erdos207.VortexSharpWeight

/-!
# The sharp singleton profile count for an absorber-induced family

This is the finite WS4 part of KSSS Lemma 7.2.  A2 puts local completions in
one bounded bank.  Every genuinely nonlocal completion has a nonempty exact
bank part and exposes a level-zero triangle, so the strict exact-bank count
absorbs the polynomial number of possible bank parts.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Sum of the fixed-order exact-bank profile constants. -/
def exactBankVortexOrderCoefficient (q ell : ℕ) : ℕ :=
  ∑ rho ∈ Icc 5 q, exactBankVortexCoefficient rho ell

/-- Exact classes whose bank part lies in the bounded A2-local bank. -/
def localBankProfiledCover
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q j : ℕ) (B R L : TripleSystemOn V)
    (t : VortexProfile ell) : ForbiddenFamilyOn V :=
  (Icc 5 q).biUnion fun rho ↦
    L.powerset.biUnion fun K ↦
      exactBankProfiledExtensions W rho j B R K t

/-- Exact classes with a nonempty bank part of size at most the cutoff. -/
def nonemptyBankProfiledCover
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (q j : ℕ) (B R : TripleSystemOn V)
    (t : VortexProfile ell) : ForbiddenFamilyOn V :=
  (Icc 5 q).biUnion fun rho ↦
    ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)).biUnion fun K ↦
      exactBankProfiledExtensions W rho j B R K t

/-- A triangle containing a vertex outside `U₁` has vortex level zero. -/
lemma Vortex.level_eq_zero_of_mem_not_mem_one
    {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (W : Vortex V (m + 1)) {T : TripleOn V} {v : V}
    (hvT : v ∈ T.1) (hv : v ∉ W.U 1) : W.level T = 0 := by
  apply Fin.ext
  simp only [Fin.val_zero]
  by_contra hnot
  have hone : (1 : Fin (m + 2)) ≤ W.level T := by
    exact Fin.mk_le_mk.mpr (Nat.one_le_iff_ne_zero.mpr hnot)
  have hsub : T.1 ⊆ W.U 1 := (W.subset_iff_le_level T 1).mpr hone
  exact hv (hsub hvT)

/-- A nonlocal A2 witness forces a positive first profile coordinate when
all nonroot absorber-support vertices lie outside `U₁`. -/
lemma outerProfile_zero_pos_of_meets_support
    {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (W : Vortex V (m + 1)) {H : SimpleGraph V} {X : Finset V}
    {S R : TripleSystemOn V} {T : TripleOn V} {v : V}
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hTS : T ∈ S) (hTR : T ∉ R) (hvT : v ∈ T.1)
    (hvH : v ∈ graphSupportFinset H) (hvX : v ∉ X) :
    0 < W.outerProfile (S \ R) 0 := by
  have hTdiff : T ∈ S \ R := mem_sdiff.mpr ⟨hTS, hTR⟩
  have hlevel : W.level T = 0 :=
    W.level_eq_zero_of_mem_not_mem_one hvT (hsep v hvH hvX)
  unfold Vortex.outerProfile Vortex.levelCount
  apply card_pos.mpr
  exact ⟨T, mem_inter.mpr
    ⟨hTdiff, W.mem_trianglesAtLevel_iff 0 T |>.mpr hlevel⟩⟩

/-- The retained A2 dichotomy covers a singleton profiled family by the
bounded local classes and the nonempty-bank strict classes. -/
lemma profiledExtensions_absorberInduced_subset_sharpCover
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) (t : VortexProfile (m + 1))
    (hA2 : HasAbsorberLocalization q M H X B) (hRq : R.card ≤ q)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t ⊆
        localBankProfiledCover W q j B R L t ∪
          nonemptyBankProfiledCover W q j B R t ∧
      (0 < t 0 ∨
        W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t ⊆
          localBankProfiledCover W q j B R L t) := by
  obtain ⟨L, hLB, hLM, hsplit⟩ :=
    absorberInduced_extensions_local_or_genuinely_meets_support hA2 hRq
  refine ⟨L, hLB, hLM, ?_, ?_⟩
  · intro S hS
    have hm := W.mem_profiledExtensions_iff
      (absorberInducedConfigurationsOn q j B) R t S |>.mp hS
    rcases hsplit S hm.1 hm.2.1 with hlocal | hsupport
    · obtain ⟨hScard, rho, hrho5, hrhoq, E, hE, hEout⟩ :=
        mem_absorberInducedConfigurationsOn_iff.mp hm.1
      let K := E ∩ B
      have hKL : K ⊆ L := hlocal rho E hrho5 hrhoq hE hEout
      apply mem_union_left
      apply mem_biUnion.mpr
      refine ⟨rho, mem_Icc.mpr ⟨hrho5, hrhoq⟩, ?_⟩
      apply mem_biUnion.mpr
      refine ⟨K, mem_powerset.mpr hKL, ?_⟩
      exact mem_exactBankProfiledExtensions_iff.mpr
        ⟨mem_exactBankOutsideExtensions_iff.mpr
          ⟨hScard, hm.2.1, E, hE, hEout, rfl⟩, hm.2.2⟩
    · obtain ⟨rho, E, T, v, hrho5, hrhoq, hE, hEout,
          hEnotL, hTS, hTR, hvT, hvH, hvX⟩ := hsupport
      let K := E ∩ B
      have hKnonempty : K.Nonempty := by
        rw [nonempty_iff_ne_empty]
        intro hKempty
        apply hEnotL
        rw [show E ∩ B = ∅ by exact hKempty]
        exact empty_subset L
      have hKB : K ⊆ B := inter_subset_right
      have hKcard : K.card ≤ q := by
        calc
          K.card ≤ E.card := card_le_card inter_subset_left
          _ = rho - 2 := hE.1.1
          _ ≤ q := by omega
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨rho, mem_Icc.mpr ⟨hrho5, hrhoq⟩, ?_⟩
      apply mem_biUnion.mpr
      refine ⟨K, mem_filter.mpr
        ⟨mem_subsetsUpToCard_iff.mpr ⟨hKB, hKcard⟩, hKnonempty⟩, ?_⟩
      have hScard := (mem_absorberInducedConfigurationsOn_iff.mp hm.1).1
      exact mem_exactBankProfiledExtensions_iff.mpr
        ⟨mem_exactBankOutsideExtensions_iff.mpr
          ⟨hScard, hm.2.1, E, hE, hEout, rfl⟩, hm.2.2⟩
  · by_cases ht0 : 0 < t 0
    · exact Or.inl ht0
    · right
      intro S hS
      have hm := W.mem_profiledExtensions_iff
        (absorberInducedConfigurationsOn q j B) R t S |>.mp hS
      rcases hsplit S hm.1 hm.2.1 with hlocal | hsupport
      · obtain ⟨hScard, rho, hrho5, hrhoq, E, hE, hEout⟩ :=
          mem_absorberInducedConfigurationsOn_iff.mp hm.1
        let K := E ∩ B
        apply mem_biUnion.mpr
        refine ⟨rho, mem_Icc.mpr ⟨hrho5, hrhoq⟩, ?_⟩
        apply mem_biUnion.mpr
        refine ⟨K, mem_powerset.mpr
          (hlocal rho E hrho5 hrhoq hE hEout), ?_⟩
        exact mem_exactBankProfiledExtensions_iff.mpr
          ⟨mem_exactBankOutsideExtensions_iff.mpr
            ⟨hScard, hm.2.1, E, hE, hEout, rfl⟩, hm.2.2⟩
      · obtain ⟨_rho, _E, T, v, _hrho5, _hrhoq, _hE, _hEout,
            _hEnotL, hTS, hTR, hvT, hvH, hvX⟩ := hsupport
        have hpos := outerProfile_zero_pos_of_meets_support
          W hsep hTS hTR hvT hvH hvX
        rw [hm.2.2] at hpos
        exact (ht0 hpos).elim

/-- Cardinal bound for the local cover. -/
theorem card_localBankProfiledCover_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R L : TripleSystemOn V)
    (t : VortexProfile ell) (hj : 3 ≤ j) (hR : R.Nonempty)
    (hRcard : R.card ≤ j - 2) (hterminal : 0 < W.terminalSize) :
    (localBankProfiledCover W q j B R L t).card ≤
      L.powerset.card * exactBankVortexOrderCoefficient q ell *
        (W.terminalSize ^
          (j - t.mass - vortexRootExponent j R.card) * W.profileScale t) := by
  calc
    (localBankProfiledCover W q j B R L t).card ≤
        ∑ rho ∈ Icc 5 q, ∑ K ∈ L.powerset,
          (exactBankProfiledExtensions W rho j B R K t).card := by
      unfold localBankProfiledCover
      exact card_biUnion_le.trans (sum_le_sum fun _rho _hrho ↦ card_biUnion_le)
    _ ≤ ∑ rho ∈ Icc 5 q, ∑ _K ∈ L.powerset,
        exactBankVortexCoefficient rho ell *
          (W.terminalSize ^
            (j - t.mass - vortexRootExponent j R.card) * W.profileScale t) := by
      apply sum_le_sum
      intro rho hrho
      apply sum_le_sum
      intro K _hK
      by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
      · obtain ⟨S, hSF⟩ := hF
        have hSexact := (mem_exactBankProfiledExtensions_iff.mp hSF).1
        have hjrho := exactBank_index_order_le hj hSexact
        simpa only [mul_assoc] using
          (card_exactBankProfiledExtensions_le
            (B := B) (R := R) (K := K) W t
              (mem_Icc.mp hrho).1 hj hjrho hR hRcard hterminal)
      · rw [not_nonempty_iff_eq_empty.mp hF]
        simp
    _ = L.powerset.card * exactBankVortexOrderCoefficient q ell *
        (W.terminalSize ^
          (j - t.mass - vortexRootExponent j R.card) * W.profileScale t) := by
      simp only [sum_const, nsmul_eq_mul]
      unfold exactBankVortexOrderCoefficient
      rw [Finset.mul_sum, Finset.sum_mul]
      apply sum_congr rfl
      intro rho _hrho
      simp only [Nat.cast_id]
      ac_rfl

/-- Cardinal bound for all nonempty-bank strict classes. -/
theorem card_nonemptyBankProfiledCover_mul_root_le
    {V : Type*} [Fintype V] [DecidableEq V] {m q j : ℕ}
    (W : Vortex V (m + 1)) (B R : TripleSystemOn V)
    (t : VortexProfile (m + 1)) (hj : 4 ≤ j)
    (hRcard : R.card = 1) (ht0 : 0 < t 0)
    (hterminal : 0 < W.terminalSize) :
    (W.U 0).card * (nonemptyBankProfiledCover W q j B R t).card ≤
      ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)).card *
        exactBankVortexOrderCoefficient q (m + 1) *
          (W.terminalSize ^ (j - t.mass - 3) * W.profileScale t) := by
  let banks := (subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)
  have hcover : (nonemptyBankProfiledCover W q j B R t).card ≤
      ∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        (exactBankProfiledExtensions W rho j B R K t).card := by
    unfold nonemptyBankProfiledCover
    exact card_biUnion_le.trans (sum_le_sum fun _rho _hrho ↦ card_biUnion_le)
  calc
    (W.U 0).card * (nonemptyBankProfiledCover W q j B R t).card ≤
        (W.U 0).card *
          (∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
            (exactBankProfiledExtensions W rho j B R K t).card) := by gcongr
    _ = ∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        (W.U 0).card *
          (exactBankProfiledExtensions W rho j B R K t).card := by
      simp only [mul_sum]
    _ ≤ ∑ rho ∈ Icc 5 q, ∑ _K ∈ banks,
        exactBankVortexCoefficient rho (m + 1) *
          W.terminalSize ^ (j - t.mass - 3) * W.profileScale t := by
      apply sum_le_sum
      intro rho hrho
      apply sum_le_sum
      intro K hK
      have hKnonempty : K.Nonempty := (mem_filter.mp hK).2
      by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
      · obtain ⟨S, hSF⟩ := hF
        have hSexact := (mem_exactBankProfiledExtensions_iff.mp hSF).1
        have hjrho := exactBank_index_order_le (by omega : 3 ≤ j) hSexact
        exact card_exactBankProfiledExtensions_mul_root_le_strict
          W t (mem_Icc.mp hrho).1 hj hjrho hRcard hKnonempty ht0 hterminal
      · rw [not_nonempty_iff_eq_empty.mp hF]
        simp
    _ = banks.card * exactBankVortexOrderCoefficient q (m + 1) *
        (W.terminalSize ^ (j - t.mass - 3) * W.profileScale t) := by
      simp only [sum_const, nsmul_eq_mul]
      unfold exactBankVortexOrderCoefficient
      rw [Finset.mul_sum, Finset.sum_mul]
      apply sum_congr rfl
      intro rho _hrho
      simp only [Nat.cast_id]
      ac_rfl
    _ = ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)).card *
        exactBankVortexOrderCoefficient q (m + 1) *
          (W.terminalSize ^ (j - t.mass - 3) * W.profileScale t) := rfl

/-- Sharp WS4 profile bound.  The bank-size hypothesis is the finite form of
the numerical inequality that absorbs all nonlocal exact bank parts. -/
theorem card_profiledExtensions_absorberInduced_singleton_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (T : TripleOn V)
    (t : VortexProfile (m + 1))
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hj : 4 ≤ j) (hjq : j ≤ q)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card) :
    (W.profiledExtensions (absorberInducedConfigurationsOn q j B) {T} t).card ≤
      ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) *
        W.terminalSize ^ (j - t.mass - 3) * W.profileScale t := by
  obtain ⟨L, _hLB, hLM, hcover, hzero⟩ :=
    profiledExtensions_absorberInduced_subset_sharpCover
      (j := j) W H X B {T} t hA2 (by simp; omega) hsep
  let base := W.terminalSize ^ (j - t.mass - 3) * W.profileScale t
  have hlocal := card_localBankProfiledCover_le (q := q) W B {T} L t
    (by omega : 3 ≤ j) (by simp) (by simp; omega) hterminal
  have hLpow : L.powerset.card ≤ 2 ^ M := by
    rw [card_powerset]
    exact pow_le_pow_right₀ (by omega) hLM
  have hlocalBase : (localBankProfiledCover W q j B {T} L t).card ≤
      L.powerset.card * exactBankVortexOrderCoefficient q (m + 1) * base := by
    simpa only [base, card_singleton, vortexRootExponent_one] using hlocal
  have hlocal' : (localBankProfiledCover W q j B {T} L t).card ≤
      2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base := by
    exact hlocalBase.trans (by gcongr)
  have htotal :
      (W.profiledExtensions (absorberInducedConfigurationsOn q j B) {T} t).card ≤
        (localBankProfiledCover W q j B {T} L t).card +
          (nonemptyBankProfiledCover W q j B {T} t).card :=
    (card_le_card hcover).trans (card_union_le _ _)
  rcases hzero with ht0 | hlocalOnly
  · have hstrict := card_nonemptyBankProfiledCover_mul_root_le
      (q := q) W B {T} t hj (by simp) ht0 hterminal
    have hbanks : ((subsetsUpToCard B q).filter
        (fun K ↦ K.Nonempty)).card ≤ (W.U 0).card := by
      exact (card_le_card (filter_subset (s := subsetsUpToCard B q)
        (p := fun K ↦ K.Nonempty))).trans hbank
    have hstrict' : (nonemptyBankProfiledCover W q j B {T} t).card ≤
        exactBankVortexOrderCoefficient q (m + 1) * base := by
      have hmul : (W.U 0).card *
          (nonemptyBankProfiledCover W q j B {T} t).card ≤
          (W.U 0).card *
            (exactBankVortexOrderCoefficient q (m + 1) * base) := by
        calc
        (W.U 0).card *
            (nonemptyBankProfiledCover W q j B {T} t).card ≤
          ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)).card *
            exactBankVortexOrderCoefficient q (m + 1) * base := by
              simpa only [base, mul_assoc] using hstrict
        _ ≤ (W.U 0).card *
            (exactBankVortexOrderCoefficient q (m + 1) * base) := by
          calc
            ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)).card *
                exactBankVortexOrderCoefficient q (m + 1) * base ≤
              (W.U 0).card *
                exactBankVortexOrderCoefficient q (m + 1) * base := by
              exact Nat.mul_le_mul_right base
                (Nat.mul_le_mul_right
                  (exactBankVortexOrderCoefficient q (m + 1)) hbanks)
            _ = (W.U 0).card *
                (exactBankVortexOrderCoefficient q (m + 1) * base) := by
              ring
      exact Nat.le_of_mul_le_mul_left hmul hroot
    calc
      (W.profiledExtensions
          (absorberInducedConfigurationsOn q j B) {T} t).card ≤
          (localBankProfiledCover W q j B {T} L t).card +
            (nonemptyBankProfiledCover W q j B {T} t).card := htotal
      _ ≤ 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base +
          exactBankVortexOrderCoefficient q (m + 1) * base :=
        Nat.add_le_add hlocal' hstrict'
      _ = ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) *
          W.terminalSize ^ (j - t.mass - 3) * W.profileScale t := by
        dsimp only [base]
        ring
  · have honly := card_le_card hlocalOnly
    calc
      (W.profiledExtensions
          (absorberInducedConfigurationsOn q j B) {T} t).card ≤
          (localBankProfiledCover W q j B {T} L t).card := honly
      _ ≤ 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base := hlocal'
      _ ≤ ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) *
          W.terminalSize ^ (j - t.mass - 3) * W.profileScale t := by
        calc
          2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base ≤
              ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) *
                base := by
            gcongr
            omega
          _ = ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) *
              W.terminalSize ^ (j - t.mass - 3) * W.profileScale t := by
            dsimp only [base]
            ring

/-- W1 support-branch count for all nonempty exact bank parts.  Relative to
WS4, one terminal-size factor remains because an arbitrary nonempty planted
root need not give the extra global vertex saving. -/
theorem card_nonemptyBankProfiledCover_mul_root_le_sharpW1
    {V : Type*} [Fintype V] [DecidableEq V] {m q j : ℕ}
    (W : Vortex V (m + 1)) (B R : TripleSystemOn V)
    (t : VortexProfile (m + 1)) (hj : 4 ≤ j)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (ht0 : 0 < t 0) (hterminal : 0 < W.terminalSize) :
    (W.U 0).card * (nonemptyBankProfiledCover W q j B R t).card ≤
      ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)).card *
        exactBankVortexOrderCoefficient q (m + 1) *
          (W.terminalSize *
            (W.terminalSize ^
              (j - t.mass - vortexRootExponent j R.card) *
                W.profileScale t)) := by
  let banks := (subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)
  let base := W.terminalSize ^
      (j - t.mass - vortexRootExponent j R.card) * W.profileScale t
  have hN : 1 ≤ W.terminalSize := by omega
  have hcover : (nonemptyBankProfiledCover W q j B R t).card ≤
      ∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        (exactBankProfiledExtensions W rho j B R K t).card := by
    unfold nonemptyBankProfiledCover
    exact card_biUnion_le.trans (sum_le_sum fun _rho _hrho ↦ card_biUnion_le)
  calc
    (W.U 0).card * (nonemptyBankProfiledCover W q j B R t).card ≤
        (W.U 0).card *
          (∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
            (exactBankProfiledExtensions W rho j B R K t).card) := by gcongr
    _ = ∑ rho ∈ Icc 5 q, ∑ K ∈ banks,
        (W.U 0).card *
          (exactBankProfiledExtensions W rho j B R K t).card := by
      simp only [mul_sum]
    _ ≤ ∑ rho ∈ Icc 5 q, ∑ _K ∈ banks,
        exactBankVortexCoefficient rho (m + 1) *
          (W.terminalSize * base) := by
      apply sum_le_sum
      intro rho hrho
      apply sum_le_sum
      intro K hK
      have hKnonempty : K.Nonempty := (mem_filter.mp hK).2
      by_cases hF : (exactBankProfiledExtensions W rho j B R K t).Nonempty
      · obtain ⟨S, hSF⟩ := hF
        have hSexact := (mem_exactBankProfiledExtensions_iff.mp hSF).1
        have hjrho := exactBank_index_order_le (by omega : 3 ≤ j) hSexact
        have hstrict :=
          card_exactBankProfiledExtensions_mul_root_le_nonempty_bank
            (B := B) W t (mem_Icc.mp hrho).1 hj hjrho hR hRcard
              hKnonempty ht0 hterminal
        apply hstrict.trans
        have hmass := VortexProfile.dropFirst_mass_add_one t ht0
        have hexp :
            (j - vortexRootExponent j R.card) - t.dropFirst.mass ≤
              1 + (j - t.mass - vortexRootExponent j R.card) := by
          omega
        have hpow : W.terminalSize ^
              ((j - vortexRootExponent j R.card) - t.dropFirst.mass) ≤
            W.terminalSize ^
              (1 + (j - t.mass - vortexRootExponent j R.card)) :=
          pow_le_pow_right₀ hN hexp
        dsimp only [base]
        calc
          exactBankVortexCoefficient rho (m + 1) *
                W.terminalSize ^
                  ((j - vortexRootExponent j R.card) - t.dropFirst.mass) *
                W.profileScale t ≤
              exactBankVortexCoefficient rho (m + 1) *
                W.terminalSize ^
                  (1 + (j - t.mass - vortexRootExponent j R.card)) *
                W.profileScale t := by gcongr
          _ = exactBankVortexCoefficient rho (m + 1) *
              (W.terminalSize *
                (W.terminalSize ^
                    (j - t.mass - vortexRootExponent j R.card) *
                  W.profileScale t)) := by
            rw [show 1 + (j - t.mass - vortexRootExponent j R.card) =
                (j - t.mass - vortexRootExponent j R.card) + 1 by omega,
              pow_succ]
            ring
      · rw [not_nonempty_iff_eq_empty.mp hF]
        simp
    _ = banks.card * exactBankVortexOrderCoefficient q (m + 1) *
        (W.terminalSize * base) := by
      simp only [sum_const, nsmul_eq_mul]
      unfold exactBankVortexOrderCoefficient
      rw [Finset.mul_sum, Finset.sum_mul]
      apply sum_congr rfl
      intro rho _hrho
      simp only [Nat.cast_id]
      ac_rfl
    _ = ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)).card *
        exactBankVortexOrderCoefficient q (m + 1) *
          (W.terminalSize *
            (W.terminalSize ^
              (j - t.mass - vortexRootExponent j R.card) *
                W.profileScale t)) := rfl

/-- Sharp, bank-independent W1 profile count in KSSS Lemma 7.2. -/
theorem card_profiledExtensions_absorberInduced_nonempty_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) (t : VortexProfile (m + 1))
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hj : 3 ≤ j) (hjq : j ≤ q)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card) :
    (W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card ≤
      ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
        W.terminalSize) *
          W.terminalSize ^
            (j - t.mass - vortexRootExponent j R.card) *
          W.profileScale t := by
  by_cases hj4 : 4 ≤ j
  · obtain ⟨L, _hLB, hLM, hcover, hzero⟩ :=
      profiledExtensions_absorberInduced_subset_sharpCover
        (j := j) W H X B R t hA2 (hRcard.trans (by omega)) hsep
    let base := W.terminalSize ^
      (j - t.mass - vortexRootExponent j R.card) * W.profileScale t
    have hN : 1 ≤ W.terminalSize := by omega
    have hbaseN : base ≤ W.terminalSize * base := by
      simpa only [mul_comm] using Nat.le_mul_of_pos_right base hterminal
    have hlocal := card_localBankProfiledCover_le (q := q) W B R L t
      hj hR hRcard hterminal
    have hLpow : L.powerset.card ≤ 2 ^ M := by
      rw [card_powerset]
      exact pow_le_pow_right₀ (by omega) hLM
    have hlocalBase : (localBankProfiledCover W q j B R L t).card ≤
        L.powerset.card * exactBankVortexOrderCoefficient q (m + 1) *
          base := by
      simpa only [base] using hlocal
    have hlocal' : (localBankProfiledCover W q j B R L t).card ≤
        2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base :=
      hlocalBase.trans (by gcongr)
    have htotal :
        (W.profiledExtensions
          (absorberInducedConfigurationsOn q j B) R t).card ≤
          (localBankProfiledCover W q j B R L t).card +
            (nonemptyBankProfiledCover W q j B R t).card :=
      (card_le_card hcover).trans (card_union_le _ _)
    rcases hzero with ht0 | hlocalOnly
    · have hstrict := card_nonemptyBankProfiledCover_mul_root_le_sharpW1
        (q := q) W B R t hj4 hR hRcard ht0 hterminal
      have hbanks : ((subsetsUpToCard B q).filter
          (fun K ↦ K.Nonempty)).card ≤ (W.U 0).card :=
        (card_le_card (filter_subset (s := subsetsUpToCard B q)
          (p := fun K ↦ K.Nonempty))).trans hbank
      have hstrict' : (nonemptyBankProfiledCover W q j B R t).card ≤
          exactBankVortexOrderCoefficient q (m + 1) *
            (W.terminalSize * base) := by
        have hmul : (W.U 0).card *
            (nonemptyBankProfiledCover W q j B R t).card ≤
            (W.U 0).card *
              (exactBankVortexOrderCoefficient q (m + 1) *
                (W.terminalSize * base)) := by
          calc
            (W.U 0).card *
                (nonemptyBankProfiledCover W q j B R t).card ≤
              ((subsetsUpToCard B q).filter
                  (fun K ↦ K.Nonempty)).card *
                exactBankVortexOrderCoefficient q (m + 1) *
                  (W.terminalSize * base) := by
                simpa only [base] using hstrict
            _ ≤ (W.U 0).card *
                (exactBankVortexOrderCoefficient q (m + 1) *
                  (W.terminalSize * base)) := by
              calc
                ((subsetsUpToCard B q).filter
                    (fun K ↦ K.Nonempty)).card *
                      exactBankVortexOrderCoefficient q (m + 1) *
                        (W.terminalSize * base) ≤
                    (W.U 0).card *
                      exactBankVortexOrderCoefficient q (m + 1) *
                        (W.terminalSize * base) := by gcongr
                _ = (W.U 0).card *
                    (exactBankVortexOrderCoefficient q (m + 1) *
                      (W.terminalSize * base)) := by ring
        exact Nat.le_of_mul_le_mul_left hmul hroot
      calc
        (W.profiledExtensions
            (absorberInducedConfigurationsOn q j B) R t).card ≤
            (localBankProfiledCover W q j B R L t).card +
              (nonemptyBankProfiledCover W q j B R t).card := htotal
        _ ≤ 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) *
              (W.terminalSize * base) +
            exactBankVortexOrderCoefficient q (m + 1) *
              (W.terminalSize * base) :=
          Nat.add_le_add
            (hlocal'.trans (Nat.mul_le_mul_left
              (2 ^ M * exactBankVortexOrderCoefficient q (m + 1)) hbaseN))
            hstrict'
        _ = ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
              W.terminalSize) * base := by ring
        _ = ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
              W.terminalSize) *
            W.terminalSize ^
              (j - t.mass - vortexRootExponent j R.card) *
            W.profileScale t := by
          dsimp only [base]
          ring
    · calc
        (W.profiledExtensions
            (absorberInducedConfigurationsOn q j B) R t).card ≤
            (localBankProfiledCover W q j B R L t).card :=
          card_le_card hlocalOnly
        _ ≤ 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base :=
          hlocal'
        _ ≤ 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) *
              (W.terminalSize * base) :=
          Nat.mul_le_mul_left
            (2 ^ M * exactBankVortexOrderCoefficient q (m + 1)) hbaseN
        _ ≤ ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
              W.terminalSize) * base := by
          have hc : 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) ≤
              (2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) :=
            Nat.mul_le_mul_right
              (exactBankVortexOrderCoefficient q (m + 1)) (by omega)
          simpa only [mul_assoc] using
            Nat.mul_le_mul_right (W.terminalSize * base) hc
        _ = ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
              W.terminalSize) *
            W.terminalSize ^
              (j - t.mass - vortexRootExponent j R.card) *
            W.profileScale t := by
          dsimp only [base]
          ring
  · obtain ⟨L, _hLB, hLM, _hcover, hzero⟩ :=
      profiledExtensions_absorberInduced_subset_sharpCover
        (j := j) W H X B R t hA2 (hRcard.trans (by omega)) hsep
    let base := W.terminalSize ^
      (j - t.mass - vortexRootExponent j R.card) * W.profileScale t
    have hlocal := card_localBankProfiledCover_le (q := q) W B R L t
      hj hR hRcard hterminal
    have hLpow : L.powerset.card ≤ 2 ^ M := by
      rw [card_powerset]
      exact pow_le_pow_right₀ (by omega) hLM
    have hlocal' : (localBankProfiledCover W q j B R L t).card ≤
        2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base := by
      apply hlocal.trans
      dsimp only [base]
      gcongr
    rcases hzero with ht0 | hlocalOnly
    · have hempty : W.profiledExtensions
          (absorberInducedConfigurationsOn q j B) R t = ∅ := by
        apply not_nonempty_iff_eq_empty.mp
        intro hnonempty
        obtain ⟨S, hS⟩ := hnonempty
        have hm := W.mem_profiledExtensions_iff
          (absorberInducedConfigurationsOn q j B) R t S |>.mp hS
        have hScard :=
          (mem_absorberInducedConfigurationsOn_iff.mp hm.1).1
        have hReq : R = S := by
          apply Finset.eq_of_subset_of_card_le hm.2.1
          have hRpos : 1 ≤ R.card := card_pos.mpr hR
          omega
        have htzero : t 0 = 0 := by
          rw [← hm.2.2, hReq, sdiff_self]
          simp [Vortex.outerProfile, Vortex.levelCount]
        omega
      rw [hempty]
      simp
    · calc
        (W.profiledExtensions
            (absorberInducedConfigurationsOn q j B) R t).card ≤
            (localBankProfiledCover W q j B R L t).card :=
          card_le_card hlocalOnly
        _ ≤ 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) * base :=
          hlocal'
        _ ≤ 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) *
              (W.terminalSize * base) := by
          apply Nat.mul_le_mul_left
          simpa only [mul_comm] using
            Nat.le_mul_of_pos_right base hterminal
        _ ≤ ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
              W.terminalSize) * base := by
          have hc : 2 ^ M * exactBankVortexOrderCoefficient q (m + 1) ≤
              (2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) :=
            Nat.mul_le_mul_right
              (exactBankVortexOrderCoefficient q (m + 1)) (by omega)
          simpa only [mul_assoc] using
            Nat.mul_le_mul_right (W.terminalSize * base) hc
        _ = ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
              W.terminalSize) *
            W.terminalSize ^
              (j - t.mass - vortexRootExponent j R.card) *
            W.profileScale t := by
          dsimp only [base]
          ring

/-- KSSS Lemma 7.2 with its sharp, bank-independent WS4 coefficient.  The
other well-spread fields retain the earlier coarse finite coefficient; only
WS4 is used in the rooted first-moment estimate. -/
theorem absorberInduced_vortexWellSpread_sharpWS4
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ W.U 1, x ∉ X → x ∉ graphSupportFinset H)
    (hj : 4 ≤ j) (hjq : j ≤ q)
    (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card) :
    VortexWellSpread W j (absorberInducedConfigurationsOn q j B)
      ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1))
      (inducedVortexCoefficient q (m + 1) B * W.terminalSize +
        W.terminalSize ^ 3) := by
  let coarse := absorberInduced_vortexWellSpread (q := q) W B
    (by omega : 3 ≤ j) hterminal
  refine ⟨coarse.uniform, coarse.extensions, coarse.equal_remainders,
    coarse.order_four_pair, ?_⟩
  intro T t
  apply card_profiledExtensions_absorberInduced_singleton_le_sharp
    W H X B T t hA2
  · intro x hxH hxX hxU
    exact hsep x hxU hxX hxH
  · exact hj
  · exact hjq
  · exact hterminal
  · have hsub : W.U (Fin.last (m + 1)) ⊆ W.U 0 :=
      W.antitone 0 (Fin.last (m + 1)) (Fin.zero_le _)
    exact hterminal.trans_le (by
      simpa only [Vortex.terminalSize] using card_le_card hsub)
  · exact hbank

/-- Density-sensitive weighted form of the preceding sharp WS4 estimate. -/
theorem extensionWeight_absorberInduced_vortex_singleton_le_sharpWS4
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (c : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ W.U 1, x ∉ X → x ∉ graphSupportFinset H)
    (hj : 4 ≤ j) (hjq : j ≤ q)
    (houter : ∀ i : Fin (m + 1), 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    (T : TripleOn V) :
    extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) {T} ≤
      (((j + 1) ^ (m + 1) *
        ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) : ℕ) :
          ℝ≥0) * c ^ (j - 3) := by
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (absorberInduced_vortexWellSpread_sharpWS4
      W H X B hA2 hsep hj hjq hterminal hbank).extensionWeight_singleton_le_sharp
        c (by omega : 3 ≤ j) houter hterminal T

/-- Density-sensitive weighted W1 estimate with the bank-independent A2
coefficient. -/
theorem extensionWeight_absorberInduced_vortex_nonempty_le_sharpA2
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (c : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ W.U 1, x ∉ X → x ∉ graphSupportFinset H)
    (hj : 3 ≤ j) (hjq : j ≤ q)
    (houter : ∀ i : Fin (m + 1), 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    (R : TripleSystemOn V) (hR : R.Nonempty)
    (hRcard : R.card ≤ j - 2) :
    extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) R ≤
      (((j + 1) ^ (m + 1) *
        ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
          W.terminalSize) : ℕ) : ℝ≥0) * c ^ (j - 2 - R.card) := by
  rw [extensionWeight_vortex_eq_profile_sum W
    (absorberInducedConfigurationsOn q j B)
      (fun E hE ↦ (absorberInduced_uniform E hE).1) c R]
  let z := (2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
    W.terminalSize
  have hroot : 0 < (W.U 0).card := by
    have hsub : W.U (Fin.last (m + 1)) ⊆ W.U 0 :=
      W.antitone 0 (Fin.last (m + 1)) (Fin.zero_le _)
    exact hterminal.trans_le (by
      simpa only [Vortex.terminalSize] using card_le_card hsub)
  calc
    ∑ t ∈ W.rootProfileSupport
          (absorberInducedConfigurationsOn q j B) R,
        ((W.profiledExtensions
          (absorberInducedConfigurationsOn q j B) R t).card : ℝ≥0) *
          vortexProfileWeight W c (j - 2 - R.card) t ≤
      ∑ _t ∈ W.rootProfileSupport
          (absorberInducedConfigurationsOn q j B) R,
        (z : ℝ≥0) * c ^ (j - 2 - R.card) := by
      apply sum_le_sum
      intro t ht
      by_cases hprof : (W.profiledExtensions
          (absorberInducedConfigurationsOn q j B) R t).Nonempty
      · obtain ⟨E, hE⟩ := hprof
        have hm := W.mem_profiledExtensions_iff
          (absorberInducedConfigurationsOn q j B) R t E |>.mp hE
        have hdiff : (E \ R).card = j - 2 - R.card := by
          rw [card_sdiff_of_subset hm.2.1, (absorberInduced_uniform E hm.1).1]
        have hmass : t.mass ≤ j - 2 - R.card := by
          rw [← hm.2.2]
          exact (W.outerProfile_mass_le_card (E \ R)).trans_eq hdiff
        have hexp :
            j - t.mass - vortexRootExponent j R.card ≤
              (j - 2 - R.card) - t.mass := by
          have hrootexp := add_two_le_vortexRootExponent j R.card
          omega
        have hN : 1 ≤ W.terminalSize := by omega
        calc
          ((W.profiledExtensions
                (absorberInducedConfigurationsOn q j B) R t).card : ℝ≥0) *
                vortexProfileWeight W c (j - 2 - R.card) t ≤
              (((z * W.terminalSize ^
                    (j - t.mass - vortexRootExponent j R.card) *
                  W.profileScale t : ℕ) : ℝ≥0) *
                vortexProfileWeight W c (j - 2 - R.card) t) := by
            gcongr
            exact_mod_cast
              card_profiledExtensions_absorberInduced_nonempty_le_sharp
                W H X B R t hA2
                  (fun x hxH hxX ↦ fun hxU ↦ hsep x hxU hxX hxH)
                  hj hjq hR hRcard hterminal hroot hbank
          _ ≤ (((z * W.terminalSize ^
                    ((j - 2 - R.card) - t.mass) *
                  W.profileScale t : ℕ) : ℝ≥0) *
                vortexProfileWeight W c (j - 2 - R.card) t) := by
            gcongr
          _ = (z : ℝ≥0) * c ^ (j - 2 - R.card) :=
            vortexProfileScaleWeight_eq W c t hmass houter hterminal
      · rw [not_nonempty_iff_eq_empty.mp hprof]
        simp
    _ = ((W.rootProfileSupport
          (absorberInducedConfigurationsOn q j B) R).card : ℝ≥0) *
        ((z : ℝ≥0) * c ^ (j - 2 - R.card)) := by simp
    _ ≤ (((j + 1) ^ (m + 1) : ℕ) : ℝ≥0) *
        ((z : ℝ≥0) * c ^ (j - 2 - R.card)) := by
      gcongr
      exact_mod_cast W.card_rootProfileSupport_le
        (absorberInducedConfigurationsOn q j B)
          (fun E hE ↦ (absorberInduced_uniform E hE).1) R
    _ = (((j + 1) ^ (m + 1) *
          ((2 ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1) *
            W.terminalSize) : ℕ) : ℝ≥0) *
          c ^ (j - 2 - R.card) := by
      dsimp only [z]
      push_cast
      ring

end

end Erdos207
