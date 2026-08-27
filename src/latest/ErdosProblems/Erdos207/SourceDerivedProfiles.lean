/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceAbsorberProfiles
import ErdosProblems.Erdos207.DerivedAbsorberCount

/-! # The additional singleton saving for derived absorber configurations -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem profiledExtensions_derived_subset_nonemptyBankCover
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V) (t : VortexProfile ell) :
    W.profiledExtensions (derivedAbsorberConfigurations q j B) R t ⊆
      bankProfiledCover W q j B R
        ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)) t := by
  classical
  intro S hS
  have hm := (W.mem_profiledExtensions_iff _ _ _ _).mp hS
  obtain ⟨hSF, rho, hrho5, hrhoq, E, hE, hEout, hbank⟩ := mem_filter.mp hm.1
  have hcard := (mem_absorberInducedConfigurationsOn_iff.mp hSF).1
  have hK : E ∩ B ∈ subsetsUpToCard B q := by
    apply mem_subsetsUpToCard_iff.mpr
    refine ⟨inter_subset_right, ?_⟩
    have h := card_le_card (inter_subset_left : E ∩ B ⊆ E)
    rw [hE.1.1] at h
    omega
  apply mem_biUnion.mpr
  refine ⟨rho, mem_Icc.mpr ⟨hrho5, hrhoq⟩, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨E ∩ B, mem_filter.mpr ⟨hK, hbank⟩, ?_⟩
  exact mem_exactBankProfiledExtensions_iff.mpr
    ⟨mem_exactBankOutsideExtensions_iff.mpr ⟨hcard, hm.2.1, E, hE, hEout, rfl⟩, hm.2.2⟩

theorem profiledExtensions_derived_subset_localBankCover_of_zero
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) (t : VortexProfile (m + 1))
    (hA2 : HasAbsorberLocalization q M H X B) (hRq : R.card ≤ q)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1) (ht0 : t 0 = 0) :
    ∃ L : TripleSystemOn V, L ⊆ B ∧ L.card ≤ M ∧
      W.profiledExtensions (derivedAbsorberConfigurations q j B) R t ⊆
        bankProfiledCover W q j B R (L.powerset.filter (fun K ↦ K.Nonempty)) t := by
  classical
  obtain ⟨L, hLB, hLM, hsplit⟩ :=
    absorberInduced_extensions_local_or_genuinely_meets_support (j := j) hA2 hRq
  refine ⟨L, hLB, hLM, ?_⟩
  intro S hS
  have hm := (W.mem_profiledExtensions_iff _ _ _ _).mp hS
  obtain ⟨hSF, rho, hrho5, hrhoq, E, hE, hEout, hbank⟩ := mem_filter.mp hm.1
  have hcard := (mem_absorberInducedConfigurationsOn_iff.mp hSF).1
  rcases hsplit S hSF hm.2.1 with hlocal | hsupport
  · apply mem_biUnion.mpr
    refine ⟨rho, mem_Icc.mpr ⟨hrho5, hrhoq⟩, ?_⟩
    apply mem_biUnion.mpr
    refine ⟨E ∩ B, mem_filter.mpr
      ⟨mem_powerset.mpr (hlocal rho E hrho5 hrhoq hE hEout), hbank⟩, ?_⟩
    exact mem_exactBankProfiledExtensions_iff.mpr
      ⟨mem_exactBankOutsideExtensions_iff.mpr ⟨hcard, hm.2.1, E, hE, hEout, rfl⟩, hm.2.2⟩
  · obtain ⟨_, _, T, v, _, _, _, _, _, hTS, hTR, hvT, hvH, hvX⟩ := hsupport
    have hpos := outerProfile_zero_pos_of_meets_support W hsep hTS hTR hvT hvH hvX
    rw [hm.2.2, ht0] at hpos
    omega

theorem card_profiledExtensions_derived_singleton_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (T : TripleOn V) (t : VortexProfile ell)
    (hj : 4 ≤ j) (hterminal : 0 < W.terminalSize) :
    ((W.profiledExtensions (derivedAbsorberConfigurations q j B) {T} t).card : ℝ≥0) ≤
      (subsetsUpToCard B q).card * (exactBankVortexOrderCoefficient q ell : ℝ≥0) *
        W.sourceProfileScale (j - 4) t := by
  let banks := (subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)
  have hsub : ((W.profiledExtensions (derivedAbsorberConfigurations q j B) {T} t).card : ℝ≥0) ≤
      (bankProfiledCover W q j B {T} banks t).card := by
    exact_mod_cast card_le_card (profiledExtensions_derived_subset_nonemptyBankCover W B {T} t)
  have h := card_bankProfiledCover_singleton_source_le (q := q) W B {T} banks t hj
    (by simp) (fun K hK ↦ (mem_filter.mp hK).2) hterminal
  have hbanks : (banks.card : ℝ≥0) ≤ (subsetsUpToCard B q).card := by
    exact_mod_cast card_le_card (filter_subset (s := subsetsUpToCard B q) (p := fun K ↦ K.Nonempty))
  exact (hsub.trans h).trans (by gcongr)

theorem card_profiledExtensions_derived_singleton_source_le_localized
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (T : TripleOn V) (t : VortexProfile (m + 1)) (z : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hj : 4 ≤ j) (hjq : j ≤ q)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbank : ((subsetsUpToCard B q).card : ℝ≥0) * W.terminalSize ≤ (W.U 0).card * z) :
    ((W.profiledExtensions (derivedAbsorberConfigurations q j B) {T} t).card : ℝ≥0) ≤
      ((2 : ℝ≥0) ^ M + z) * exactBankVortexOrderCoefficient q (m + 1) * W.sourceProfileScale (j - 4) t := by
  let C : ℝ≥0 := exactBankVortexOrderCoefficient q (m + 1)
  let s := W.sourceProfileScale (j - 4) t
  by_cases ht0 : 0 < t 0
  · let banks := (subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)
    have hsub : ((W.profiledExtensions (derivedAbsorberConfigurations q j B) {T} t).card : ℝ≥0) ≤
        (bankProfiledCover W q j B {T} banks t).card := by
      exact_mod_cast card_le_card (profiledExtensions_derived_subset_nonemptyBankCover W B {T} t)
    have h := card_bankProfiledCover_singleton_mul_root_source_le (q := q) W B {T} banks t hj
      (by simp) (fun K hK ↦ (mem_filter.mp hK).2) ht0 hterminal
    have heq : W.sourceProfileScale (j - 3) t = W.terminalSize * s := by
      dsimp only [s, Vortex.sourceProfileScale]
      rw [show j - 3 = j - 4 + 1 by omega, pow_succ]
      ring
    rw [heq] at h
    have hbanks : (banks.card : ℝ≥0) ≤ (subsetsUpToCard B q).card := by
      exact_mod_cast card_le_card (filter_subset (s := subsetsUpToCard B q) (p := fun K ↦ K.Nonempty))
    have hNpos : (0 : ℝ≥0) < (W.U 0).card := by exact_mod_cast hroot
    have hsmall : ((bankProfiledCover W q j B {T} banks t).card : ℝ≥0) ≤ z * C * s := by
      apply (mul_le_mul_iff_right₀ hNpos).mp
      calc
        _ ≤ banks.card * C * (W.terminalSize * s) := h
        _ = ((banks.card : ℝ≥0) * W.terminalSize) * C * s := by ring
        _ ≤ ((W.U 0).card * z) * C * s := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_right hbanks zero_le).trans hbank) zero_le) zero_le
        _ = _ := by ring
    exact (hsub.trans hsmall).trans (by change z * C * s ≤ _; gcongr; exact le_add_self)
  · obtain ⟨L, _hLB, hLM, hsub⟩ := profiledExtensions_derived_subset_localBankCover_of_zero
      (j := j) W H X B {T} t hA2 (by simp; omega) hsep (by omega)
    have hsub' : ((W.profiledExtensions (derivedAbsorberConfigurations q j B) {T} t).card : ℝ≥0) ≤
        (bankProfiledCover W q j B {T} (L.powerset.filter (fun K ↦ K.Nonempty)) t).card := by
      exact_mod_cast card_le_card hsub
    have h := card_bankProfiledCover_singleton_source_le (q := q) W B {T}
      (L.powerset.filter (fun K ↦ K.Nonempty)) t hj (by simp)
      (fun K hK ↦ (mem_filter.mp hK).2) hterminal
    have hL : (((L.powerset.filter (fun K ↦ K.Nonempty)).card) : ℝ≥0) ≤ (2 : ℝ≥0) ^ M := by
      have hn : (L.powerset.filter (fun K ↦ K.Nonempty)).card ≤ 2 ^ M := by
        apply (card_filter_le _ _).trans
        rw [card_powerset]
        exact pow_le_pow_right₀ (by omega) hLM
      exact_mod_cast hn
    apply (hsub'.trans h).trans
    change _ * C * s ≤ _
    gcongr
    exact hL.trans le_self_add

end

end Erdos207
