/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceAbsorberWellSpread

/-! # The source well-spread bound for large terminals, including length zero -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem Vortex.sourceProfileScale_succ
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (d : ℕ) (t : VortexProfile ell) :
    W.sourceProfileScale (d + 1) t = W.terminalSize * W.sourceProfileScale d t := by
  unfold sourceProfileScale
  rw [pow_succ]
  ring

theorem profiledExtensions_absorber_subset_empty_bank_union_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V) (t : VortexProfile ell) :
    W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t ⊆
      bankProfiledCover W q j B R {∅} t ∪
      bankProfiledCover W q j B R ((subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)) t := by
  intro S hS
  have hcover := profiledExtensions_absorberInduced_subset_bankProfiledCover W B R t hS
  obtain ⟨rho, hrho, hS⟩ := mem_biUnion.mp hcover
  obtain ⟨K, hK, hSK⟩ := mem_biUnion.mp hS
  by_cases hK0 : K = ∅
  · subst K
    exact mem_union_left _ (mem_biUnion.mpr
      ⟨rho, hrho, mem_biUnion.mpr ⟨∅, mem_singleton_self _, hSK⟩⟩)
  · exact mem_union_right _ (mem_biUnion.mpr
      ⟨rho, hrho, mem_biUnion.mpr ⟨K, mem_filter.mpr ⟨hK, nonempty_iff_ne_empty.mpr hK0⟩, hSK⟩⟩)

theorem card_profiledExtensions_absorber_singleton_source_le_global
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (T : TripleOn V) (t : VortexProfile ell)
    (hj : 4 ≤ j) (hterminal : 0 < W.terminalSize)
    (hbank : (subsetsUpToCard B q).card ≤ W.terminalSize) :
    ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) {T} t).card : ℝ≥0) ≤
      (2 * exactBankVortexOrderCoefficient q ell : ℝ≥0) * W.sourceProfileScale (j - 3) t := by
  let C : ℝ≥0 := exactBankVortexOrderCoefficient q ell
  let s := W.sourceProfileScale (j - 3) t
  let banks := (subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)
  have hleft : ((bankProfiledCover W q j B {T} {∅} t).card : ℝ≥0) ≤ C * s := by
    have h := card_bankProfiledCover_source_le (q := q) (j := j) W B {T} {∅} t
      (by omega) (by simp) (by simp; omega) hterminal
    simpa only [card_singleton, Nat.cast_one, one_mul, vortexRootExponent_one] using h
  have hright : ((bankProfiledCover W q j B {T} banks t).card : ℝ≥0) ≤ C * s := by
    have h := card_bankProfiledCover_singleton_source_le (q := q) W B {T} banks t hj
      (by simp) (fun K hK ↦ (mem_filter.mp hK).2) hterminal
    have hbanks : (banks.card : ℝ≥0) ≤ W.terminalSize := by
      exact_mod_cast (card_filter_le _ _).trans hbank
    have he : W.sourceProfileScale (j - 3) t = W.terminalSize * W.sourceProfileScale (j - 4) t := by
      rw [show j - 3 = j - 4 + 1 by omega, W.sourceProfileScale_succ]
    calc
      _ ≤ banks.card * C * W.sourceProfileScale (j - 4) t := h
      _ ≤ W.terminalSize * C * W.sourceProfileScale (j - 4) t := by gcongr
      _ = C * s := by dsimp only [s]; rw [he]; ring
  have hsub : ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) {T} t).card : ℝ≥0) ≤
      (bankProfiledCover W q j B {T} {∅} t).card + (bankProfiledCover W q j B {T} banks t).card := by
    exact_mod_cast (card_le_card (profiledExtensions_absorber_subset_empty_bank_union_nonempty W B {T} t)).trans
      (card_union_le _ _)
  exact hsub.trans ((add_le_add hleft hright).trans_eq (by dsimp only [C, s]; ring))

theorem card_terminalPairExtensions_absorber_source_le_global
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (T : TripleOn V) (P : VortexPairOn V)
    (hterminal : 0 < W.terminalSize) :
    ((W.terminalPairExtensions (absorberInducedConfigurationsOn q 4 B) T P).card : ℝ≥0) ≤
      (subsetsUpToCard B q).card * (exactBankVortexOrderCoefficient q ell : ℝ≥0) := by
  have hsub : ((W.terminalPairExtensions (absorberInducedConfigurationsOn q 4 B) T P).card : ℝ≥0) ≤
      (W.profiledExtensions (derivedAbsorberConfigurations q 4 B) {T} 0).card := by
    exact_mod_cast card_le_card (terminalPairExtensions_induced_four_subset_derived_zero W B T P)
  have h := card_profiledExtensions_derived_singleton_source_le (q := q) W B T 0 (by omega : 4 ≤ 4) hterminal
  simpa [Vortex.sourceProfileScale, Vortex.profileScale, VortexProfile.mass] using hsub.trans h

theorem absorberInduced_sourceVortexWellSpread_global
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (hj : 4 ≤ j)
    (hterminal : 0 < W.terminalSize) (hbank : (subsetsUpToCard B q).card ≤ W.terminalSize) :
    SourceVortexWellSpread W j (absorberInducedConfigurationsOn q j B)
      (2 * exactBankVortexOrderCoefficient q ell)
      (2 * ((subsetsUpToCard B q).card * (exactBankVortexOrderCoefficient q ell : ℝ≥0)) +
        exactBankVortexCoefficient j ell) := by
  let a : ℝ≥0 := (subsetsUpToCard B q).card * (exactBankVortexOrderCoefficient q ell : ℝ≥0)
  have ha : a ≤ 2 * a + exactBankVortexCoefficient j ell := by
    calc
      a ≤ a + a := le_self_add
      _ = 2 * a := by ring
      _ ≤ _ := le_self_add
  refine ⟨hj, hterminal, absorberInduced_uniform, ?_, ?_, ?_, ?_⟩
  · intro R t hR hRcard
    exact (card_profiledExtensions_absorberInduced_source_le W B R t (by omega) hR hRcard hterminal).trans
      (mul_le_mul_of_nonneg_right ha zero_le)
  · intro T T' t
    exact card_profiledDistinctPairs_absorber_source_le W B T T' t hj hterminal
  · intro hj4 T P _hP
    subst j
    exact (card_terminalPairExtensions_absorber_source_le_global W B T P hterminal).trans ha
  · intro T t
    exact card_profiledExtensions_absorber_singleton_source_le_global W B T t hj hterminal hbank

end

end Erdos207
