/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceBankProfiledCover

/-! # Source-profile extension estimates from absorber localization -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem profiledExtensions_absorberInduced_subset_bankProfiledCover
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V) (t : VortexProfile ell) :
    W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t ⊆
      bankProfiledCover W q j B R (subsetsUpToCard B q) t := by
  have heq : B.powerset.filter (fun K ↦ K.card ≤ q) = subsetsUpToCard B q := by
    ext K
    simp only [mem_filter, mem_powerset, mem_subsetsUpToCard_iff]
  simpa only [profiledExactBankCover, bankProfiledCover, heq] using
    profiledExtensions_absorberInduced_subset_exactBankCover (q := q) (j := j) W B R t

theorem card_profiledExtensions_absorberInduced_source_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B R : TripleSystemOn V) (t : VortexProfile ell)
    (hj : 3 ≤ j) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hterminal : 0 < W.terminalSize) :
    ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card : ℝ≥0) ≤
      (subsetsUpToCard B q).card * (exactBankVortexOrderCoefficient q ell : ℝ≥0) *
        W.sourceProfileScale (j - vortexRootExponent j R.card) t := by
  have hsub : ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card : ℝ≥0) ≤
      (bankProfiledCover W q j B R (subsetsUpToCard B q) t).card := by
    exact_mod_cast card_le_card (profiledExtensions_absorberInduced_subset_bankProfiledCover W B R t)
  exact hsub.trans (card_bankProfiledCover_source_le W B R _ t hj hR hRcard hterminal)

theorem card_profiledExtensions_absorberInduced_source_le_localized
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B R : TripleSystemOn V) (t : VortexProfile (m + 1)) (z : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hj : 4 ≤ j) (hjq : j ≤ q) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbank : ((subsetsUpToCard B q).card : ℝ≥0) * W.terminalSize ≤ (W.U 0).card * z) :
    ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card : ℝ≥0) ≤
      ((2 : ℝ≥0) ^ M + z) * exactBankVortexOrderCoefficient q (m + 1) *
        W.sourceProfileScale (j - vortexRootExponent j R.card) t := by
  obtain ⟨L, _hLB, hLM, hcover, hzero⟩ :=
    profiledExtensions_absorberInduced_subset_sharpCover (j := j) W H X B R t
      hA2 (hRcard.trans (by omega)) hsep
  let C : ℝ≥0 := exactBankVortexOrderCoefficient q (m + 1)
  let s := W.sourceProfileScale (j - vortexRootExponent j R.card) t
  have hlocal : ((localBankProfiledCover W q j B R L t).card : ℝ≥0) ≤ (2 : ℝ≥0) ^ M * C * s := by
    have h := card_bankProfiledCover_source_le (q := q) W B R L.powerset t (by omega) hR hRcard hterminal
    have hLpow : (L.powerset.card : ℝ≥0) ≤ (2 : ℝ≥0) ^ M := by
      have hnat : L.powerset.card ≤ 2 ^ M := by
        rw [card_powerset]
        exact pow_le_pow_right₀ (by omega) hLM
      exact_mod_cast hnat
    exact h.trans (by change (L.powerset.card : ℝ≥0) * C * s ≤ _; gcongr)
  rcases hzero with ht0 | hlocalOnly
  · let banks := (subsetsUpToCard B q).filter (fun K ↦ K.Nonempty)
    have hbanks : (banks.card : ℝ≥0) ≤ (subsetsUpToCard B q).card := by
      exact_mod_cast card_le_card (filter_subset (s := subsetsUpToCard B q) (p := fun K ↦ K.Nonempty))
    have hstrict := card_bankProfiledCover_mul_root_source_le (q := q) W B R banks t hj hR hRcard
      (fun K hK ↦ (mem_filter.mp hK).2) ht0 hterminal
    have hNpos : (0 : ℝ≥0) < (W.U 0).card := by exact_mod_cast hroot
    have hnonlocal : ((nonemptyBankProfiledCover W q j B R t).card : ℝ≥0) ≤ z * C * s := by
      apply (mul_le_mul_iff_right₀ hNpos).mp
      calc
        _ ≤ banks.card * C * (W.terminalSize * s) := hstrict
        _ = ((banks.card : ℝ≥0) * W.terminalSize) * C * s := by ring
        _ ≤ ((W.U 0).card * z) * C * s := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_right hbanks zero_le).trans hbank) zero_le) zero_le
        _ = _ := by ring
    have htotal : ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card : ℝ≥0) ≤
        (localBankProfiledCover W q j B R L t).card + (nonemptyBankProfiledCover W q j B R t).card := by
      exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
    calc
      _ ≤ ((localBankProfiledCover W q j B R L t).card : ℝ≥0) + (nonemptyBankProfiledCover W q j B R t).card := htotal
      _ ≤ (2 : ℝ≥0) ^ M * C * s + z * C * s := add_le_add hlocal hnonlocal
      _ = _ := by dsimp only [C, s]; ring
  · have hsub : ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) R t).card : ℝ≥0) ≤
        (localBankProfiledCover W q j B R L t).card := by exact_mod_cast card_le_card hlocalOnly
    calc
      _ ≤ (2 : ℝ≥0) ^ M * C * s := hsub.trans hlocal
      _ ≤ ((2 : ℝ≥0) ^ M + z) * C * s := by gcongr; exact le_self_add

theorem card_profiledExtensions_absorberInduced_singleton_source_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (T : TripleOn V) (t : VortexProfile (m + 1))
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hj : 4 ≤ j) (hjq : j ≤ q)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbank : (subsetsUpToCard B q).card ≤ (W.U 0).card) :
    ((W.profiledExtensions (absorberInducedConfigurationsOn q j B) {T} t).card : ℝ≥0) ≤
      (((2 : ℝ≥0) ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1)) * W.sourceProfileScale (j - 3) t := by
  by_cases hF : (W.profiledExtensions (absorberInducedConfigurationsOn q j B) {T} t).Nonempty
  · obtain ⟨S, hS⟩ := hF
    have hm := (W.mem_profiledExtensions_iff _ _ _ _).mp hS
    have hScard := (mem_absorberInducedConfigurationsOn_iff.mp hm.1).1
    have hmass : t.mass ≤ j - 3 := by
      rw [← hm.2.2]
      have h := W.outerProfile_mass_le_card (S \ {T})
      rw [card_sdiff_of_subset hm.2.1, card_singleton, hScard] at h
      omega
    rw [W.sourceProfileScale_of_mass_le t hterminal hmass]
    have h := card_profiledExtensions_absorberInduced_singleton_le_sharp
      W H X B T t hA2 hsep hj hjq hterminal hroot hbank
    have he : j - 3 - t.mass = j - t.mass - 3 := by omega
    rw [he]
    simp only [← mul_assoc]
    exact_mod_cast h
  · simp only [not_nonempty_iff_eq_empty.mp hF, card_empty, Nat.cast_zero, zero_le]

end

end Erdos207
