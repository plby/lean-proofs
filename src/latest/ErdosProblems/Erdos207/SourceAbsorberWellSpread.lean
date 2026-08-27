/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceAbsorberPairProfiles

/-! # Source-correct well-spreadness of localized absorber-induced families -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem Vortex.outerProfile_singleton_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (D : TripleOn V) (hD : W.level D = Fin.last ell) :
    W.outerProfile {D} = 0 := by
  funext i
  change ({D} ∩ W.trianglesAtLevel i.castSucc).card = 0
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hmem := mem_inter.mp hS
  have hSD : S = D := mem_singleton.mp hmem.1
  subst S
  have hlevel := (W.mem_trianglesAtLevel_iff i.castSucc D).mp hmem.2
  have hval := congrArg Fin.val hlevel
  simp only [hD, Fin.val_last, Fin.val_castSucc] at hval
  omega

theorem terminalPairExtensions_induced_four_subset_derived_zero
    {V : Type*} [Fintype V] [DecidableEq V] {ell q : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (T : TripleOn V) (P : VortexPairOn V) :
    W.terminalPairExtensions (absorberInducedConfigurationsOn q 4 B) T P ⊆
      W.profiledExtensions (derivedAbsorberConfigurations q 4 B) {T} 0 := by
  intro E hE
  obtain ⟨hEF, hT, D, hD, hDlevel, _hP⟩ := (W.mem_terminalPairExtensions_iff _ _ _ _).mp hE
  have hcard : E.card = 2 := by simpa using (absorberInduced_uniform E hEF).1
  have herasecard : (E.erase T).card = 1 := by rw [card_erase_of_mem hT, hcard]
  have herase : E.erase T = {D} := by
    symm
    apply eq_of_subset_of_card_le (singleton_subset_iff.mpr hD)
    simp only [herasecard, card_singleton, le_refl]
  have hderived : E ∈ derivedAbsorberConfigurations q 4 B := by
    by_contra hnot
    have h := genuine_of_induced_not_derived (by omega : 3 ≤ 4) hEF hnot
    omega
  apply (W.mem_profiledExtensions_iff _ _ _ _).mpr
  refine ⟨hderived, singleton_subset_iff.mpr hT, ?_⟩
  rw [sdiff_singleton_eq_erase, herase]
  exact W.outerProfile_singleton_terminal D hDlevel

theorem card_terminalPairExtensions_absorber_source_le_localized
    {V : Type*} [Fintype V] [DecidableEq V] {m q M : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (T : TripleOn V) (P : VortexPairOn V) (z : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1) (hq : 4 ≤ q)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbank : ((subsetsUpToCard B q).card : ℝ≥0) * W.terminalSize ≤ (W.U 0).card * z) :
    ((W.terminalPairExtensions (absorberInducedConfigurationsOn q 4 B) T P).card : ℝ≥0) ≤
      ((2 : ℝ≥0) ^ M + z) * exactBankVortexOrderCoefficient q (m + 1) := by
  have hsub : ((W.terminalPairExtensions (absorberInducedConfigurationsOn q 4 B) T P).card : ℝ≥0) ≤
      (W.profiledExtensions (derivedAbsorberConfigurations q 4 B) {T} 0).card := by
    exact_mod_cast card_le_card (terminalPairExtensions_induced_four_subset_derived_zero W B T P)
  have h := card_profiledExtensions_derived_singleton_source_le_localized W H X B T 0 z
    hA2 hsep (by omega : 4 ≤ 4) hq hterminal hroot hbank
  simpa [Vortex.sourceProfileScale, Vortex.profileScale, VortexProfile.mass] using hsub.trans h

theorem absorberInduced_sourceVortexWellSpread_localized
    {V : Type*} [Fintype V] [DecidableEq V] {m q M j : ℕ}
    (W : Vortex V (m + 1)) (H : SimpleGraph V) (X : Finset V)
    (B : TripleSystemOn V) (z : ℝ≥0)
    (hA2 : HasAbsorberLocalization q M H X B)
    (hsep : ∀ x ∈ graphSupportFinset H, x ∉ X → x ∉ W.U 1)
    (hj : 4 ≤ j) (hjq : j ≤ q)
    (hterminal : 0 < W.terminalSize) (hroot : 0 < (W.U 0).card)
    (hbankRoot : (subsetsUpToCard B q).card ≤ (W.U 0).card)
    (hbank : ((subsetsUpToCard B q).card : ℝ≥0) * W.terminalSize ≤ (W.U 0).card * z) :
    SourceVortexWellSpread W j (absorberInducedConfigurationsOn q j B)
      (((2 : ℝ≥0) ^ M + 1) * exactBankVortexOrderCoefficient q (m + 1))
      (2 * (((2 : ℝ≥0) ^ M + z) * exactBankVortexOrderCoefficient q (m + 1)) +
        exactBankVortexCoefficient j (m + 1)) := by
  let a : ℝ≥0 := ((2 : ℝ≥0) ^ M + z) * exactBankVortexOrderCoefficient q (m + 1)
  have ha : a ≤ 2 * a + exactBankVortexCoefficient j (m + 1) := by
    calc
      a ≤ a + a := le_self_add
      _ = 2 * a := by ring
      _ ≤ _ := le_self_add
  refine ⟨hj, hterminal, absorberInduced_uniform, ?_, ?_, ?_, ?_⟩
  · intro R t hR hRcard
    exact (card_profiledExtensions_absorberInduced_source_le_localized W H X B R t z
      hA2 hsep hj hjq hR hRcard hterminal hroot hbank).trans
        (mul_le_mul_of_nonneg_right ha zero_le)
  · intro T T' t
    exact card_profiledDistinctPairs_absorber_source_le_localized W H X B T T' t z
      hA2 hsep hj hjq hterminal hroot hbank
  · intro hj4 T P _hP
    subst j
    exact (card_terminalPairExtensions_absorber_source_le_localized W H X B T P z
      hA2 hsep hjq hterminal hroot hbank).trans ha
  · intro T t
    exact card_profiledExtensions_absorberInduced_singleton_source_le_sharp W H X B T t
      hA2 hsep hj hjq hterminal hroot hbankRoot

end

end Erdos207
