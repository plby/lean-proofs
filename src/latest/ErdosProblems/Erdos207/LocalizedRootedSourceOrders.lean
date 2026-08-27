/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedRootedSourceTail
import ErdosProblems.Erdos207.SelectedCountCover

/-! # Rooted crude-statistic tails for all localized fixed source orders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedRooted_card_le_sigma_source
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell j c : ℕ}
    (W : Vortex V ell) (F : I → ForbiddenFamilyOn V) (order : I → ℕ)
    (J processF : ForbiddenFamilyOn V) (S : GreedyStateOn V)
    (Q available old : TripleSystemOn V) (hj : 2 ≤ j) (horder : ∀ i, j ≤ order i)
    (huniform : ∀ i E, E ∈ F i → E.card = order i - 2)
    (hS : GreedyInvariant processF S) (hterminal : ∀ T ∈ S.available, W.level T = Fin.last ell)
    (hdis : Disjoint available old)
    (hJ : ∀ C ∈ J, C.card = j - 2 ∧ C ⊆ available ∧
      ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old) :
    ((greedyRootedConfigurationClass J S Q c).card : ℝ≥0) ≤
      selectedCount (fun u : Σ i, terminalOmissionCodes W (familyExtensions (F i) Q)
        (fun E ↦ E \ Q) (order i - j + c) ↦ u.2.1.2) (old ∪ S.chosen) := by
  classical
  let rem := fun u : Σ i, terminalOmissionCodes W (familyExtensions (F i) Q)
    (fun E ↦ E \ Q) (order i - j + c) ↦ u.2.1.2
  let decode := fun u : Σ i, terminalOmissionCodes W (familyExtensions (F i) Q)
    (fun E ↦ E \ Q) (order i - j + c) ↦ u.2.1.1 \ old
  have hsub : greedyRootedConfigurationClass J S Q c ⊆ selectedWitnessImage rem decode (old ∪ S.chosen) := by
    intro C hC
    obtain ⟨hCcard, hCA, i, E, hE, hCE, hOld⟩ := hJ C (mem_filter.mp hC).1
    have hcode := localizedRooted_source_omission_code W (F i) J processF S Q C E hj (horder i)
      hS hterminal hC hCcard hE (huniform i E hE) hCE
    apply mem_selectedWitnessImage.mpr
    exact ⟨⟨i, ⟨(E, (E \ C) ∪ (C ∩ S.chosen)), hcode⟩⟩,
      union_subset_union hOld inter_subset_right, localization_eq_sdiff_old hdis hCA hCE hOld⟩
  have hcard : ((greedyRootedConfigurationClass J S Q c).card : ℝ≥0) ≤
      (selectedWitnessImage rem decode (old ∪ S.chosen)).card := by exact_mod_cast card_le_card hsub
  exact hcard.trans (card_selectedWitnessImage_le_selectedCount rem decode (old ∪ S.chosen))

theorem localizedRooted_source_orders_tail_additive
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype I] {ell q j c s : ℕ}
    {W : Vortex V ell} {F : I → ForbiddenFamilyOn V} {order : I → ℕ} {y z : I → ℝ≥0}
    (hF : ∀ i, SourceVortexWellSpread W (order i) (F i) (y i) (z i))
    (horder : ∀ i, j ≤ order i ∧ order i ≤ q) (Q : TripleSystemOn V) (hQ : Q.card = 2)
    (hc : c + 5 ≤ j) (w : ℝ≥0) (hw : 1 ≤ w)
    (L : FiniteLaw Ω) (J processF : Ω → ForbiddenFamilyOn V) (S : Ω → GreedyStateOn V)
    (available old : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦ GreedyInvariant (processF x) (S x) ∧
      (∀ T ∈ (S x).available, W.level T = Fin.last ell) ∧ Disjoint (available x) (old x) ∧
      ∀ C ∈ J x, C.card = j - 2 ∧ C ⊆ available x ∧
        ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old x))
    (A epsilon K : ℝ≥0) (hK : 0 < K)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ s * (q - j + c) →
      L.probability (fun x ↦ H ⊆ old x ∪ (S x).chosen) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    let kappa := ∑ i, ((((order i - j + c + 1) ^ ell : ℕ) : ℝ≥0) *
      ((2 : ℝ≥0) ^ (order i - 2) * z i) * w ^ (order i - j + c) *
      (W.terminalSize : ℝ≥0) ^ (j - c - 5))
    let countBound := ∑ i, (2 : ℝ≥0) ^ order i * (Fintype.card V + 1 : ℝ≥0) ^ (3 * order i)
    L.probability (fun x ↦ K ≤ ((greedyRootedConfigurationClass (J x) (S x) Q c).card : ℝ≥0)) ≤
      A * (((boundedIntersectionMomentCoefficient (q - j + c) s : ℝ≥0) * kappa) / K) ^ s +
        epsilon * (countBound / K) ^ s := by
  classical
  dsimp only
  let rem := fun u : Σ i, terminalOmissionCodes W (familyExtensions (F i) Q)
    (fun E ↦ E \ Q) (order i - j + c) ↦ u.2.1.2
  let selected := fun x ↦ old x ∪ (S x).chosen
  let X := fun x ↦ ((greedyRootedConfigurationClass (J x) (S x) Q c).card : ℝ≥0)
  have hdom : L.SupportedOn (fun x ↦ X x ≤ selectedCount rem (selected x)) := by
    intro x hx
    have hs := hstate x hx
    exact localizedRooted_card_le_sigma_source W F order (J x) (processF x) (S x) Q
      (available x) (old x) (by omega) (fun i ↦ (horder i).1)
      (fun i E hE ↦ ((hF i).uniform E hE).1) hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have hcard : ∀ u, (rem u).card ≤ q - j + c := by
    intro u
    have hc' := (mem_terminalRemainderChoices_iff.mp (mem_terminalOmissionCodes_iff.mp u.2.2).2).2.1
    have ho := horder u.1
    dsimp only [rem]
    omega
  have hkappa := hasExtensionBound_sigma_sum
    (fun i (u : terminalOmissionCodes W (familyExtensions (F i) Q) (fun E ↦ E \ Q) (order i - j + c)) ↦ u.1.2)
    (vortexTripleWeight W w)
    (fun i ↦ ((((order i - j + c + 1) ^ ell : ℕ) : ℝ≥0) *
      ((2 : ℝ≥0) ^ (order i - 2) * z i) * w ^ (order i - j + c) *
      (W.terminalSize : ℝ≥0) ^ (j - c - 5))) (by
      intro i
      have ho := (horder i).1
      have hfit : Q.card + (order i - j + c) + 3 ≤ order i := by rw [hQ]; omega
      have hexp : order i - Q.card - 3 - (order i - j + c) = j - c - 5 := by rw [hQ]; omega
      have hbound := (hF i).root_omission_hasExtensionBound Q (by omega) hfit w hw
      simpa only [hexp] using hbound)
  apply (dominatedConfigurationTailBound_additive L rem selected X (vortexTripleWeight W w)
    A epsilon _ K hdom hcard hkappa hK hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  rw [Fintype.card_sigma, Nat.cast_sum]
  apply sum_le_sum
  intro i _hi
  rw [Fintype.card_coe]
  exact_mod_cast card_sourceRootOmissionCodes_le_polynomial W (F i) Q (order i) (order i - j + c)
    (fun E hE ↦ ((hF i).uniform E hE).1)

end

end Erdos207
