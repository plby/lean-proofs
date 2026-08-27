/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedGainSourceTail
import ErdosProblems.Erdos207.SelectedCountCover

/-! # The fourth generalized crude tail over all fixed source-order pairs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedGainDefectCount_le_sigma_source
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell c m : ℕ}
    (W : Vortex V ell) (F : I → ForbiddenFamilyOn V) (J J' processF : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T : TripleOn V) (available old : TripleSystemOn V)
    (hS : GreedyInvariant processF S) (huniform : ∀ C ∈ J, C.card = m)
    (hdis : Disjoint available old) (hterm : ∀ U ∈ available, W.level U = Fin.last ell)
    (hJ : ∀ C ∈ J, C ⊆ available ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old)
    (hJ' : ∀ C ∈ J', C ⊆ available ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old) :
    (greedyActiveGainDefectCount J J' S T c : ℝ≥0) ≤
      selectedCount (fun u : Σ i : I, Σ i' : I, sourceGainDefects W (F i) (F i') T (m - c - 1) ↦ u.2.2.1.remainder)
        (old ∪ S.chosen) := by
  classical
  by_cases hT : T ∈ S.available
  · simp only [greedyActiveGainDefectCount, if_pos hT]
    let rem := fun u : Σ i : I, Σ i' : I, sourceGainDefects W (F i) (F i') T (m - c - 1) ↦ u.2.2.1.remainder
    let decode := fun u : Σ i : I, Σ i' : I, sourceGainDefects W (F i) (F i') T (m - c - 1) ↦
      (u.2.2.1.first \ old, u.2.2.1.second \ old)
    have hsub : greedyGainDefectPairs J J' S T c ⊆ selectedWitnessImage rem decode (old ∪ S.chosen) := by
      intro p hp
      let u := greedyGainDefectPairWitness J J' S T c m hS hT huniform ⟨p, hp⟩
      obtain ⟨hCA, i, E, hE, hCE, hOld⟩ := hJ u.first u.first_mem
      obtain ⟨hCA', i', E', hE', hCE', hOld'⟩ := hJ' u.second u.second_mem
      let v := u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld'
      have hv : v ∈ sourceGainDefects W (F i) (F i') T (m - c - 1) :=
        mem_filter.mpr ⟨mem_univ v, fun U hU ↦ hterm U (hCA (u.omittedRoot_subset_first hU))⟩
      apply mem_selectedWitnessImage.mpr
      refine ⟨⟨i, i', ⟨v, hv⟩⟩, ?_, ?_⟩
      · exact (u.liftLocalized_remainder_subset available old E E' hdis hCA hCA' hE hE'
          hCE hCE' hOld hOld').trans (union_subset_union_right
            (greedyGainDefectPairWitness_remainder_subset J J' S T c m hS hT huniform ⟨p, hp⟩))
      · exact Prod.ext (localization_eq_sdiff_old hdis hCA hCE hOld)
          (localization_eq_sdiff_old hdis hCA' hCE' hOld')
    have hc : ((greedyGainDefectPairs J J' S T c).card : ℝ≥0) ≤
        (selectedWitnessImage rem decode (old ∪ S.chosen)).card := by exact_mod_cast card_le_card hsub
    exact hc.trans (card_selectedWitnessImage_le_selectedCount rem decode (old ∪ S.chosen))
  · simp only [greedyActiveGainDefectCount, if_neg hT, Nat.cast_zero, zero_le]

theorem localizedGain_source_orders_tail_additive
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype I] {ell q c m t : ℕ}
    {W : Vortex V ell} {F : I → ForbiddenFamilyOn V} {order : I → ℕ} {y z : I → ℝ≥0}
    (hF : ∀ i, SourceVortexWellSpread W (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (ha : 1 ≤ m - c - 1) (T : TripleOn V) (w : ℝ≥0) (hw : 1 ≤ w)
    (L : FiniteLaw Ω) (J J' processF : Ω → ForbiddenFamilyOn V) (S : Ω → GreedyStateOn V)
    (available old : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦ GreedyInvariant (processF x) (S x) ∧
      (∀ C ∈ J x, C.card = m) ∧ Disjoint (available x) (old x) ∧
      (∀ U ∈ available x, W.level U = Fin.last ell) ∧
      (∀ C ∈ J x, C ⊆ available x ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old x) ∧
      (∀ C ∈ J' x, C ⊆ available x ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old x)))
    (A epsilon K : ℝ≥0) (hK : 0 < K)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ t * (2 * q) →
      L.probability (fun x ↦ H ⊆ old x ∪ (S x).chosen) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    let kappa := ∑ i, ∑ i', sourceGainMomentCoefficient ell q (order i) w (z i) (z i') *
      (W.terminalSize : ℝ≥0) ^ (m - c - 2)
    L.probability (fun x ↦ K ≤ (greedyActiveGainDefectCount (J x) (J' x) (S x) T c : ℝ≥0)) ≤
      A * (((boundedIntersectionMomentCoefficient (2 * q) t : ℝ≥0) * kappa) / K) ^ t +
      epsilon * (((Fintype.card I : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ q *
        (Fintype.card V + 1 : ℝ≥0) ^ (6 * q)) / K) ^ t := by
  classical
  dsimp only
  let rem := fun u : Σ i : I, Σ i' : I, sourceGainDefects W (F i) (F i') T (m - c - 1) ↦ u.2.2.1.remainder
  let selected := fun x ↦ old x ∪ (S x).chosen
  let X := fun x ↦ (greedyActiveGainDefectCount (J x) (J' x) (S x) T c : ℝ≥0)
  have hdom : L.SupportedOn (fun x ↦ X x ≤ selectedCount rem (selected x)) := by
    intro x hx
    have hd := hstate x hx
    exact localizedGainDefectCount_le_sigma_source W F (J x) (J' x) (processF x) (S x) T
      (available x) (old x) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2.1 hd.2.2.2.2.2
  have hcard : ∀ u, (rem u).card ≤ 2 * q := by
    intro u
    have hc := u.2.2.1.remainder_card
    have hf := ((hF u.1).uniform u.2.2.1.first u.2.2.1.first_mem).1
    have hg := ((hF u.2.1).uniform u.2.2.1.second u.2.2.1.second_mem).1
    have hr := horder u.1
    have hs := horder u.2.1
    dsimp only [rem]
    omega
  have hkappa := hasExtensionBound_sigma_sum
    (fun i (u : Σ i' : I, sourceGainDefects W (F i) (F i') T (m - c - 1)) ↦ u.2.1.remainder)
    (vortexTripleWeight W w)
    (fun i ↦ ∑ i', sourceGainMomentCoefficient ell q (order i) w (z i) (z i') *
      (W.terminalSize : ℝ≥0) ^ (m - c - 2)) (by
      intro i
      apply hasExtensionBound_sigma_sum
        (fun i' (u : sourceGainDefects W (F i) (F i') T (m - c - 1)) ↦ u.1.remainder)
        (vortexTripleWeight W w)
        (fun i' ↦ sourceGainMomentCoefficient ell q (order i) w (z i) (z i') *
          (W.terminalSize : ℝ≥0) ^ (m - c - 2))
      intro i'
      have hb := sourceGain_hasExtensionBound (hF i) (hF i') (horder i) (horder i')
        (hidentical i i') ha T w hw
      simpa only [show m - c - 1 - 1 = m - c - 2 by omega] using hb)
  apply (dominatedConfigurationTailBound_additive L rem selected X (vortexTripleWeight W w)
    A epsilon _ K hdom hcard hkappa hK hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  have hcount : Fintype.card (Σ i : I, Σ i' : I, sourceGainDefects W (F i) (F i') T (m - c - 1)) ≤
      (Fintype.card I) ^ 2 * 2 ^ q * (Fintype.card V + 1) ^ (6 * q) := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : I, ∑ _i' : I, (2 ^ q * (Fintype.card V + 1) ^ (6 * q)) := by
        apply sum_le_sum
        intro i _hi
        rw [Fintype.card_sigma]
        apply sum_le_sum
        intro i' _hi'
        rw [Fintype.card_coe]
        exact card_sourceGainDefects_le_polynomial W (F i) (F i') T (m - c - 1)
          (fun E hE ↦ ((hF i).uniform E hE).1) (fun E hE ↦ ((hF i').uniform E hE).1)
          (horder i) (horder i')
      _ = _ := by simp only [sum_const, card_univ, smul_eq_mul]; ring
  exact_mod_cast hcount

end

end Erdos207
