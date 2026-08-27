/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LocalizedCommonSourceTail
import ErdosProblems.Erdos207.SelectedCountCover

/-! # Common-threat tails for all pairs of fixed source orders -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem localizedCommonThreatPairs_card_le_sigma_source
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {ell : ℕ}
    (W : Vortex V ell) (F : I → ForbiddenFamilyOn V) (J : ForbiddenFamilyOn V)
    (S : GreedyStateOn V) (T T' : TripleOn V) (available old : TripleSystemOn V)
    (hdis : Disjoint available old) (hterm : ∀ U ∈ available, W.level U = Fin.last ell)
    (hJ : ∀ C ∈ J, C ⊆ available ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old) :
    ((greedyCommonThreatPairs J J S T T').card : ℝ≥0) ≤
      selectedCount (fun u : Σ i : I, Σ i' : I, sourceCommonThreats W (F i) (F i') T T' ↦ u.2.2.1.remainder)
        (old ∪ S.chosen) := by
  classical
  let rem := fun u : Σ i : I, Σ i' : I, sourceCommonThreats W (F i) (F i') T T' ↦ u.2.2.1.remainder
  let decode := fun u : Σ i : I, Σ i' : I, sourceCommonThreats W (F i) (F i') T T' ↦
    (u.2.2.1.first \ old, u.2.2.1.second \ old)
  have hsub : greedyCommonThreatPairs J J S T T' ⊆ selectedWitnessImage rem decode (old ∪ S.chosen) := by
    intro p hp
    let u := greedyCommonThreatPairWitness J J S T T' ⟨p, hp⟩
    obtain ⟨hCA, i, E, hE, hCE, hOld⟩ := hJ u.first u.first_mem
    obtain ⟨hCA', i', E', hE', hCE', hOld'⟩ := hJ u.second u.second_mem
    let v := u.liftLocalized available old E E' hdis hCA hCA' hE hE' hCE hCE' hOld hOld'
    have hv : v ∈ sourceCommonThreats W (F i) (F i') T T' :=
      mem_filter.mpr ⟨mem_univ v, hterm _ (hCA u.bridge_first)⟩
    apply mem_selectedWitnessImage.mpr
    refine ⟨⟨i, i', ⟨v, hv⟩⟩, ?_, ?_⟩
    · exact (u.liftLocalized_remainder_subset available old E E' hdis hCA hCA' hE hE'
        hCE hCE' hOld hOld').trans (union_subset_union_right
          (greedyCommonThreatPairWitness_remainder_subset J J S T T' ⟨p, hp⟩))
    · exact Prod.ext (localization_eq_sdiff_old hdis hCA hCE hOld)
        (localization_eq_sdiff_old hdis hCA' hCE' hOld')
  have hc : ((greedyCommonThreatPairs J J S T T').card : ℝ≥0) ≤
      (selectedWitnessImage rem decode (old ∪ S.chosen)).card := by exact_mod_cast card_le_card hsub
  exact hc.trans (card_selectedWitnessImage_le_selectedCount rem decode (old ∪ S.chosen))

theorem localizedCommon_source_orders_tail_additive
    {Ω V I : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] [Fintype I] {ell q t : ℕ}
    {W : Vortex V ell} {F : I → ForbiddenFamilyOn V} {order : I → ℕ} {y z : I → ℝ≥0}
    (hF : ∀ i, SourceVortexWellSpread W (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (T T' : TripleOn V) (w : ℝ≥0) (hw : 1 ≤ w)
    (L : FiniteLaw Ω) (J : Ω → ForbiddenFamilyOn V) (S : Ω → GreedyStateOn V)
    (available old : Ω → TripleSystemOn V)
    (hstate : L.SupportedOn (fun x ↦ Disjoint (available x) (old x) ∧
      (∀ U ∈ available x, W.level U = Fin.last ell) ∧
      ∀ C ∈ J x, C ⊆ available x ∧ ∃ i E, E ∈ F i ∧ C ⊆ E ∧ E \ C ⊆ old x))
    (A epsilon K : ℝ≥0) (hK : 0 < K)
    (hjoint : ∀ H : TripleSystemOn V, H.card ≤ t * (2 * q) →
      L.probability (fun x ↦ H ⊆ old x ∪ (S x).chosen) ≤
        A * setWeight (vortexTripleWeight W w) H + epsilon) :
    let kappa := ∑ i, ∑ i', sourceCommonMomentCoefficient ell q (order i) w (z i) (z i')
    L.probability (fun x ↦ K ≤ ((greedyCommonThreatPairs (J x) (J x) (S x) T T').card : ℝ≥0)) ≤
      A * (((boundedIntersectionMomentCoefficient (2 * q) t : ℝ≥0) * kappa) / K) ^ t +
      epsilon * (((Fintype.card I : ℝ≥0) ^ 2 * (q + 1 : ℝ≥0) *
        (Fintype.card V + 1 : ℝ≥0) ^ (6 * q)) / K) ^ t := by
  classical
  dsimp only
  let rem := fun u : Σ i : I, Σ i' : I, sourceCommonThreats W (F i) (F i') T T' ↦ u.2.2.1.remainder
  let selected := fun x ↦ old x ∪ (S x).chosen
  let X := fun x ↦ ((greedyCommonThreatPairs (J x) (J x) (S x) T T').card : ℝ≥0)
  have hdom : L.SupportedOn (fun x ↦ X x ≤ selectedCount rem (selected x)) := by
    intro x hx
    have hd := hstate x hx
    exact localizedCommonThreatPairs_card_le_sigma_source W F (J x) (S x) T T'
      (available x) (old x) hd.1 hd.2.1 hd.2.2
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
    (fun i (u : Σ i' : I, sourceCommonThreats W (F i) (F i') T T') ↦ u.2.1.remainder)
    (vortexTripleWeight W w)
    (fun i ↦ ∑ i', sourceCommonMomentCoefficient ell q (order i) w (z i) (z i')) (by
      intro i
      exact hasExtensionBound_sigma_sum
        (fun i' (u : sourceCommonThreats W (F i) (F i') T T') ↦ u.1.remainder)
        (vortexTripleWeight W w) (fun i' ↦ sourceCommonMomentCoefficient ell q (order i) w (z i) (z i'))
        (fun i' ↦ sourceCommon_hasExtensionBound (hF i) (hF i') (horder i) (horder i')
          (hidentical i i') T T' w hw))
  apply (dominatedConfigurationTailBound_additive L rem selected X (vortexTripleWeight W w)
    A epsilon _ K hdom hcard hkappa hK hjoint).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  apply pow_le_pow_left'
  apply div_le_div_of_nonneg_right _ zero_le
  have hcount : Fintype.card (Σ i : I, Σ i' : I, sourceCommonThreats W (F i) (F i') T T') ≤
      (Fintype.card I) ^ 2 * (q + 1) * (Fintype.card V + 1) ^ (6 * q) := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : I, ∑ _i' : I, ((q + 1) * (Fintype.card V + 1) ^ (6 * q)) := by
        apply sum_le_sum
        intro i _hi
        rw [Fintype.card_sigma]
        apply sum_le_sum
        intro i' _hi'
        rw [Fintype.card_coe]
        exact card_sourceCommonThreats_le_polynomial W (F i) (F i') T T'
          (fun E hE ↦ ((hF i).uniform E hE).1) (fun E hE ↦ ((hF i').uniform E hE).1)
          (horder i) (horder i')
      _ = _ := by simp only [sum_const, card_univ, smul_eq_mul]; ring
  exact_mod_cast hcount

end

end Erdos207
