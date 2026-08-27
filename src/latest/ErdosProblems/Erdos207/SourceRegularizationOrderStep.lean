/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationSuccess
import ErdosProblems.Erdos207.RegularizationForbiddenDegree
import ErdosProblems.Erdos207.RegularizationGoodCounts

/-! # The finite source-correct forbidden-order regularization step -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem original_contains_earlier_or_trim
    {I : Type*} [DecidableEq I] (L earlier : Finset (Finset I)) :
    ∀ E ∈ L, ∃ C ∈ earlier ∪ trimForbiddenSupersets L earlier, C ⊆ E := by
  classical
  intro E hE
  by_cases hex : ∃ C ∈ earlier, C ⊆ E
  · obtain ⟨C, hC, hCE⟩ := hex
    exact ⟨C, mem_union_left _ hC, hCE⟩
  · refine ⟨E, mem_union_right _ ((mem_trimForbiddenSupersets_iff L earlier E).mpr ⟨hE, ?_⟩), Subset.rfl⟩
    intro C hC hCE
    exact hex ⟨C, hC, hCE⟩

theorem exists_source_regularization_order_step_with_counts
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [Nonempty I] {ell j s : ℕ}
    {W : Vortex V ell} {delta a : ℝ≥0}
    (P : SourceRandomConfigurationParameters W j delta a s)
    (L earlier : Finset (Finset I)) (hL : ∀ E ∈ L, E.card = j - 2)
    (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell))
    (hsize : 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card I)
    (b : ℕ) (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    let G := trimForbiddenSupersets L earlier
    let H := regularizationForbiddenFamily e (j - 2) G earlier
    (2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree H ≤
        (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (j - 2 - 1) →
    2 * regularizationBaseHazard G (j - 2) ≤ sourceRandomConfigurationProbability W.terminalSize delta j →
    finiteHypergraphDegreeGap G * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
        (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1 →
    ∃ Lstar : Finset (Finset I), ∃ Fsup : ForbiddenFamilyOn V,
      (∀ E ∈ Lstar, E.card = j - 2) ∧
      finiteHypergraphMaxDegree Lstar ≤ 9 * finiteHypergraphMaxDegree L ∧
      finiteHypergraphDegreeGap Lstar ≤ b ∧
      (∀ E ∈ Lstar, ∀ C ∈ earlier, ¬ C ⊆ E) ∧
      (∀ E ∈ L, ∃ C ∈ earlier ∪ Lstar, C ⊆ E) ∧
      F ⊆ Fsup ∧ (Lstar \ L).image (Finset.map e) ⊆ Fsup ∧
      SourceVortexWellSpread W j Fsup (y + a) (z + 3 * a) ∧
      (∀ E ∈ Fsup \ F, E ⊆ Finset.univ.map e) ∧
      SourceAugmentationCounts j W.terminalSize F (Fsup \ F) a := by
  classical
  dsimp only
  intro hdensity hprob hsmall
  let G := trimForbiddenSupersets L earlier
  let H := regularizationForbiddenFamily e (j - 2) G earlier
  have hk : 2 ≤ j - 2 := by have := P.order; omega
  have hGH : G ⊆ H := subset_regularizationForbiddenFamily e (j - 2) G earlier
  obtain ⟨R, havoid, hRcard, _hcandidates, hmax, hgap, hspread, hcounts⟩ :=
    exists_source_regularizing_augmentation_with_counts P G H hGH hk hsize hdensity b e
      (regularizationForbiddenFamily_contains_nonCandidates W e hsupport G earlier)
      hprob F y z hF hdeltaY hsmall
  refine ⟨G ∪ R, F ∪ R.image (Finset.map e), ?_, ?_, hgap, ?_, ?_, subset_union_left, ?_, hspread, ?_, ?_⟩
  · intro E hE
    rcases mem_union.mp hE with hold | hnew
    · exact hL E (trimForbiddenSupersets_subset L earlier hold)
    · exact hRcard E hnew
  · exact hmax.trans (Nat.mul_le_mul_left 9 (finiteHypergraphMaxDegree_mono (trimForbiddenSupersets_subset L earlier)))
  · exact regularizedFamily_no_earlier_subset e (j - 2) L earlier R hRcard havoid
  · intro E hE
    obtain ⟨C, hC, hCE⟩ := original_contains_earlier_or_trim L earlier E hE
    refine ⟨C, ?_, hCE⟩
    exact (union_subset_union_right (subset_union_left : G ⊆ G ∪ R)) hC
  · intro C hC
    obtain ⟨E, hE, rfl⟩ := mem_image.mp hC
    have hm := mem_sdiff.mp hE
    have hER : E ∈ R := by
      rcases mem_union.mp hm.1 with hold | hnew
      · exact (hm.2 (trimForbiddenSupersets_subset L earlier hold)).elim
      · exact hnew
    exact mem_union_right _ (mem_image.mpr ⟨E, hER, rfl⟩)

  · intro E hE
    have hEF := mem_sdiff.mp hE
    have hER : E ∈ R.image (Finset.map e) := (mem_union.mp hEF.1).resolve_left hEF.2
    obtain ⟨C, _hC, rfl⟩ := mem_image.mp hER
    intro T hT
    obtain ⟨i, _hi, rfl⟩ := mem_map.mp hT
    exact mem_map.mpr ⟨i, mem_univ i, rfl⟩

  · apply hcounts.mono
    intro E hE
    have hh := mem_sdiff.mp hE
    exact (mem_union.mp hh.1).resolve_left hh.2

theorem exists_source_regularization_order_step_with_support
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [Nonempty I] {ell j s : ℕ}
    {W : Vortex V ell} {delta a : ℝ≥0}
    (P : SourceRandomConfigurationParameters W j delta a s)
    (L earlier : Finset (Finset I)) (hL : ∀ E ∈ L, E.card = j - 2)
    (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell))
    (hsize : 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card I)
    (b : ℕ) (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    let G := trimForbiddenSupersets L earlier
    let H := regularizationForbiddenFamily e (j - 2) G earlier
    (2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree H ≤
        (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (j - 2 - 1) →
    2 * regularizationBaseHazard G (j - 2) ≤ sourceRandomConfigurationProbability W.terminalSize delta j →
    finiteHypergraphDegreeGap G * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
        (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1 →
    ∃ Lstar : Finset (Finset I), ∃ Fsup : ForbiddenFamilyOn V,
      (∀ E ∈ Lstar, E.card = j - 2) ∧
      finiteHypergraphMaxDegree Lstar ≤ 9 * finiteHypergraphMaxDegree L ∧
      finiteHypergraphDegreeGap Lstar ≤ b ∧
      (∀ E ∈ Lstar, ∀ C ∈ earlier, ¬ C ⊆ E) ∧
      (∀ E ∈ L, ∃ C ∈ earlier ∪ Lstar, C ⊆ E) ∧
      F ⊆ Fsup ∧ (Lstar \ L).image (Finset.map e) ⊆ Fsup ∧
      SourceVortexWellSpread W j Fsup (y + a) (z + 3 * a) ∧
      (∀ E ∈ Fsup \ F, E ⊆ Finset.univ.map e) := by
  dsimp only
  intro hdensity hprob hsmall
  obtain ⟨Lstar, Fsup, hu, hm, hg, ha, hc, hf, hn, hs, hsup, _hcounts⟩ :=
    exists_source_regularization_order_step_with_counts P L earlier hL e hsupport hsize b F y z hF
      hdeltaY hdensity hprob hsmall
  exact ⟨Lstar, Fsup, hu, hm, hg, ha, hc, hf, hn, hs, hsup⟩

theorem exists_source_regularization_order_step
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] [Nonempty I] {ell j s : ℕ}
    {W : Vortex V ell} {delta a : ℝ≥0}
    (P : SourceRandomConfigurationParameters W j delta a s)
    (L earlier : Finset (Finset I)) (hL : ∀ E ∈ L, E.card = j - 2)
    (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell))
    (hsize : 16 * 2 ^ (j - 2 - 1) * (j - 2 - 1) ≤ Fintype.card I)
    (b : ℕ) (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    let G := trimForbiddenSupersets L earlier
    let H := regularizationForbiddenFamily e (j - 2) G earlier
    (2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree H ≤
        (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (j - 2 - 1) →
    2 * regularizationBaseHazard G (j - 2) ≤ sourceRandomConfigurationProbability W.terminalSize delta j →
    finiteHypergraphDegreeGap G * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
        (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1 →
    ∃ Lstar : Finset (Finset I), ∃ Fsup : ForbiddenFamilyOn V,
      (∀ E ∈ Lstar, E.card = j - 2) ∧
      finiteHypergraphMaxDegree Lstar ≤ 9 * finiteHypergraphMaxDegree L ∧
      finiteHypergraphDegreeGap Lstar ≤ b ∧
      (∀ E ∈ Lstar, ∀ C ∈ earlier, ¬ C ⊆ E) ∧
      (∀ E ∈ L, ∃ C ∈ earlier ∪ Lstar, C ⊆ E) ∧
      F ⊆ Fsup ∧ (Lstar \ L).image (Finset.map e) ⊆ Fsup ∧
      SourceVortexWellSpread W j Fsup (y + a) (z + 3 * a) := by
  dsimp only
  intro hdensity hprob hsmall
  obtain ⟨Lstar, Fsup, huniform, hmax, hgap, havoid, hcover, hsub, himage, hspread, _hsupport⟩ :=
    exists_source_regularization_order_step_with_support P L earlier hL e hsupport hsize b F y z hF
      hdeltaY hdensity hprob hsmall
  exact ⟨Lstar, Fsup, huniform, hmax, hgap, havoid, hcover, hsub, himage, hspread⟩

end

end Erdos207
