/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationStepBudgets

/-! # Explicit inputs and proved outputs of the source regularized-order induction -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

structure SourceRegularizationOrderInput
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {ell : ℕ} (W : Vortex V ell) (j : ℕ) (L : Finset (Finset I)) (F : ForbiddenFamilyOn V)
    (b s : ℕ) (y z a delta sigma C B : ℝ≥0) : Prop where
  parameters : SourceRandomConfigurationParameters W j delta a s
  uniform : ∀ E ∈ L, E.card = j - 2
  spread : SourceVortexWellSpread W j F y z
  delta_y : delta * y ≤ W.terminalSize
  size : 16 * 2 ^ (j - 3) * (j - 3) ≤ Fintype.card I
  maximum_power : 9 * finiteHypergraphMaxDegree L ≤ W.terminalSize ^ (j - 3)
  sigma_pos : 0 < sigma
  constant_pos : 0 < C
  mass : sigma * (W.terminalSize : ℝ≥0) ^ 3 / C ≤ Fintype.card I
  degree : (finiteHypergraphMaxDegree L : ℝ≥0) ≤
    B * sigma ^ (j - 3) * (W.terminalSize : ℝ≥0) ^ (j - 3)
  density : 324 * (2 : ℝ≥0) ^ (j - 2) * (2 * C) ^ (j - 3) * (j - 3).factorial ≤
    sigma ^ (j - 3) * W.terminalSize
  coefficient : (2 : ℝ≥0) ^ (j - 1) * (2 * C) ^ (j - 3) * (j - 3).factorial * B ≤ delta
  failure : finiteHypergraphMaxDegree L * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
    (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1

structure SourceRegularizationOrderResult
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Nonempty I]
    {ell : ℕ} (W : Vortex V ell) (e : I ↪ TripleOn V) (j b : ℕ)
    (L earlier : Finset (Finset I)) (F : ForbiddenFamilyOn V) (y z : ℝ≥0)
    (Lstar : Finset (Finset I)) (Fsup : ForbiddenFamilyOn V) : Prop where
  uniform : ∀ E ∈ Lstar, E.card = j - 2
  maximum : finiteHypergraphMaxDegree Lstar ≤ 9 * finiteHypergraphMaxDegree L
  gap : finiteHypergraphDegreeGap Lstar ≤ b
  no_earlier_subset : ∀ E ∈ Lstar, ∀ C ∈ earlier, ¬ C ⊆ E
  covers_original : ∀ E ∈ L, ∃ C ∈ earlier ∪ Lstar, C ⊆ E
  contains_original : F ⊆ Fsup
  contains_new_constraints : (Lstar \ L).image (Finset.map e) ⊆ Fsup
  spread : SourceVortexWellSpread W j Fsup y z
  new_support : ∀ E ∈ Fsup \ F, E ⊆ Finset.univ.map e

theorem SourceRegularizationOrderInput.exists_result_with_counts
    {V I K : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    [Nonempty I] [DecidableEq K] {ell j b s : ℕ}
    {W : Vortex V ell} {L : Finset (Finset I)} {F : ForbiddenFamilyOn V}
    {y z a delta sigma C B : ℝ≥0}
    (h : SourceRegularizationOrderInput W j L F b s y z a delta sigma C B)
    (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell))
    (orders : Finset K) (earlier : K → Finset (Finset I)) (size : K → ℕ)
    (horders : orders.card ≤ W.terminalSize)
    (hsize : ∀ i ∈ orders, 2 ≤ size i ∧ size i ≤ j - 2)
    (huniform : ∀ i ∈ orders, ∀ E ∈ earlier i, E.card = size i)
    (hearlier : ∀ i ∈ orders, finiteHypergraphMaxDegree (earlier i) ≤ W.terminalSize ^ (size i - 1)) :
    ∃ Lstar Fsup, SourceRegularizationOrderResult W e j b L (orders.biUnion earlier) F
      (y + a) (z + 3 * a) Lstar Fsup ∧
      SourceAugmentationCounts j W.terminalSize F (Fsup \ F) a := by
  have hj := h.parameters.order
  have he : j - 2 - 1 = j - 3 := by omega
  have hpow : 0 < 2 ^ (j - 3) := by positivity
  have hm : 2 * (j - 3) ≤ Fintype.card I :=
    (Nat.mul_le_mul_right (j - 3) (show 2 ≤ 16 * 2 ^ (j - 3) by omega)).trans h.size
  have hLpower : finiteHypergraphMaxDegree L ≤ W.terminalSize ^ (j - 3) := by
    have hh := h.maximum_power
    omega
  obtain ⟨hdensity, hprob, hsmall⟩ := sourceRegularization_order_scalar_conditions W e hsupport hj
    h.spread.terminal_nonempty hm L orders earlier size horders hsize huniform hearlier hLpower
    sigma C B delta h.sigma_pos h.constant_pos h.mass h.degree h.density h.coefficient b s h.failure
  obtain ⟨Lstar, Fsup, hu, hm', hg, ha, hc, hf, hn, hs, hsup, hcounts⟩ :=
    exists_source_regularization_order_step_with_counts h.parameters L (orders.biUnion earlier)
      h.uniform e hsupport (by simpa only [he] using h.size) b F y z h.spread h.delta_y
      hdensity hprob hsmall
  exact ⟨Lstar, Fsup, ⟨hu, hm', hg, ha, hc, hf, hn, hs, hsup⟩, hcounts⟩

theorem SourceRegularizationOrderInput.exists_result
    {V I K : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    [Nonempty I] [DecidableEq K] {ell j b s : ℕ}
    {W : Vortex V ell} {L : Finset (Finset I)} {F : ForbiddenFamilyOn V}
    {y z a delta sigma C B : ℝ≥0}
    (h : SourceRegularizationOrderInput W j L F b s y z a delta sigma C B)
    (e : I ↪ TripleOn V) (hsupport : ∀ i, (e i).1 ⊆ W.U (Fin.last ell))
    (orders : Finset K) (earlier : K → Finset (Finset I)) (size : K → ℕ)
    (horders : orders.card ≤ W.terminalSize)
    (hsize : ∀ i ∈ orders, 2 ≤ size i ∧ size i ≤ j - 2)
    (huniform : ∀ i ∈ orders, ∀ E ∈ earlier i, E.card = size i)
    (hearlier : ∀ i ∈ orders, finiteHypergraphMaxDegree (earlier i) ≤ W.terminalSize ^ (size i - 1)) :
    ∃ Lstar Fsup, SourceRegularizationOrderResult W e j b L (orders.biUnion earlier) F
      (y + a) (z + 3 * a) Lstar Fsup := by
  obtain ⟨Lstar, Fsup, hresult, _hcounts⟩ :=
    h.exists_result_with_counts e hsupport orders earlier size horders hsize huniform hearlier
  exact ⟨Lstar, Fsup, hresult⟩

end

end Erdos207
