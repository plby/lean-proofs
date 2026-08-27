/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRegularizationOrderData

/-! # Reusing the checked order-input budgets before fixing a random envelope -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceRegularizationOrderInput.scalar_conditions
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
    let G := trimForbiddenSupersets L (orders.biUnion earlier)
    let H := regularizationForbiddenFamily e (j - 2) G (orders.biUnion earlier)
    ((2 : ℝ≥0) ^ (j - 2) * finiteHypergraphMaxDegree H ≤
      (1 / 36 : ℝ≥0) * Nat.choose (Fintype.card I) (j - 2 - 1)) ∧
    (2 * regularizationBaseHazard G (j - 2) ≤ sourceRandomConfigurationProbability W.terminalSize delta j) ∧
    (finiteHypergraphDegreeGap G * (2 * Fintype.card I * Real.exp (-(b : ℝ) / 8192)) +
      (sourceRandomFailureCoefficient W j : ℝ) * ((2 : ℝ) ^ s)⁻¹ < 1) := by
  have hj := h.parameters.order
  have hpow : 0 < 2 ^ (j - 3) := by positivity
  have hm : 2 * (j - 3) ≤ Fintype.card I :=
    (Nat.mul_le_mul_right (j - 3) (show 2 ≤ 16 * 2 ^ (j - 3) by omega)).trans h.size
  have hLpower : finiteHypergraphMaxDegree L ≤ W.terminalSize ^ (j - 3) := by
    have hh := h.maximum_power
    omega
  exact sourceRegularization_order_scalar_conditions W e hsupport hj h.spread.terminal_nonempty hm
    L orders earlier size horders hsize huniform hearlier hLpower sigma C B delta
    h.sigma_pos h.constant_pos h.mass h.degree h.density h.coefficient b s h.failure

end

end Erdos207
