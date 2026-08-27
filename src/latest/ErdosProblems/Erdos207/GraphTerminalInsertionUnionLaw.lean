/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.TerminalInsertionUnionLaw
import ErdosProblems.Erdos207.GraphRestrictedUnionDistribution

/-! # The actual prior graph law supplies the mixed selected-union moment hypothesis -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsGraphStronglyWellDistributed.joint_terminal_insertion_union
    {D S V : Type*} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {P : FiniteLaw D} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : D → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed P W k G initial later p C b)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (K : D → FiniteLaw S) (new : D → S → TripleSystemOn V) (delta : ℝ≥0) (hdelta : delta ≤ 1)
    (hsupport : ∀ d, (K d).SupportedOn (fun s ↦ ∀ T ∈ new d s, T.1 ⊆ W.U k))
    (hnew : ∀ d Q, (K d).probability (fun s ↦ Q ⊆ new d s) ≤ delta ^ Q.card)
    (m : ℕ) (U : TripleSystemOn V) (hU : U.card ≤ m) :
    (P.jointBind K).probability (fun z ↦ U ⊆ (initial z.1 ∪ later z.1) ∪ new z.1 z.2) ≤
      (4 * C) ^ m *
        (setWeight (vortexTripleWeight (W.prefix k) (2 + delta * (W.prefix k).terminalSize)) U + b) := by
  have htwo : (1 : ℝ≥0) ≤ 2 * C := one_le_mul_of_one_le_of_one_le (by norm_num) hC
  have hold : ∀ Q ⊆ U, P.probability (fun d ↦ Q ⊆ initial d ∪ later d) ≤
      (2 * C) ^ m * setWeight (vortexTripleWeight (W.prefix k) 2) Q + (2 * C) ^ m * b := by
    intro Q hQ
    have hbase := h.probability_union_and_edges_prefix_le hp hnonempty Q ∅ (empty_subset _)
    have hbase' : P.probability (fun d ↦ Q ⊆ initial d ∪ later d) ≤
        (2 * C) ^ Q.card * (setWeight (vortexTripleWeight (W.prefix k) 2) Q + b) := by
      simpa using hbase
    apply hbase'.trans
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ htwo ((card_le_card hQ).trans hU)) zero_le
  have hn : 0 < (W.prefix k).terminalSize := by
    simpa only [Vortex.prefix_terminalSize] using (hnonempty k).card_pos
  have hsupport' : ∀ d, (K d).SupportedOn
      (fun s ↦ ∀ T ∈ new d s, T.1 ⊆ (W.prefix k).U (Fin.last k.val)) := by
    simpa only [Vortex.prefix_U, vortexPrefixEmbedding_last] using hsupport
  have hbound := joint_union_vortex_inclusion_with_error P K (fun d ↦ initial d ∪ later d) new
    (W.prefix k) 2 delta ((2 * C) ^ m) ((2 * C) ^ m * b) hn hdelta U hold hsupport' hnew
  apply hbound.trans
  let X := setWeight (vortexTripleWeight (W.prefix k) (2 + delta * (W.prefix k).terminalSize)) U
  change (2 * C) ^ m * X + (2 * C) ^ m * b * 2 ^ U.card ≤ (4 * C) ^ m * (X + b)
  have hpow : (2 : ℝ≥0) ^ U.card ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hU
  have hone : (1 : ℝ≥0) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  calc
    _ ≤ ((2 * C) ^ m * X) * 2 ^ m + ((2 * C) ^ m * b) * 2 ^ m := by
      apply add_le_add
      · exact le_mul_of_one_le_right (zero_le : (0 : ℝ≥0) ≤ (2 * C) ^ m * X) hone
      · exact mul_le_mul_of_nonneg_left hpow zero_le
    _ = _ := by
      have hfour : (4 : ℝ≥0) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
      simp only [mul_pow]
      rw [hfour]
      ring

end

end Erdos207
