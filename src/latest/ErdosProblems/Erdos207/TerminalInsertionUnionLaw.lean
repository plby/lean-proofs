/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.JointUnionInclusion
import ErdosProblems.Erdos207.VortexWeight

/-! # Mixing a terminal insertion law into prior vortex-weighted selected data -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def terminalInsertionWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (delta : ℝ≥0) (T : TripleOn V) : ℝ≥0 := by
  classical
  exact if T.1 ⊆ W.U (Fin.last ell) then delta else 0

theorem terminalInsertionWeight_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (delta : ℝ≥0) (hdelta : delta ≤ 1) (T : TripleOn V) :
    terminalInsertionWeight W delta T ≤ 1 := by
  classical
  unfold terminalInsertionWeight
  split_ifs
  · exact hdelta
  · exact zero_le

theorem vortexTripleWeight_add_terminalInsertion
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (c delta : ℝ≥0) (hn : 0 < W.terminalSize) (T : TripleOn V) :
    vortexTripleWeight W c T + terminalInsertionWeight W delta T ≤
      vortexTripleWeight W (c + delta * W.terminalSize) T := by
  classical
  unfold terminalInsertionWeight
  split_ifs with hT
  · have hlevel : W.level T = Fin.last ell :=
      le_antisymm (Fin.le_last _) ((W.subset_iff_le_level T (Fin.last ell)).mp hT)
    unfold vortexTripleWeight
    rw [hlevel]
    change c / (W.terminalSize : ℝ≥0) + delta ≤ (c + delta * W.terminalSize) / W.terminalSize
    rw [add_div, mul_div_cancel_right₀ delta (by exact_mod_cast Nat.ne_of_gt hn)]
  · simp only [add_zero]
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right zero_le) zero_le

theorem terminal_supported_joint_inclusion
    {S V : Type*} [Fintype S] [Fintype V] [DecidableEq V] {ell : ℕ}
    (K : FiniteLaw S) (selected : S → TripleSystemOn V) (W : Vortex V ell) (delta : ℝ≥0)
    (hsupport : K.SupportedOn (fun s ↦ ∀ T ∈ selected s, T.1 ⊆ W.U (Fin.last ell)))
    (hjoint : ∀ Q, K.probability (fun s ↦ Q ⊆ selected s) ≤ delta ^ Q.card)
    (Q : TripleSystemOn V) :
    K.probability (fun s ↦ Q ⊆ selected s) ≤ setWeight (terminalInsertionWeight W delta) Q := by
  classical
  by_cases hQ : ∀ T ∈ Q, T.1 ⊆ W.U (Fin.last ell)
  · have heq : setWeight (terminalInsertionWeight W delta) Q = delta ^ Q.card := by
      unfold setWeight
      calc
        _ = ∏ _T ∈ Q, delta := prod_congr rfl (fun T hT ↦ if_pos (hQ T hT))
        _ = _ := prod_const _
    rw [heq]
    exact hjoint Q
  · have hzero : K.probability (fun s ↦ Q ⊆ selected s) ≤ K.probability (fun _ ↦ False) := by
      apply K.probability_mono_of_supported hsupport
      intro s hs hsub
      exact hQ (fun T hT ↦ hs T (hsub hT))
    rw [K.probability_false] at hzero
    exact hzero.trans zero_le

theorem joint_union_vortex_inclusion_with_error
    {D S V : Type*} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (P : FiniteLaw D) (K : D → FiniteLaw S) (old : D → TripleSystemOn V) (new : D → S → TripleSystemOn V)
    (W : Vortex V ell) (c delta A b : ℝ≥0) (hn : 0 < W.terminalSize) (hdelta : delta ≤ 1)
    (U : TripleSystemOn V)
    (hold : ∀ Q ⊆ U, P.probability (fun d ↦ Q ⊆ old d) ≤ A * setWeight (vortexTripleWeight W c) Q + b)
    (hsupport : ∀ d, (K d).SupportedOn (fun s ↦ ∀ T ∈ new d s, T.1 ⊆ W.U (Fin.last ell)))
    (hnew : ∀ d Q, (K d).probability (fun s ↦ Q ⊆ new d s) ≤ delta ^ Q.card) :
    (P.jointBind K).probability (fun z ↦ U ⊆ old z.1 ∪ new z.1 z.2) ≤
      A * setWeight (vortexTripleWeight W (c + delta * W.terminalSize)) U + b * 2 ^ U.card := by
  apply (joint_union_inclusion_with_uniform_error P K old new (vortexTripleWeight W c)
    (terminalInsertionWeight W delta) A b U hold
    (fun d ↦ terminal_supported_joint_inclusion (K d) (new d) W delta (hsupport d) (hnew d))
    (fun T _ ↦ terminalInsertionWeight_le_one W delta hdelta T)).trans
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left _ zero_le
  exact prod_le_prod' (fun T _ ↦ vortexTripleWeight_add_terminalInsertion W c delta hn T)

end

end Erdos207
