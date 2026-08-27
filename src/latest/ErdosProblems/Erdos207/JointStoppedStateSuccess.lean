/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedGreedyStateTerminal
import ErdosProblems.Erdos207.FiniteJointConditioning

/-! # Quantitative joint horizon success with bad inputs and retrospective crude errors -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem joint_stopped_state_horizon_failure_le
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (P : FiniteLaw D) (horizon : D → ℕ) (F : D → ForbiddenFamilyOn V)
    (active : D → ℕ → GreedyStateOn V → Prop) (S₀ : D → GreedyStateOn V)
    (Good : D → Prop) (Band Crude : D → GreedyStateOn V → Prop)
    (hInv : ∀ d, GreedyInvariant (F d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (havailable : ∀ d i, i < horizon d → ∀ S, GreedyInvariant (F d) S → active d i S → S.available.Nonempty)
    (hactive : ∀ d, Good d → ∀ S, GreedyInvariant (F d) S → GreedyContainedIn (S₀ d).available S →
      S.chosen.card ≤ horizon d → Band d S → Crude d S → active d S.chosen.card S)
    (eta beta epsilon : ℝ≥0) (hinput : P.probability (fun d ↦ ¬ Good d) ≤ eta)
    (hband : ∀ d, Good d → (stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d)).probability (fun S ↦ ¬ Band d S) ≤ beta)
    (hcrude : (P.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d))).probability
      (fun u ↦ ¬ Crude u.1 u.2) ≤ epsilon) :
    (P.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d))).probability
      (fun u ↦ ¬ (Good u.1 ∧ u.2.chosen.card = horizon u.1 ∧ Band u.1 u.2 ∧ Crude u.1 u.2)) ≤
        eta + beta + epsilon := by
  classical
  let K := fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d)
  let L := P.jointBind K
  have hsupported := (show P.SupportedOn (fun _ ↦ True) from fun _ _ ↦ trivial).jointBind
    (Q := fun d S ↦ GreedyInvariant (F d) S ∧ GreedyContainedIn (S₀ d).available S ∧ S.chosen.card ≤ horizon d ∧
      (S.chosen.card = horizon d ∨ ¬ active d S.chosen.card S))
    (fun d _ ↦ stoppedGreedyStateLaw_supported_terminal (horizon d) (F d) (active d) (S₀ d)
      (hInv d) (hchosen d) (havailable d))
  have hsub : L.probability (fun u ↦ ¬ (Good u.1 ∧ u.2.chosen.card = horizon u.1 ∧ Band u.1 u.2 ∧ Crude u.1 u.2)) ≤
      L.probability (fun u ↦ ¬ Good u.1 ∨ (Good u.1 ∧ ¬ Band u.1 u.2) ∨ ¬ Crude u.1 u.2) := by
    apply L.probability_mono_of_supported hsupported
    intro u hu hbad
    by_cases hi : Good u.1
    · by_cases hb : Band u.1 u.2
      · right
        right
        intro hc
        have ha := hactive u.1 hi u.2 hu.2.1 hu.2.2.1 hu.2.2.2.1 hb hc
        have htime := hu.2.2.2.2.resolve_right (not_not_intro ha)
        exact hbad ⟨hi, htime, hb, hc⟩
      · exact Or.inr (Or.inl ⟨hi, hb⟩)
    · exact Or.inl hi
  have hbadBand : L.probability (fun u ↦ Good u.1 ∧ ¬ Band u.1 u.2) ≤ beta := by
    have h := P.jointBind_probability_and_le_on_support K Good (fun d S ↦ ¬ Band d S) beta
      (fun d _ hd ↦ hband d hd)
    exact h.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (P.probability_le_one Good) (show 0 ≤ beta from zero_le))
  have hbadInput : L.probability (fun u ↦ ¬ Good u.1) ≤ eta := by
    exact (FiniteLaw.probability_jointBind_fst P K (fun d ↦ ¬ Good d)).le.trans hinput
  have hor := L.probability_or_le (fun u ↦ ¬ Good u.1)
    (fun u ↦ (Good u.1 ∧ ¬ Band u.1 u.2) ∨ ¬ Crude u.1 u.2)
  have hor' := L.probability_or_le (fun u ↦ Good u.1 ∧ ¬ Band u.1 u.2) (fun u ↦ ¬ Crude u.1 u.2)
  exact (hsub.trans (hor.trans (add_le_add hbadInput (hor'.trans (add_le_add hbadBand hcrude))))).trans_eq (add_assoc _ _ _).symm

end

end Erdos207
