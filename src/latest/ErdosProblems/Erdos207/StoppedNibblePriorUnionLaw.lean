/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphTerminalInsertionUnionLaw
import ErdosProblems.Erdos207.TimedStoppedSharpJointInclusion
import ErdosProblems.Erdos207.SupportedConditionedPreliminaryKernel

/-! # The actual stopped nibble supplies the generalized source moment law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem timedStoppedGreedy_supported_empty_initial
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop)
    (S₀ : GreedyStateOn V) (hInv : GreedyInvariant F S₀) (hchosen : S₀.chosen = ∅) :
    (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀).SupportedOn
      (fun z ↦ GreedyInvariant F z.2 ∧ z.2.available ⊆ S₀.available ∧ z.2.chosen ⊆ S₀.available) := by
  intro z hz
  have h := timedStoppedGreedyProcess_supported_relativeGreedyTrajectory n F active S₀ hInv z hz
  have hc := h.2.2.2
  rw [hchosen, empty_union] at hc
  exact ⟨h.1, h.2.1, hc⟩

theorem IsGraphStronglyWellDistributed.stopped_nibble_selected_union
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {ell : ℕ}
    {P : FiniteLaw D} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : D → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed P W k G initial later p C b)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (n floor : ℕ) (F : D → ForbiddenFamilyOn V) (active : D → ℕ → GreedyStateOn V → Prop)
    (S₀ : D → GreedyStateOn V) (delta : ℝ≥0) (hdelta : delta ≤ 1) (hfloor : 0 < floor)
    (hratio : (n : ℝ≥0) * (floor : ℝ≥0)⁻¹ ≤ delta)
    (hactive : ∀ d i S, active d i S → floor ≤ S.available.card)
    (hInv : ∀ d, GreedyInvariant (F d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (hgeometry : ∀ d T, T ∈ (S₀ d).available → T.1 ⊆ W.U k)
    (m : ℕ) (U : TripleSystemOn V) (hU : U.card ≤ m) :
    (P.jointBind (fun d ↦ FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel (F d)) (active d) (S₀ d))).probability
      (fun z ↦ U ⊆ (initial z.1 ∪ later z.1) ∪ z.2.2.chosen) ≤
      (4 * C) ^ m *
        (setWeight (vortexTripleWeight (W.prefix k) (2 + delta * (W.prefix k).terminalSize)) U + b) := by
  apply h.joint_terminal_insertion_union hp hC hnonempty
    (fun d ↦ FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel (F d)) (active d) (S₀ d))
    (fun _ z ↦ z.2.chosen) delta hdelta _ _ m U hU
  · intro d z hz T hT
    have hs := timedStoppedGreedy_supported_empty_initial n (F d) (active d) (S₀ d)
      (hInv d) (hchosen d) z hz
    exact hgeometry d T (hs.2.2 hT)
  · intro d Q
    exact (timedStoppedGreedyProcess_probability_subset_chosen_le_sharp n (F d) (active d)
      floor hfloor (hactive d) (S₀ d) Q (by rw [hchosen d]; exact disjoint_empty_right Q)).trans
        (pow_le_pow_left' hratio Q.card)

end

end Erdos207
