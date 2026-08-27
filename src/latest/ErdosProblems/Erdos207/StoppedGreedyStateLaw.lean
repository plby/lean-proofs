/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StoppedNibblePriorUnionLaw
import ErdosProblems.Erdos207.MappedStoppedProcess

/-! # State marginals permit data-dependent stopped horizons without changing the process -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def stoppedGreedyStateLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V) :
    FiniteLaw (GreedyStateOn V) :=
  FiniteLaw.map Prod.snd (FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel F) active S₀)

theorem stoppedGreedyStateLaw_supported
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (hInv : GreedyInvariant F S₀) (hchosen : S₀.chosen = ∅) :
    (stoppedGreedyStateLaw n F active S₀).SupportedOn
      (fun S ↦ GreedyInvariant F S ∧ S.available ⊆ S₀.available ∧ S.chosen ⊆ S₀.available) :=
  (timedStoppedGreedy_supported_empty_initial n F active S₀ hInv hchosen).map Prod.snd (fun _ h ↦ h)

theorem stoppedGreedyStateLaw_selected_inclusion
    {V : Type*} [Fintype V] [DecidableEq V]
    (n floor : ℕ) (F : ForbiddenFamilyOn V) (active : ℕ → GreedyStateOn V → Prop) (S₀ : GreedyStateOn V)
    (hfloor : 0 < floor) (hactive : ∀ i S, active i S → floor ≤ S.available.card)
    (hchosen : S₀.chosen = ∅) (Q : TripleSystemOn V) :
    (stoppedGreedyStateLaw n F active S₀).probability (fun S ↦ Q ⊆ S.chosen) ≤
      ((n : ℝ≥0) * (floor : ℝ≥0)⁻¹) ^ Q.card := by
  rw [stoppedGreedyStateLaw, FiniteLaw.probability_map]
  exact timedStoppedGreedyProcess_probability_subset_chosen_le_sharp n F active floor hfloor hactive S₀ Q
    (by rw [hchosen]; exact disjoint_empty_right Q)

theorem stoppedGreedyStateLaw_map
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (f : V ↪ W) (n : ℕ) (F : ForbiddenFamilyOn V)
    (active : ℕ → GreedyStateOn V → Prop) (active' : ℕ → GreedyStateOn W → Prop)
    (hactive : ∀ i S, active' i (mapGreedyState f S) ↔ active i S) (S₀ : GreedyStateOn V) :
    FiniteLaw.map (mapGreedyState f) (stoppedGreedyStateLaw n F active S₀) =
      stoppedGreedyStateLaw n (mapForbiddenFamily f F) active' (mapGreedyState f S₀) := by
  have h := congrArg (FiniteLaw.map Prod.snd) (timedStoppedGreedyProcessLaw_map f n F active active' hactive S₀)
  simpa only [stoppedGreedyStateLaw, FiniteLaw.map_comp, Function.comp_def] using h

theorem IsGraphStronglyWellDistributed.variable_stopped_nibble_selected_union
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {ell : ℕ}
    {P : FiniteLaw D} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : D → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed P W k G initial later p C b)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (horizon floor : D → ℕ) (F : D → ForbiddenFamilyOn V) (active : D → ℕ → GreedyStateOn V → Prop)
    (S₀ : D → GreedyStateOn V) (delta : ℝ≥0) (hdelta : delta ≤ 1) (hfloor : ∀ d, 0 < floor d)
    (hratio : ∀ d, (horizon d : ℝ≥0) * (floor d : ℝ≥0)⁻¹ ≤ delta)
    (hactive : ∀ d i S, active d i S → floor d ≤ S.available.card)
    (hInv : ∀ d, GreedyInvariant (F d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (hgeometry : ∀ d T, T ∈ (S₀ d).available → T.1 ⊆ W.U k)
    (m : ℕ) (U : TripleSystemOn V) (hU : U.card ≤ m) :
    (P.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d))).probability
      (fun z ↦ U ⊆ (initial z.1 ∪ later z.1) ∪ z.2.chosen) ≤
      (4 * C) ^ m *
        (setWeight (vortexTripleWeight (W.prefix k) (2 + delta * (W.prefix k).terminalSize)) U + b) := by
  apply h.joint_terminal_insertion_union hp hC hnonempty
    (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d))
    (fun _ S ↦ S.chosen) delta hdelta _ _ m U hU
  · intro d S hS T hT
    have hs := stoppedGreedyStateLaw_supported (horizon d) (F d) (active d) (S₀ d) (hInv d) (hchosen d) S hS
    exact hgeometry d T (hs.2.2 hT)
  · intro d Q
    exact (stoppedGreedyStateLaw_selected_inclusion (horizon d) (floor d) (F d) (active d) (S₀ d)
      (hfloor d) (hactive d) (hchosen d) Q).trans (pow_le_pow_left' (hratio d) Q.card)

end

end Erdos207
