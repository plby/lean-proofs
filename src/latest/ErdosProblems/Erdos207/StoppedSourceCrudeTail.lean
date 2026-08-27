/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCrudeStateTail
import ErdosProblems.Erdos207.StoppedNibblePriorUnionLaw
import ErdosProblems.Erdos207.VortexShellGeometry

/-! # The generalized source bound for the actual conditional stopped greedy law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsGraphStronglyWellDistributed.stopped_source_crude_failure_le_sum
    {D V I : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype I]
    {ell q s : ℕ} {P : FiniteLaw D} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : D → TripleSystemOn V} {p C b : ℝ≥0}
    (hstrong : IsGraphStronglyWellDistributed P W k G initial later p C b)
    (hp : p ≤ 1) (hC : 1 ≤ C) (hnonempty : ∀ i, (W.U i).Nonempty)
    (n floor : ℕ) (J : D → ForbiddenFamilyOn V) (active : D → ℕ → GreedyStateOn V → Prop)
    (S₀ : D → GreedyStateOn V) (delta : ℝ≥0) (hdelta : delta ≤ 1) (hfloor : 0 < floor)
    (hratio : (n : ℝ≥0) * (floor : ℝ≥0)⁻¹ ≤ delta)
    (hactive : ∀ d i S, active d i S → floor ≤ S.available.card)
    (hInv : ∀ d, GreedyInvariant (J d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (hgeometry : ∀ d T, T ∈ (S₀ d).available → T.1 ⊆ W.U k)
    (F : I → ForbiddenFamilyOn V) (order : I → ℕ) (y z : I → ℝ≥0)
    (hF : ∀ i, SourceVortexWellSpread (W.prefix k) (order i) (F i) (y i) (z i))
    (horder : ∀ i, order i ≤ q) (hidentical : ∀ i i', order i = order i' → F i = F i')
    (hprior : P.SupportedOn (fun d ↦ Disjoint (S₀ d).available (initial d ∪ later d) ∧
      ∀ B ∈ J d, B ⊆ (S₀ d).available ∧ ∃ i E, E ∈ F i ∧ B ⊆ E ∧ E \ B ⊆ initial d ∪ later d))
    (K : CrudeThresholds) (hK : ∀ i : CrudeStatisticIndex V q, 0 < crudeThreshold K i) :
    (P.jointBind (fun d ↦ FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel (J d)) (active d) (S₀ d))).probability
      (fun z ↦ ¬ CrudeStateBounds (J z.1) z.2.2 q K) ≤
      ∑ i : CrudeStatisticIndex V q,
        sourceCrudeTailBound (W.prefix k) order z s (2 + delta * (W.prefix k).terminalSize)
          ((4 * C) ^ (s * (2 * q))) (((4 * C) ^ (s * (2 * q))) * b) K i := by
  classical
  have hsupported := hprior.jointBind (Q := fun d (u : Fin (n + 1) × GreedyStateOn V) ↦ GreedyInvariant (J d) u.2 ∧
      u.2.available ⊆ (S₀ d).available ∧ u.2.chosen ⊆ (S₀ d).available)
    (fun d _ ↦ timedStoppedGreedy_supported_empty_initial n (J d) (active d) (S₀ d) (hInv d) (hchosen d))
  apply source_crudeState_failure_le_sum (s := s) hF horder hidentical
    (2 + delta * (W.prefix k).terminalSize) (by
      exact (by norm_num : (1 : ℝ≥0) ≤ 2).trans (le_add_of_nonneg_right zero_le))
    (P.jointBind (fun d ↦ FiniteLaw.timedStoppedProcessLaw n (fun _ ↦ greedyKernel (J d)) (active d) (S₀ d)))
    (fun u ↦ J u.1) (fun u ↦ u.2.2) (fun u ↦ (S₀ u.1).available) (fun u ↦ initial u.1 ∪ later u.1)
  · intro u hu
    have hs := hsupported u hu
    exact ⟨hs.2.1, hs.2.2.1, hs.1.1,
      fun T hT ↦ W.prefix_level_eq_last_of_subset k T (hgeometry u.1 T hT), hs.1.2⟩
  · exact hK
  · intro H hH
    simpa only [mul_add] using hstrong.stopped_nibble_selected_union hp hC hnonempty
      n floor J active S₀ delta hdelta hfloor hratio hactive hInv hchosen hgeometry (s * (2 * q)) H hH

end

end Erdos207
