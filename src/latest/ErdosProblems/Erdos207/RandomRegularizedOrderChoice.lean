/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizedOrderChoice
import ErdosProblems.Erdos207.FiniteLawSupportPullback

/-! # The deterministic regularizer's gap exception is bounded in the original data law -/

namespace Erdos207

open Finset

noncomputable section

theorem regularizedOrderChoice_gap_failure_of_marginal
    {Ω D V : Type*} [Fintype Ω] [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    (e : (d : D) → I d ↪ TripleOn V) (j b : ℕ)
    (L earlier : (d : D) → Finset (Finset (I d)))
    (hL : ∀ d E, E ∈ L d → E.card = j - 2) (Fsup : ForbiddenFamilyOn V)
    (M : FiniteLaw Ω) (data : Ω → D) (P : FiniteLaw D) (hmarg : FiniteLaw.map data M = P)
    (accepted : Ω → ForbiddenFamilyOn V) (haccepted : M.SupportedOn (fun x ↦ accepted x ⊆ Fsup)) :
    P.probability (fun d ↦ b < finiteHypergraphDegreeGap
      (regularizedOrderChoice (e d) j b (L d) (earlier d) Fsup)) ≤
    M.probability (fun x ↦ ¬ RegularizationOutputWitness (e (data x))
      (trimForbiddenSupersets (L (data x)) (earlier (data x)))
      (regularizationForbiddenFamily (e (data x)) (j - 2)
        (trimForbiddenSupersets (L (data x)) (earlier (data x))) (earlier (data x)))
      (j - 2) b (accepted x)) := by
  have heq := congrArg (fun K : FiniteLaw D ↦ K.probability (fun d ↦
    b < finiteHypergraphDegreeGap (regularizedOrderChoice (e d) j b (L d) (earlier d) Fsup))) hmarg
  rw [FiniteLaw.probability_map] at heq
  rw [← heq]
  apply M.probability_mono_of_supported haccepted
  intro x hsub hgap hwitness
  have hex := hwitness.exists_regularizedOrderCore (e (data x)) (L (data x)) (earlier (data x))
    (hL (data x)) (accepted x) Fsup hsub
  have hcore := regularizedOrderChoice_core_of_exists (e (data x)) j b
    (L (data x)) (earlier (data x)) Fsup hex
  exact (not_lt_of_ge hcore.gap) hgap

end

end Erdos207
