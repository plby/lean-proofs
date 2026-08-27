/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SparseKSSSGraphLaw
import ErdosProblems.Erdos207.FiniteJointFailureRates
import ErdosProblems.Erdos207.StoppedGreedyStateTerminal

/-! # Conditional sparse mixed laws outside an explicitly bounded set of prior inputs -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem sparse_conditional_graph_law_failure_le
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    (L : FiniteLaw D) (horizon : D → ℕ) (F : D → ForbiddenFamilyOn V) (G : D → SimpleGraph V)
    (S₀ : D → GreedyStateOn V) (active : D → ℕ → GreedyStateOn V → Prop)
    (q b B k t Rmin c : ℕ) (a coeff : D → ℕ → ℝ) (E A : D → ℝ) (Good : D → Prop)
    (P : ∀ d, Good d → KSSSPowerParameters (F d) q (horizon d) b B k t Rmin (a d) (coeff d) (E d) (A d))
    (hactive : ∀ d i S, active d i S → Good d ∧
      KSSSPowerActive (F d) (graphPairFamily (G d)) q b B k t (a d) (E d) (A d) i S)
    (hInv : ∀ d, GreedyInvariant (F d) (S₀ d)) (hchosen : ∀ d, (S₀ d).chosen = ∅)
    (hambient : ∀ d, Good d → ∀ T ∈ (S₀ d).available, tripleEdgeFinset T ⊆ graphEdges (G d))
    (hcb : 2 * c ≤ b)
    (hfloor : ∀ d, Good d → ∀ i : ℕ, i ≤ horizon d → 1 / (t : ℝ) ^ c ≤ ksssEdgeDensity (E d) i)
    (epsilon delta : ℝ≥0) (hdelta : 0 < delta) (hsmall : delta < 1)
    (herror : (1 / 2 : ℝ≥0) ^ t ≤ delta)
    (hfailure : (L.jointBind (fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d))).probability
      (fun u ↦ ¬ Good u.1 ∨ ¬ active u.1 u.2.chosen.card u.2) ≤ epsilon) :
    L.probability (fun d ↦ ¬ (Good d ∧
      IsGraphMixedProductBound (stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d)) (fun S ↦ S.chosen) (G d)
        (Real.toNNReal (ksssEdgeDensity (E d) (horizon d))) (Real.toNNReal (E d) / Real.toNNReal (A d))
        (ksssSparseGraphProductConstant q (coeff d)) delta)) ≤ epsilon / delta := by
  classical
  let K := fun d ↦ stoppedGreedyStateLaw (horizon d) (F d) (active d) (S₀ d)
  let Bad := fun d (S : GreedyStateOn V) ↦ ¬ Good d ∨ ¬ active d S.chosen.card S
  have hrate := L.probability_large_conditional_failure_le K Bad epsilon delta hdelta hfailure
  apply le_trans _ hrate
  apply L.probability_mono
  intro d hnot
  by_contra hlarge
  have hrateSmall : (K d).probability (Bad d) < delta := lt_of_not_ge hlarge
  have hd : Good d := by
    by_contra hd
    have hone : (K d).probability (Bad d) = 1 := by
      apply (K d).probability_eq_one_of_supported
      exact fun _ _ ↦ Or.inl hd
    rw [hone] at hrateSmall
    exact (not_lt_of_ge hsmall.le) hrateSmall
  apply hnot
  refine ⟨hd, (P d hd).sparse_graph_mixed_product_bound (G d) (S₀ d) (active d)
    (fun i S ha ↦ (hactive d i S ha).2) (hInv d) (hchosen d) (hambient d hd)
    hcb (hfloor d hd) delta herror hsmall ?_⟩
  have hindex := stoppedGreedyStateLaw_probability_indexed (horizon d) (F d) (active d) (S₀ d)
    (hInv d) (hchosen d)
    (fun i hi S hS ha ↦ ((P d hd).kernelBounds (graphPairFamily (G d)) 1 (by norm_num)).available
      i hi S hS (hactive d i S ha).2)
    (fun i S ↦ ¬ active d i S)
  rw [← hindex]
  exact ((K d).probability_mono (fun S h ↦ Or.inr h)).trans hrateSmall.le

end

end Erdos207
