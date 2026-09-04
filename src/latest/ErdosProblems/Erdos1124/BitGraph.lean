/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.IntegralFlow
import ErdosProblems.Erdos1124.TorusAction

/-!
# The bit-direction permutation graph

The dyadic flow is indexed by directions in `{0,1}^d`.  This file packages
those translations as the permutation graph expected by the integral-flow
rounding theorem and records that the two divergence definitions agree.
-/

open scoped BigOperators

namespace Erdos1124.BitGraph

noncomputable section

open TorusAction

/-- Translation by every bit direction of the generated torus action. -/
def bitPermutationGraph {d k : ℕ} (u : Fin d → Torus k) :
    IntegralFlow.PermutationGraph (Torus k) (Flow.BitDirection d) where
  move g := Equiv.addLeft (displacement u (Flow.bitVector g))

lemma displacement_neg {d k : ℕ} (u : Fin d → Torus k) (n : Flow.Lattice d) :
    displacement u (-n) = -displacement u n := by
  apply eq_neg_of_add_eq_zero_left
  rw [← displacement_add, neg_add_cancel, displacement_zero]

@[simp]
lemma bitPermutationGraph_move_apply {d k : ℕ} (u : Fin d → Torus k)
    (g : Flow.BitDirection d) (x : Torus k) :
    (bitPermutationGraph u).move g x =
      displacement u (Flow.bitVector g) + x := rfl

@[simp]
lemma bitPermutationGraph_move_symm_apply {d k : ℕ} (u : Fin d → Torus k)
    (g : Flow.BitDirection d) (x : Torus k) :
    ((bitPermutationGraph u).move g).symm x =
      displacement u (-Flow.bitVector g) + x := by
  change -displacement u (Flow.bitVector g) + x = _
  rw [displacement_neg]

/-- The permutation-graph and dyadic-flow divergence conventions coincide. -/
theorem divergence_eq_flow_divergence {d k : ℕ} (u : Fin d → Torus k)
    (φ : Flow.DirectionalFlow (d := d) (X := Torus k) (𝕜 := ℝ))
    (x : Torus k) :
    letI := torusAddAction u
    (bitPermutationGraph u).divergence (fun y g ↦ φ g y) x =
      Flow.divergence (d := d) φ x := by
  let := torusAddAction u
  rw [IntegralFlow.PermutationGraph.divergence, Flow.divergence]
  apply Finset.sum_congr rfl
  intro g hg
  rw [bitPermutationGraph_move_symm_apply]
  rfl

/-- Integer-valued target-minus-source demand. -/
noncomputable def intDemand {k : ℕ} (A B : Set (Torus k)) (x : Torus k) : ℤ := by
  classical
  exact (if x ∈ B then 1 else 0) - if x ∈ A then 1 else 0

/-- The real signed indicator used by the limiting flow is the cast of the
integer demand, with the required sign. -/
lemma intDemand_cast {k : ℕ} (A B : Set (Torus k)) (x : Torus k) :
    (intDemand A B x : ℝ) = -TorusAction.signedIndicator A B x := by
  classical
  unfold intDemand TorusAction.signedIndicator
  split_ifs <;> norm_num

/-- Round a bounded bit-direction real flow solving the signed-indicator
equation to an integer flow with the same capacity and divergence. -/
theorem exists_integral_bitFlow {d k : ℕ} (u : Fin d → Torus k)
    (A B : Set (Torus k))
    (φ : Flow.DirectionalFlow (d := d) (X := Torus k) (𝕜 := ℝ)) (b : ℕ)
    (hdiv : letI := torusAddAction u
      ∀ x, Flow.divergence (d := d) φ x = -TorusAction.signedIndicator A B x)
    (hbound : ∀ g x, |φ g x| ≤ b) :
    ∃ ψ : Torus k → Flow.BitDirection d → ℤ,
      (∀ x g, |ψ x g| ≤ b) ∧
      ∀ x, (bitPermutationGraph u).divergence ψ x = intDemand A B x := by
  let := torusAddAction u
  apply IntegralFlow.exists_integral_flow (bitPermutationGraph u)
    (fun x g ↦ φ g x) (intDemand A B) b
  · intro x
    rw [divergence_eq_flow_divergence u φ x, hdiv x, ← intDemand_cast]
  · intro x g
    exact hbound g x

end

end Erdos1124.BitGraph
