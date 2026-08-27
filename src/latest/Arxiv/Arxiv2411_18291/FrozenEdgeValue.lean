import Arxiv.Arxiv2411_18291.FrozenEdgeConditionalVariance

/-!
# The frozen value agrees with the live clique degree

Before an edge is removed, the accumulated increments telescope to its
actual remaining clique degree minus the deterministic comparison value.
On the removal step itself, both terms are frozen.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

omit [Fintype V] in
theorem trajectoryCliques_mono (ω : ℕ → State V q) {i j : ℕ} (hij : i ≤ j) :
    trajectoryCliques ω i ⊆ trajectoryCliques ω j := by
  intro Q hQ
  obtain ⟨k, hk, hQ⟩ := mem_biUnion.mp hQ
  exact mem_biUnion.mpr ⟨k, mem_range.mpr ((mem_range.mp hk).trans_le hij), hQ⟩

theorem trajectory_support_mono (ω : ℕ → State V q) {i j : ℕ} (hij : i ≤ j) :
    cliqueSupport r (trajectoryCliques ω i) ⊆ cliqueSupport r (trajectoryCliques ω j) := by
  intro e he
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  exact mem_biUnion.mpr ⟨Q, trajectoryCliques_mono ω hij hQ, heQ⟩

theorem remainingCliques_at_succ (H : Finset (Block V q)) (ω : ℕ → State V q)
    (i : ℕ) (Q : Block V q) (hQ : ω (i + 1) = some Q) :
    remainingCliques r H (trajectoryCliques ω (i + 1)) =
      cliqueRemoval r (remainingCliques r H (trajectoryCliques ω i)) Q := by
  rw [trajectoryCliques_succ, hQ, Option.toFinset_some, union_singleton, remainingCliques_insert]

theorem edgeIncrement_of_removing (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ)
    (i : ℕ) (ω : ℕ → State V q) (Q : Block V q) (hQ : ω (i + 1) = some Q)
    (heQ : e.val ⊆ Q.val) : edgeIncrement H e c i ω = 0 := by
  rw [edgeIncrement, hQ, Option.elim_some]
  unfold edgeStepValue
  split_ifs
  · rfl
  · exact frozenTrackingIncrement_removed _ e _ Q heQ

theorem frozenEdgeProcess_succ_of_removing (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) (ω : ℕ → State V q) (Q : Block V q)
    (hQ : ω (i + 1) = some Q) (heQ : e.val ⊆ Q.val) :
    frozenEdgeProcess H e c (i + 1) ω = frozenEdgeProcess H e c i ω := by
  rw [frozenEdgeProcess_succ, edgeIncrement_of_removing H e c i ω Q hQ heQ, add_zero]

theorem frozenEdgeProcess_eq_of_alive (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (ω : ℕ → State V q) (n : ℕ)
    (hchoice : ∀ i < n, ∃ Q, ω (i + 1) = some Q)
    (he : e ∉ cliqueSupport r (trajectoryCliques ω n)) :
    frozenEdgeProcess H e c n ω =
      (((remainingCliques r H (trajectoryCliques ω n)).filter
        fun Q => e.val ⊆ Q.val).card : ℝ) - c n := by
  revert hchoice he
  induction n with
  | zero =>
    intro _ _
    simp [frozenEdgeProcess]
  | succ n ih =>
    intro hchoice he
    obtain ⟨Q, hQ⟩ := hchoice n (Nat.lt_succ_self n)
    have heprev : e ∉ cliqueSupport r (trajectoryCliques ω n) :=
      fun h => he (trajectory_support_mono ω (Nat.le_succ n) h)
    have heQ : ¬e.val ⊆ Q.val := by
      intro heQ
      apply he
      apply mem_biUnion.mpr
      refine ⟨Q, ?_, (mem_cliqueEdges _ _).mpr heQ⟩
      rw [trajectoryCliques_succ, hQ, Option.toFinset_some]
      exact mem_union_right _ (mem_singleton_self Q)
    have hprev := ih (fun i hi => hchoice i (by omega)) heprev
    let R := remainingCliques r H (trajectoryCliques ω n)
    have hinc : edgeIncrement H e c n ω =
        -(frozenEdgeLoss R e Q : ℝ) - (c (n + 1) - c n) := by
      simp only [edgeIncrement, hQ, Option.elim_some, edgeStepValue, historyCliques_prefix,
        if_neg heprev, frozenTrackingIncrement, if_pos heQ, R]
    have hpart : (((cliqueRemoval r R Q).filter fun P => e.val ⊆ P.val).card : ℝ) +
        (frozenEdgeLoss R e Q : ℝ) = (R.filter fun P => e.val ⊆ P.val).card := by
      rw [frozenEdgeLoss, if_pos heQ]
      exact_mod_cast cliqueRemoval_degree_partition R e Q
    rw [frozenEdgeProcess_succ, hprev, hinc, remainingCliques_at_succ H ω n Q hQ]
    change ((R.filter fun P => e.val ⊆ P.val).card : ℝ) - c n +
        (-(frozenEdgeLoss R e Q : ℝ) - (c (n + 1) - c n)) =
      (((cliqueRemoval r R Q).filter fun P => e.val ⊆ P.val).card : ℝ) - c (n + 1)
    linarith only [hpart]

end Arxiv2411_18291.CliqueRemovalProcess
