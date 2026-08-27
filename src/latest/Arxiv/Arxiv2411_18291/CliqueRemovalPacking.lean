import Arxiv.Arxiv2411_18291.CliqueRemovalProcess
import Arxiv.Arxiv2411_18291.FinalNegativeFamily

/-!
# Supported removal trajectories are actual clique packings

Every selected clique is legal and disjoint from previous choices.
Whenever an available clique exists at each step, exactly one new clique
is chosen per step and the remaining edge count is exact.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
variable (H : Finset (Block V q)) (ω : ℕ → State V q)
variable (hsupport : ∀ i, ω (i + 1) ∈ (step r H i (frestrictLe i ω)).support)

include hsupport

theorem trajectory_packing (n : ℕ) : trajectoryCliques ω n ⊆ H ∧
    (trajectoryCliques ω n : Set (Block V q)).Pairwise
      (fun P Q => Disjoint (cliqueEdges r P) (cliqueEdges r Q)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases hnext : ω (n + 1) with
    | none => simpa only [trajectoryCliques_succ, hnext, Option.toFinset_none, union_empty] using ih
    | some Q =>
      have hQ : Q ∈ remainingCliques r H (trajectoryCliques ω n) := by
        have h := hsupport n
        rw [hnext] at h
        simpa only [historyCliques_prefix] using (step_some_mem_support_iff H _ Q).mp h
      obtain ⟨hQH, hQdis⟩ := mem_remainingCliques.mp hQ
      rw [trajectoryCliques_succ, hnext, Option.toFinset_some, union_singleton]
      refine ⟨insert_subset_iff.mpr ⟨hQH, ih.1⟩, ?_⟩
      intro P hP R hR hne
      rcases mem_insert.mp hP with rfl | hPD
      · rcases mem_insert.mp hR with rfl | hRD
        · exact (hne rfl).elim
        · exact hQdis R hRD
      · rcases mem_insert.mp hR with rfl | hRD
        · exact (hQdis P hPD).symm
        · exact ih.2 hPD hRD hne

theorem trajectory_decomposition (n : ℕ) :
    IsDecomposition (cliqueSupport r (trajectoryCliques ω n)) (trajectoryCliques ω n) :=
  isDecomposition_cliqueSupport_of_pairwise _ (trajectory_packing H ω hsupport n).2

theorem trajectory_card (hqr : r ≤ q) (n : ℕ)
    (havailable : ∀ i < n, (remainingCliques r H (trajectoryCliques ω i)).Nonempty) :
    (trajectoryCliques ω n).card = n := by
  revert havailable
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro havailable
    have hprev := ih (fun i hi => havailable i (by omega))
    have hav : (remainingCliques r H (historyCliques (frestrictLe n ω))).Nonempty := by
      simpa only [historyCliques_prefix] using havailable n (Nat.lt_succ_self n)
    obtain ⟨Q, hnext, hQ⟩ := step_choose_of_nonempty H (frestrictLe n ω) hav _ (hsupport n)
    rw [historyCliques_prefix] at hQ
    have hnew := remainingClique_not_selected hqr hQ
    rw [trajectoryCliques_succ, hnext, Option.toFinset_some, union_singleton,
      card_insert_of_notMem hnew, hprev]

theorem trajectory_leave_card (hqr : r ≤ q) (G : Hypergraph V r)
    (hH : ∀ Q ∈ H, cliqueEdges r Q ⊆ G) (n : ℕ)
    (havailable : ∀ i < n, (remainingCliques r H (trajectoryCliques ω i)).Nonempty) :
    (G \ cliqueSupport r (trajectoryCliques ω n)).card + n * q.choose r = G.card := by
  obtain ⟨hsub, hpair⟩ := trajectory_packing H ω hsupport n
  have hgraph : cliqueSupport r (trajectoryCliques ω n) ⊆ G := by
    intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    exact hH Q (hsub hQ) heQ
  have hcount : (cliqueSupport r (trajectoryCliques ω n)).card = n * q.choose r := by
    rw [cliqueSupport, card_biUnion hpair]
    simp only [card_cliqueEdges, sum_const, nsmul_eq_mul, Nat.cast_id,
      trajectory_card H ω hsupport hqr n havailable]
  rw [← hcount]
  exact card_sdiff_add_card_eq_card hgraph

end Arxiv2411_18291.CliqueRemovalProcess
