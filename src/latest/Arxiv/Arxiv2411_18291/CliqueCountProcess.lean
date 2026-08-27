import Arxiv.Arxiv2411_18291.CliqueCountLossBounds
import Arxiv.Arxiv2411_18291.FrozenEdgeValue

/-!
# The actual number of available cliques as an adapted process

The comparison function continues even after an empty choice. The update
identity therefore holds on every trajectory, without a support assumption.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def cliqueLossStep (r : ℕ) (H : Finset (Block V q)) (i : ℕ)
    (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) : ℝ :=
  (cliqueNeighborhood r (remainingCliques r H (historyCliques h)) Q).card

def cliqueCountIncrement (r : ℕ) (H : Finset (Block V q)) (c : ℕ → ℝ) (i : ℕ)
    (ω : ℕ → State V q) : ℝ :=
  -Option.elim (ω (i + 1)) 0 (cliqueLossStep r H i (frestrictLe i ω)) - (c (i + 1) - c i)

def cliqueCountProcess (r : ℕ) (H : Finset (Block V q)) (c : ℕ → ℝ) (n : ℕ)
    (ω : ℕ → State V q) : ℝ :=
  (remainingCliques r H (trajectoryCliques ω n)).card - c n

theorem cliqueCountIncrement_stronglyMeasurable (H : Finset (Block V q))
    (c : ℕ → ℝ) (i : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) (i + 1)]
      (cliqueCountIncrement r H c i) :=
  FiniteHistoryProcess.stronglyMeasurable_step (S := State V q) i
    (fun h a => -Option.elim a 0 (cliqueLossStep r H i h) - (c (i + 1) - c i))

theorem cliqueCountIncrement_integrable (H : Finset (Block V q)) (c : ℕ → ℝ)
    (i : ℕ) : Integrable (cliqueCountIncrement r H c i) (probability r H) :=
  FiniteHistoryProcess.integrable_step (aborted V q) (step r H) i
    (fun h a => -Option.elim a 0 (cliqueLossStep r H i h) - (c (i + 1) - c i))

theorem cliqueCountProcess_stronglyMeasurable (H : Finset (Block V q))
    (c : ℕ → ℝ) (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) n]
      (cliqueCountProcess r H c n) := by
  have h := FiniteHistoryProcess.stronglyMeasurable_history (S := State V q) n
    (fun h => ((remainingCliques r H (historyCliques h)).card : ℝ) - c n)
  convert h using 1
  funext ω
  simp only [historyCliques_prefix, cliqueCountProcess]

theorem cliqueCountProcess_integrable (H : Finset (Block V q)) (c : ℕ → ℝ)
    (n : ℕ) : Integrable (cliqueCountProcess r H c n) (probability r H) := by
  have h := FiniteHistoryProcess.integrable_history (aborted V q) (step r H) n
    (fun h => ((remainingCliques r H (historyCliques h)).card : ℝ) - c n)
  convert h using 1
  · funext ω
    simp only [historyCliques_prefix, cliqueCountProcess]
  · rfl

theorem cliqueCountProcess_zero (H : Finset (Block V q)) (c : ℕ → ℝ)
    (ω : ℕ → State V q) : cliqueCountProcess r H c 0 ω = (H.card : ℝ) - c 0 := by
  simp [cliqueCountProcess]

theorem cliqueCountProcess_succ (H : Finset (Block V q)) (c : ℕ → ℝ)
    (i : ℕ) (ω : ℕ → State V q) :
    cliqueCountProcess r H c (i + 1) ω =
      cliqueCountProcess r H c i ω + cliqueCountIncrement r H c i ω := by
  cases hω : ω (i + 1) with
  | none =>
    simp only [cliqueCountProcess, trajectoryCliques_succ, hω, Option.toFinset_none,
      union_empty, cliqueCountIncrement, Option.elim_none, neg_zero]
    ring
  | some Q =>
    have h : ((cliqueRemoval r (remainingCliques r H (trajectoryCliques ω i)) Q).card : ℝ) +
        (cliqueNeighborhood r (remainingCliques r H (trajectoryCliques ω i)) Q).card =
        (remainingCliques r H (trajectoryCliques ω i)).card := by
      exact_mod_cast card_cliqueRemoval_add (remainingCliques r H (trajectoryCliques ω i)) Q
    simp only [cliqueCountProcess, remainingCliques_at_succ H ω i Q hω,
      cliqueCountIncrement, hω, Option.elim_some, cliqueLossStep, historyCliques_prefix]
    linarith

theorem cliqueLossStep_nonneg (H : Finset (Block V q)) (i : ℕ)
    (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) :
    0 ≤ cliqueLossStep r H i h Q := Nat.cast_nonneg _

theorem cliqueLossStep_le (H : Finset (Block V q)) (D : ℝ)
    (hd : ∀ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D)
    (i : ℕ) (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) :
    cliqueLossStep r H i h Q ≤ (q.choose r : ℝ) * D :=
  cliqueNeighborhood_card_le_of_degree_bound _ D
    (clique_degree_bound_of_subset (remainingCliques_subset H (historyCliques h)) D hd) Q

theorem cliqueCountIncrement_abs_bound (H : Finset (Block V q)) (D : ℝ) (hD : 0 ≤ D)
    (hd : ∀ e : Block V r, ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤ D)
    (c : ℕ → ℝ) (i : ℕ) (ω : ℕ → State V q) :
    |cliqueCountIncrement r H c i ω| ≤ (q.choose r : ℝ) * D + |c (i + 1) - c i| := by
  cases hω : ω (i + 1) with
  | none =>
    simp only [cliqueCountIncrement, hω, Option.elim_none, neg_zero, zero_sub, abs_neg]
    exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hD)
  | some Q =>
    simp only [cliqueCountIncrement, hω, Option.elim_some]
    have h := abs_sub (-(cliqueLossStep r H i (frestrictLe i ω) Q)) (c (i + 1) - c i)
    rw [abs_neg, abs_of_nonneg (cliqueLossStep_nonneg H i (frestrictLe i ω) Q)] at h
    exact h.trans (add_le_add (cliqueLossStep_le H D hd i (frestrictLe i ω) Q) le_rfl)

end Arxiv2411_18291.CliqueRemovalProcess
