import Arxiv.Arxiv2411_18291.FaceLossDrift
import Arxiv.Arxiv2411_18291.CliqueCountConditionalDrift

/-! # The adapted face-degree process and its exact increments -/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem trajectory_graph_succ (G : Hypergraph V r) (ω : ℕ → State V q) (i : ℕ)
    (Q : Block V q) (hQ : ω (i + 1) = some Q) :
    G \ cliqueSupport r (trajectoryCliques ω (i + 1)) =
      (G \ cliqueSupport r (trajectoryCliques ω i)) \ cliqueEdges r Q := by
  simp only [trajectoryCliques_succ, hQ, Option.toFinset_some, cliqueSupport]
  ext e
  simp only [mem_sdiff, mem_biUnion, mem_union, mem_singleton]
  simp only [or_and_right, exists_or, exists_eq_left]
  simp only [not_or, and_assoc]

def faceLossStep (G : Hypergraph V (r + 1)) (f : Block V r) (i : ℕ)
    (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) : ℝ :=
  cliqueFaceLoss (G \ cliqueSupport (r + 1) (historyCliques h)) f Q

def faceCountIncrement (G : Hypergraph V (r + 1)) (f : Block V r) (c : ℕ → ℝ) (i : ℕ)
    (ω : ℕ → State V q) : ℝ :=
  -Option.elim (ω (i + 1)) 0 (faceLossStep G f i (frestrictLe i ω)) - (c (i + 1) - c i)

def faceCountProcess (G : Hypergraph V (r + 1)) (f : Block V r) (c : ℕ → ℝ) (n : ℕ)
    (ω : ℕ → State V q) : ℝ :=
  ((G \ cliqueSupport (r + 1) (trajectoryCliques ω n)).filter fun e => f.val ⊆ e.val).card - c n

theorem faceCountIncrement_stronglyMeasurable (G : Hypergraph V (r + 1)) (f : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) (i + 1)]
      (faceCountIncrement G f c i) :=
  FiniteHistoryProcess.stronglyMeasurable_step (S := State V q) i
    (fun h a => -Option.elim a 0 (faceLossStep G f i h) - (c (i + 1) - c i))

theorem faceCountIncrement_integrable (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (f : Block V r) (c : ℕ → ℝ) (i : ℕ) :
    Integrable (faceCountIncrement G f c i) (probability (r + 1) H) :=
  FiniteHistoryProcess.integrable_step (aborted V q) (step (r + 1) H) i
    (fun h a => -Option.elim a 0 (faceLossStep G f i h) - (c (i + 1) - c i))

theorem faceCountProcess_stronglyMeasurable (G : Hypergraph V (r + 1)) (f : Block V r)
    (c : ℕ → ℝ) (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) n]
      (faceCountProcess G f c n) := by
  have h := FiniteHistoryProcess.stronglyMeasurable_history (S := State V q) n
    (fun h => (((G \ cliqueSupport (r + 1) (historyCliques h)).filter
      fun e => f.val ⊆ e.val).card : ℝ) - c n)
  convert h using 1
  funext ω
  simp only [historyCliques_prefix, faceCountProcess]

theorem faceCountProcess_integrable (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (f : Block V r) (c : ℕ → ℝ) (n : ℕ) :
    Integrable (faceCountProcess G f c n) (probability (r + 1) H) := by
  have h := FiniteHistoryProcess.integrable_history (aborted V q) (step (r + 1) H) n
    (fun h => (((G \ cliqueSupport (r + 1) (historyCliques h)).filter
      fun e => f.val ⊆ e.val).card : ℝ) - c n)
  convert h using 1
  · funext ω
    simp only [historyCliques_prefix, faceCountProcess]
  · rfl

theorem faceCountProcess_zero (G : Hypergraph V (r + 1)) (f : Block V r) (c : ℕ → ℝ)
    (ω : ℕ → State V q) :
    faceCountProcess G f c 0 ω = ((G.filter fun e => f.val ⊆ e.val).card : ℝ) - c 0 := by
  simp [faceCountProcess, cliqueSupport]

theorem faceCountProcess_succ (G : Hypergraph V (r + 1)) (f : Block V r) (c : ℕ → ℝ)
    (i : ℕ) (ω : ℕ → State V q) :
    faceCountProcess G f c (i + 1) ω =
      faceCountProcess G f c i ω + faceCountIncrement G f c i ω := by
  cases hω : ω (i + 1) with
  | none =>
    simp only [faceCountProcess, trajectoryCliques_succ, hω, Option.toFinset_none,
      union_empty, faceCountIncrement, Option.elim_none, neg_zero]
    ring
  | some Q =>
    let E := G \ cliqueSupport (r + 1) (trajectoryCliques ω i)
    have h : (((E \ cliqueEdges (r + 1) Q).filter fun e => f.val ⊆ e.val).card : ℝ) +
        cliqueFaceLoss E f Q = (E.filter fun e => f.val ⊆ e.val).card := by
      exact_mod_cast face_degree_remove_clique E f Q
    simp only [faceCountProcess, trajectory_graph_succ G ω i Q hω,
      faceCountIncrement, hω, Option.elim_some, faceLossStep, historyCliques_prefix]
    dsimp only [E] at h
    linarith only [h]

theorem faceLossStep_nonneg (G : Hypergraph V (r + 1)) (f : Block V r) (i : ℕ)
    (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) :
    0 ≤ faceLossStep G f i h Q := Nat.cast_nonneg _

theorem faceLossStep_le (G : Hypergraph V (r + 1)) (f : Block V r) (i : ℕ)
    (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) :
    faceLossStep G f i h Q ≤ (q - r : ℕ) := by
  unfold faceLossStep
  exact_mod_cast cliqueFaceLoss_le (G \ cliqueSupport (r + 1) (historyCliques h)) f Q

theorem faceCountIncrement_abs_bound (G : Hypergraph V (r + 1)) (f : Block V r)
    (c : ℕ → ℝ) (i : ℕ) (ω : ℕ → State V q) :
    |faceCountIncrement G f c i ω| ≤ ((q - r : ℕ) : ℝ) + |c (i + 1) - c i| := by
  cases hω : ω (i + 1) with
  | none =>
    simp only [faceCountIncrement, hω, Option.elim_none, neg_zero, zero_sub, abs_neg]
    exact le_add_of_nonneg_left (Nat.cast_nonneg _)
  | some Q =>
    simp only [faceCountIncrement, hω, Option.elim_some]
    have h := abs_sub (-(faceLossStep G f i (frestrictLe i ω) Q)) (c (i + 1) - c i)
    rw [abs_neg, abs_of_nonneg (faceLossStep_nonneg G f i (frestrictLe i ω) Q)] at h
    exact h.trans (add_le_add (faceLossStep_le G f i (frestrictLe i ω) Q) le_rfl)

end Arxiv2411_18291.CliqueRemovalProcess
