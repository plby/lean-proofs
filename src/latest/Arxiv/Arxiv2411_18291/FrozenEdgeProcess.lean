import Arxiv.Arxiv2411_18291.FrozenTrackingIncrement
import Arxiv.Arxiv2411_18291.UniformCliqueStep
import Arxiv.Arxiv2411_18291.FiniteHistoryMeasurability

/-!
# The adapted edge-degree process frozen on removal

Its increments stop both the degree and the deterministic comparison
when the edge is removed. The construction is defined on every trajectory,
and all adaptation, integrability, and one-step bounds are proved.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def edgeStepValue (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ) (i : ℕ)
    (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) : ℝ :=
  if e ∈ cliqueSupport r (historyCliques h) then 0 else
    frozenTrackingIncrement (remainingCliques r H (historyCliques h)) e (c (i + 1) - c i) Q

def edgeIncrement (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ) (i : ℕ)
    (ω : ℕ → State V q) : ℝ :=
  Option.elim (ω (i + 1)) 0 (edgeStepValue H e c i (frestrictLe i ω))

def frozenEdgeProcess (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ)
    (n : ℕ) (ω : ℕ → State V q) : ℝ :=
  ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - c 0 + ∑ i ∈ range n, edgeIncrement H e c i ω

theorem edgeIncrement_stronglyMeasurable (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) (i + 1)]
      (edgeIncrement H e c i) :=
  FiniteHistoryProcess.stronglyMeasurable_step (S := State V q) i
    (fun h a => Option.elim a 0 (edgeStepValue H e c i h))

theorem edgeIncrement_integrable (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ)
    (i : ℕ) : Integrable (edgeIncrement H e c i) (probability r H) :=
  FiniteHistoryProcess.integrable_step (aborted V q) (step r H) i
    (fun h a => Option.elim a 0 (edgeStepValue H e c i h))

theorem frozenEdgeProcess_stronglyMeasurable (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (n : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) n]
      (frozenEdgeProcess H e c n) := by
  have hs : StronglyMeasurable[Filtration.piLE (X := fun _ => State V q) n]
      (∑ i ∈ range n, edgeIncrement H e c i) := by
    apply Finset.stronglyMeasurable_sum
    intro i hi
    exact (edgeIncrement_stronglyMeasurable H e c i).mono
      (Filtration.piLE.mono (by have h := mem_range.mp hi; omega))
  have h := (stronglyMeasurable_const (b :=
    ((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - c 0)).add hs
  convert h using 1
  funext ω
  simp only [frozenEdgeProcess, Pi.add_apply, Finset.sum_apply]

theorem frozenEdgeProcess_integrable (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (n : ℕ) : Integrable (frozenEdgeProcess H e c n) (probability r H) := by
  have hs : Integrable (fun ω => ∑ i ∈ range n, edgeIncrement H e c i ω) (probability r H) :=
    integrable_finsetSum (range n) (fun i _ => edgeIncrement_integrable H e c i)
  exact (integrable_const (((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - c 0)).add hs

theorem frozenEdgeProcess_succ (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ)
    (n : ℕ) (ω : ℕ → State V q) :
    frozenEdgeProcess H e c (n + 1) ω = frozenEdgeProcess H e c n ω + edgeIncrement H e c n ω := by
  simp only [frozenEdgeProcess, sum_range_succ, add_assoc]

theorem edgeStepValue_abs_bound (hqr : r < q) (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) (h : FiniteHistoryProcess.History (State V q) i) (Q : Block V q) :
    |edgeStepValue H e c i h Q| ≤
      (q.choose r : ℝ) * (Fintype.card V : ℝ) ^ (q - r - 1) + |c (i + 1) - c i| := by
  unfold edgeStepValue
  split_ifs
  · simp only [abs_zero]
    positivity
  · exact frozenTrackingIncrement_abs_bound hqr _ e _ Q

theorem edgeIncrement_abs_bound (hqr : r < q) (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) (ω : ℕ → State V q) :
    |edgeIncrement H e c i ω| ≤
      (q.choose r : ℝ) * (Fintype.card V : ℝ) ^ (q - r - 1) + |c (i + 1) - c i| := by
  cases hω : ω (i + 1) with
  | none =>
    simp only [edgeIncrement, hω, Option.elim_none, abs_zero]
    positivity
  | some Q =>
    simpa only [edgeIncrement, hω, Option.elim_some] using
      edgeStepValue_abs_bound hqr H e c i (frestrictLe i ω) Q

theorem edgeIncrement_of_removed (H : Finset (Block V q)) (e : Block V r) (c : ℕ → ℝ)
    (i : ℕ) (ω : ℕ → State V q) (he : e ∈ cliqueSupport r (trajectoryCliques ω i)) :
    edgeIncrement H e c i ω = 0 := by
  cases hω : ω (i + 1) <;>
    simp [edgeIncrement, hω, edgeStepValue, historyCliques_prefix, he]

theorem frozenEdgeProcess_succ_of_removed (H : Finset (Block V q)) (e : Block V r)
    (c : ℕ → ℝ) (i : ℕ) (ω : ℕ → State V q)
    (he : e ∈ cliqueSupport r (trajectoryCliques ω i)) :
    frozenEdgeProcess H e c (i + 1) ω = frozenEdgeProcess H e c i ω := by
  rw [frozenEdgeProcess_succ, edgeIncrement_of_removed H e c i ω he, add_zero]

end Arxiv2411_18291.CliqueRemovalProcess
