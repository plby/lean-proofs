/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 807.
https://www.erdosproblems.com/forum/thread/807

Informal authors:
- Noga Alon
- Tom Bohman
- Hao Huang

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos807.md
-/
import ErdosProblems.Erdos807.Assembly
import ErdosProblems.Erdos807.FinalMoments
import ErdosProblems.Erdos807.Independence
import ErdosProblems.Erdos807.Resolution

/-!
# Erdős Problem 807

The bipartition number of a finite simple graph is the least number of
edge-disjoint complete bipartite graphs whose edge sets partition the graph.
Erdős Problem 807 asked whether, for the uniform random labelled graph
`G(n, 1 / 2)`, this number is asymptotically almost surely `n - α(G)`.

Alon, Bohman, and Huang proved a strictly stronger upper bound.  The final
theorems below formalize their resolution using the exact finite uniform
probability model in `Erdos807.RandomGraph`.
-/

open Filter
open scoped Topology

namespace Erdos807

/-- The original assertion in Erdős Problem 807. -/
def Erdos807Conjecture : Prop :=
  RandomGraph.AlmostSurely (fun n G ↦
    bipartitionNumber G = n - G.indepNum)

/-- The multiplicative Alon--Bohman--Huang improvement for a specified
positive constant. -/
def ABHImprovement (c : ℝ) : Prop :=
  RandomGraph.AlmostSurely (fun n G ↦
    (bipartitionNumber G : ℝ) ≤
      (n : ℝ) - (1 + c) * (G.indepNum : ℝ))

/-- The independence number of a graph on `Fin n` is at most `n`. -/
theorem indepNum_le_order {n : ℕ} (G : SimpleGraph (Fin n)) :
    G.indepNum ≤ n := by
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  rw [← hS.card_eq]
  simpa only [Fintype.card_fin] using Finset.card_le_univ S

/-- Every graph on a nonempty vertex type has a nonempty independent set. -/
theorem indepNum_pos_of_order_pos {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) : 0 < G.indepNum := by
  let v : Fin n := ⟨0, hn⟩
  have hv : G.IsIndepSet ({v} : Finset (Fin n)) := by simp
  have hcard := hv.card_le_indepNum
  simp only [Finset.card_singleton] at hcard
  omega

/-- Eventual positivity of the independence number, in the form needed to
separate the ABH improvement event from the conjectured equality event. -/
theorem eventually_indepNum_pos :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), 0 < G.indepNum := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact fun G ↦ indepNum_pos_of_order_pos (by omega) G

/-- Eventual (indeed pointwise) order bound for the independence number. -/
theorem eventually_indepNum_le_order :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n), G.indepNum ≤ n :=
  Eventually.of_forall fun _n G ↦ indepNum_le_order G

/-- Numerical and probabilistic assembly of the ABH conclusion from the
structured induced-subgraph event.  The second-moment development supplies
the hypothesis of this theorem. -/
theorem alon_bohman_huang_of_structured
    (hstructured : RandomGraph.AlmostSurely (fun n G ↦
      bipartitionNumber G ≤
        n - structuredSize n + blockCount n)) :
    ∃ c : ℝ, 0 < c ∧
      RandomGraph.AlmostSurely (fun n G ↦
        (bipartitionNumber G : ℝ) ≤
            (n : ℝ) - (2 + 2 * c) * Real.logb 2 n ∧
          (bipartitionNumber G : ℝ) ≤
            (n : ℝ) - (1 + c) * (G.indepNum : ℝ)) := by
  refine ⟨1 / 1000, by norm_num, ?_⟩
  have hboth : RandomGraph.AlmostSurely (fun n G ↦
      bipartitionNumber G ≤ n - structuredSize n + blockCount n ∧
        (G.indepNum : ℝ) <
          (2001 / 1000 : ℝ) * ((logParameter n : ℝ) + 1)) :=
    WHP.event_inter RandomGraph.probability
      RandomGraph.probability_nonneg
      (fun h ↦ RandomGraph.probability_mono h)
      RandomGraph.probability_compl
      RandomGraph.probability_union_le hstructured
      indepNum_lt_two_point_zero_zero_one_logParameter_almostSurely
  apply hboth.mono
  filter_upwards [eventually_structuredSize_le, eventually_saving_bound] with
    n hk hsaving
  intro G hG
  refine ⟨?_, ?_⟩
  · exact abh_log_inequality_of_structured hk hsaving hG.1
      (logb_lt_logParameter_add_one n)
  · exact abh_inequality_of_structured_and_independence
      hk hsaving hG.1 hG.2

/-- The original conjecture fails once the structured witness is known to
exist with high probability. -/
theorem erdos_807_of_structured
    (hstructured : RandomGraph.AlmostSurely (fun n G ↦
      bipartitionNumber G ≤
        n - structuredSize n + blockCount n)) :
    ¬ Erdos807Conjecture := by
  obtain ⟨c, hc, hABH⟩ := alon_bohman_huang_of_structured hstructured
  have himprovement : ABHImprovement c :=
    hABH.mono (Eventually.of_forall fun _n _G hG ↦ hG.2)
  exact not_almostSurely_nat_sub_equality_of_improvement
    (fun _n G ↦ bipartitionNumber G)
    (fun _n G ↦ G.indepNum) hc
    eventually_indepNum_pos eventually_indepNum_le_order himprovement

/-- The stable-slot second-moment construction yields the required saving in
the bipartition number with high probability. -/
theorem structured_bipartition_bound_almostSurely :
    RandomGraph.AlmostSurely (fun n G ↦
      bipartitionNumber G ≤
        n - structuredSize n + blockCount n) := by
  apply FinalMoments.almostSurely_positive_host_witnessCount.mono
  exact Eventually.of_forall fun n G hpos ↦ by
    have h := HostFamily.bipartitionNumber_le_of_witnessCount_pos hpos
    simpa [HostFamily.templateOrder, structuredSize_eq_mul_blockCount] using h

/-- Alon--Bohman--Huang's full-sequence resolution, with the explicit
formalization constant `c = 1 / 1000`. -/
theorem alon_bohman_huang :
    ∃ c : ℝ, 0 < c ∧
      RandomGraph.AlmostSurely (fun n G ↦
        (bipartitionNumber G : ℝ) ≤
            (n : ℝ) - (2 + 2 * c) * Real.logb 2 n ∧
          (bipartitionNumber G : ℝ) ≤
            (n : ℝ) - (1 + c) * (G.indepNum : ℝ)) :=
  alon_bohman_huang_of_structured structured_bipartition_bound_almostSurely

/-- Erdős Problem 807 has a negative answer: the proposed equality does not
hold with high probability in `G(n, 1 / 2)`. -/
theorem erdos_807 : ¬ Erdos807Conjecture :=
  erdos_807_of_structured structured_bipartition_bound_almostSurely

end Erdos807

#print axioms Erdos807.alon_bohman_huang
#print axioms Erdos807.erdos_807
