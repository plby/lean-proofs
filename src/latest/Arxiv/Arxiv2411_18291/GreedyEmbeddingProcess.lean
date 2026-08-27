import Arxiv.Arxiv2411_18291.FiniteHistoryConcentration
import Arxiv.Arxiv2411_18291.GreedyProbabilityBudget
import Arxiv.Arxiv2411_18291.PartialEdgeFamily

/-!
# The stopped random greedy embedding process

A state is either an embedding or an abort marker. At each step we inspect
the complete previous history, stop if a degree cap was reached, and
otherwise choose uniformly among the extensions avoiding the initial
forbidden graph and every previously used new edge.
-/

open Finset MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

def EmbeddingState (W V : Type*) := Option (W ↪ V)

def chosenEmbedding {W V : Type*} (f : W ↪ V) : EmbeddingState W V := some f

def abortedEmbedding (W V : Type*) : EmbeddingState W V := none

instance {W V : Type*} [Fintype W] [Fintype V] : Fintype (EmbeddingState W V) := by
  classical
  exact inferInstanceAs (Fintype (Option (W ↪ V)))

instance {W V : Type*} : MeasurableSpace (EmbeddingState W V) := ⊤

instance {W V : Type*} : MeasurableSingletonClass (EmbeddingState W V) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r n : ℕ}

def stateEdge (a : EmbeddingState W V) (e : Block W r) : Option (Block V r) :=
  Option.map (fun f => mapBlock f e) a

def stateFaceIndicator (a : EmbeddingState W V) (e : Block W r) (S : Finset V) : ℝ :=
  edgeIncidence (stateEdge a e) S

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem stateFaceIndicator_bounds (a : EmbeddingState W V) (e : Block W r) (S : Finset V) :
    0 ≤ stateFaceIndicator a e S ∧ stateFaceIndicator a e S ≤ 1 := by
  constructor
  · exact Nat.cast_nonneg _
  · change (edgeIncidence (stateEdge a e) S : ℝ) ≤ 1
    exact_mod_cast edgeIncidence_le_one (stateEdge a e) S

/-- Step indices start at zero; the trajectory's coordinate zero is the initial marker. -/
def historyAt (h : FiniteHistoryProcess.History (EmbeddingState W V) n) (j : ℕ) :
    EmbeddingState W V := if hj : j + 1 ≤ n then h ⟨j + 1, mem_Iic.mpr hj⟩ else abortedEmbedding W V

def historyEdgeGraph (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (e : Block W r) : Hypergraph V r :=
  partialFamilyGraph (range n) fun j => stateEdge (historyAt h j) e

def historyDegree (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (e : Block W r) (S : Finset V) : ℕ :=
  partialFamilyDegree (range n) (fun j => stateEdge (historyAt h j) e) S

def historyForbidden (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1))
    (F : Finset W) (h : FiniteHistoryProcess.History (EmbeddingState W V) n) :
    Hypergraph V (r + 1) := B ∪ (newEdges F H).biUnion (historyEdgeGraph h)

def historySuccessful (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : Prop :=
  ∀ j < n, historyAt h j ≠ abortedEmbedding W V

def historyGood (H : Hypergraph W (r + 1)) (F : Finset W) (L : ℝ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : Prop :=
  ∀ e ∈ newEdges F H, ∀ S : Block V r, (historyDegree h e S.val : ℝ) < L * Fintype.card V

omit [Fintype W] in
theorem historyForbidden_bounded (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1))
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) {θ L : ℝ}
    (hB : IsGraphBounded B θ) (hL : 0 ≤ L) (hgood : historyGood H F L h) :
    IsGraphBounded (historyForbidden H B F h) (θ + H.card * L) := by
  have hd : ∀ e ∈ newEdges F H, ∀ S : Block V r,
      (((historyEdgeGraph h e).filter fun g => S.val ⊆ g.val).card : ℝ) ≤
        L * Fintype.card V := by
    intro e he S
    have hc : (((historyEdgeGraph h e).filter fun g => S.val ⊆ g.val).card : ℝ) ≤
        (historyDegree h e S.val : ℝ) := by
      exact_mod_cast (partialFamilyGraph_degree_le (range n)
        (fun j => stateEdge (historyAt h j) e) S.val)
    exact hc.trans (hgood e he S).le
  have hb := hB.union_biUnion_degree_le (newEdges F H) (historyEdgeGraph h) (fun _ => L) hd
  apply hb.mono
  simp only [sum_const, nsmul_eq_mul]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (by exact_mod_cast card_filter_le H (fun e => ¬ e.val ⊆ F)) hL)

theorem historyLegal_card_half (φ : F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    {θ L : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ) (hL : 0 ≤ L)
    (hn : 4 * (Fintype.card W) ^ 2 ≤ Fintype.card V)
    (hsmall : H.card * (θ + H.card * L) ≤ 1 / 4) (hgood : historyGood H F L h) :
    (1 / 2 : ℝ) * (Fintype.card V : ℝ) ^ (Fintype.card W - F.card) ≤
      (legalExtensions φ H (historyForbidden H B F h)).card :=
  legalExtensions_card_half φ H _ (historyForbidden_bounded H B h hB hL hgood)
    (by positivity) hn hsmall

/-- The stopped process chooses actual legal embeddings, with an absorbing abort marker. -/
def greedyStep (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) (n : ℕ)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : PMF (EmbeddingState W V) := by
  classical
  exact if historySuccessful h ∧ historyGood H F L h then
    if hs : (legalExtensions (Φ n) H (historyForbidden H B F h)).Nonempty then
      (uniformLegalExtension (Φ n) H (historyForbidden H B F h) hs).map
        (fun f => chosenEmbedding f.val)
    else PMF.pure (abortedEmbedding W V)
  else PMF.pure (abortedEmbedding W V)

def greedyProbability (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) : Measure (ℕ → EmbeddingState W V) :=
  FiniteHistoryProcess.probability (abortedEmbedding W V) (greedyStep Φ H B L)

instance greedyProbability_isProbability (Φ : ℕ → F ↪ V) (H : Hypergraph W (r + 1))
    (B : Hypergraph V (r + 1)) (L : ℝ) : IsProbabilityMeasure (greedyProbability Φ H B L) := by
  unfold greedyProbability
  exact FiniteHistoryProcess.probability_isProbability (abortedEmbedding W V)
    (greedyStep Φ H B L)

end Arxiv2411_18291
