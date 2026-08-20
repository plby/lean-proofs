import ErdosProblems.Erdos746.Model
import ErdosProblems.Erdos746.RandomOrdering
import ErdosProblems.Erdos746.Adaptive
import ErdosProblems.Erdos746.Posa
import ErdosProblems.Erdos746.PosaAlternative

/-!
# Sprinkling in the uniform random-graph process

This file connects the finite adaptive estimate in `Adaptive` with the graph
process.  Starting from a fixed set of edges, a history records distinct
edges drawn uniformly without replacement from its complement.  Before the
graph becomes Hamiltonian, a successful draw is a Posa booster of the current
graph; after it becomes Hamiltonian every draw is declared successful.  This
last convention makes the conditional success lower bound valid at every
history and does not alter the Hamiltonicity failure event.
-/

open scoped BigOperators
open Erdos746.PathMax

namespace Erdos746

noncomputable section

/-- Potential edges still available after fixing the base graph. -/
def sprinklingAmbient {n : ℕ} (base : Finset (Edge n)) : Finset (Edge n) :=
  Finset.univ \ base

/-- The graph consisting of the base edges and all edges in a history. -/
def graphAfterHistory {n : ℕ} (base : Finset (Edge n))
    (h : List (Edge n)) : SimpleGraph (Fin n) :=
  graphOfEdges (base ∪ h.toFinset)

/-- Boosters of a graph, represented in the complete-graph edge subtype. -/
def edgeBoostersOfGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Edge n) :=
  by
    classical
    exact Finset.univ.filter fun e ↦
      PathMax.IsBooster G (edgeEmbedding n e)

@[simp]
theorem mem_edgeBoostersOfGraph {n : ℕ} {G : SimpleGraph (Fin n)}
    {e : Edge n} :
    e ∈ edgeBoostersOfGraph G ↔ PathMax.IsBooster G (edgeEmbedding n e) := by
  classical
  simp [edgeBoostersOfGraph]

/-- Boosters of the graph at a history, represented in the `Edge n` subtype. -/
def edgeBoostersAt {n : ℕ} (base : Finset (Edge n))
    (h : List (Edge n)) : Finset (Edge n) :=
  edgeBoostersOfGraph (graphAfterHistory base h)

/-- Adaptive successes in the graph process.  Once Hamiltonicity has already
been reached, every remaining edge is counted as a success. -/
def graphProcessBoosters {n : ℕ} (base : Finset (Edge n))
    (h : List (Edge n)) : Finset (Edge n) :=
  by
    classical
    exact if (graphAfterHistory base h).IsHamiltonian then Finset.univ
      else edgeBoostersAt base h

@[simp]
theorem graphAfterHistory_nil {n : ℕ} (base : Finset (Edge n)) :
    graphAfterHistory base [] = graphOfEdges base := by
  simp [graphAfterHistory]

theorem graphOfEdges_le_graphAfterHistory {n : ℕ}
    (base : Finset (Edge n)) (h : List (Edge n)) :
    graphOfEdges base ≤ graphAfterHistory base h := by
  exact graphOfEdges_mono Finset.subset_union_left

theorem mem_edgeSet_graphOfEdges_iff {n : ℕ} (s : Finset (Edge n))
    (e : Edge n) :
    edgeEmbedding n e ∈ (graphOfEdges s).edgeSet ↔ e ∈ s := by
  rw [edgeSet_graphOfEdges]
  simp [edgeEmbedding]

/-- Every booster of the current graph is a genuinely unrevealed edge. -/
theorem edgeBoostersAt_subset_remaining {n : ℕ}
    (base : Finset (Edge n)) (h : List (Edge n)) :
    edgeBoostersAt base h ⊆ remaining (sprinklingAmbient base) h := by
  intro e he
  have hboost :
      PathMax.IsBooster (graphAfterHistory base h) (edgeEmbedding n e) := by
    exact mem_edgeBoostersOfGraph.mp (by simpa [edgeBoostersAt] using he)
  have hmissing : edgeEmbedding n e ∉ (graphAfterHistory base h).edgeSet :=
    hboost.not_mem
  have hnot : e ∉ base ∪ h.toFinset := by
    simpa [graphAfterHistory, mem_edgeSet_graphOfEdges_iff] using hmissing
  have hnotBase : e ∉ base := fun he ↦ hnot (Finset.mem_union_left _ he)
  have hnotHistory : e ∉ h.toFinset := fun he ↦ hnot (Finset.mem_union_right _ he)
  rw [mem_remaining_iff]
  constructor
  · simp [sprinklingAmbient, hnotBase]
  · simpa using hnotHistory

theorem available_graphProcessBoosters_of_not_hamiltonian {n : ℕ}
    (base : Finset (Edge n)) (h : List (Edge n))
    (hham : ¬ (graphAfterHistory base h).IsHamiltonian) :
    availableBoosters (sprinklingAmbient base) (graphProcessBoosters base) h =
      edgeBoostersAt base h := by
  classical
  rw [availableBoosters, graphProcessBoosters, if_neg hham]
  exact Finset.inter_eq_right.mpr (edgeBoostersAt_subset_remaining base h)

theorem available_graphProcessBoosters_of_hamiltonian {n : ℕ}
    (base : Finset (Edge n)) (h : List (Edge n))
    (hham : (graphAfterHistory base h).IsHamiltonian) :
    availableBoosters (sprinklingAmbient base) (graphProcessBoosters base) h =
      remaining (sprinklingAmbient base) h := by
  classical
  rw [availableBoosters, graphProcessBoosters, if_pos hham]
  exact Finset.inter_eq_left.mpr (Finset.subset_univ _)

/-- Two-expansion is preserved when edges are added. -/
theorem isTwoExpanderUpTo_mono_sprinkling
    {V : Type*} [Fintype V] [DecidableEq V]
    {G H : SimpleGraph V} {k : ℕ} (hGH : G ≤ H)
    (hG : G.IsTwoExpanderUpTo k) : H.IsTwoExpanderUpTo k := by
  intro S hS
  refine (hG S hS).trans (Finset.card_le_card ?_)
  intro v hv
  rw [SimpleGraph.mem_outerNeighborFinset] at hv ⊢
  obtain ⟨hvS, u, huS, huv⟩ := hv
  exact ⟨hvS, u, huS, hGH huv⟩

theorem graphAfterHistory_connected {n : ℕ} {base : Finset (Edge n)}
    (hbase : (graphOfEdges base).Connected) (h : List (Edge n)) :
    (graphAfterHistory base h).Connected :=
  hbase.mono (graphOfEdges_le_graphAfterHistory base h)

theorem graphAfterHistory_twoExpander {n k : ℕ}
    {base : Finset (Edge n)}
    (hbase : (graphOfEdges base).IsTwoExpanderUpTo k)
    (h : List (Edge n)) :
    (graphAfterHistory base h).IsTwoExpanderUpTo k :=
  isTwoExpanderUpTo_mono_sprinkling
    (graphOfEdges_le_graphAfterHistory base h) hbase

@[simp]
theorem graphAfterHistory_append_singleton {n : ℕ}
    (base : Finset (Edge n)) (h : List (Edge n)) (e : Edge n) :
    graphAfterHistory base (h ++ [e]) =
      PathMax.addEdge (graphAfterHistory base h) (edgeEmbedding n e) := by
  apply SimpleGraph.edgeSet_injective
  have he : ¬(edgeEmbedding n e).IsDiag := by
    simpa [edgeEmbedding] using
      ((⊤ : SimpleGraph (Fin n)).not_isDiag_of_mem_edgeFinset e.property)
  rw [PathMax.edgeSet_addEdge_of_not_isDiag he]
  simp [graphAfterHistory, edgeSet_graphOfEdges, Finset.map_union]

/-- Number of adaptive booster hits in a chronological continuation, starting
after a fixed history. -/
def graphProcessHitCountFrom {n : ℕ} (base : Finset (Edge n))
    (hist : List (Edge n)) : List (Edge n) → ℕ
  | [] => 0
  | e :: tail =>
      (if e ∈ graphProcessBoosters base hist then 1 else 0) +
        graphProcessHitCountFrom base (hist ++ [e]) tail

@[simp]
theorem graphProcessHitCountFrom_nil {n : ℕ}
    (base : Finset (Edge n)) (hist : List (Edge n)) :
    graphProcessHitCountFrom base hist [] = 0 := rfl

@[simp]
theorem graphProcessHitCountFrom_cons {n : ℕ}
    (base : Finset (Edge n)) (hist : List (Edge n))
    (e : Edge n) (tail : List (Edge n)) :
    graphProcessHitCountFrom base hist (e :: tail) =
      (if e ∈ graphProcessBoosters base hist then 1 else 0) +
        graphProcessHitCountFrom base (hist ++ [e]) tail := rfl

/-- If a completed continuation is still non-Hamiltonian, every hit was a
genuine Pósa booster and hence paid for a strict increase of maximum path
length. -/
theorem graphProcessHitCountFrom_add_maxPathLength_le
    {n : ℕ} (base : Finset (Edge n)) (hist tail : List (Edge n))
    (hfinal : ¬(graphAfterHistory base (hist ++ tail)).IsHamiltonian) :
    graphProcessHitCountFrom base hist tail +
        PathMax.maxPathLength (graphAfterHistory base hist) ≤
      PathMax.maxPathLength (graphAfterHistory base (hist ++ tail)) := by
  induction tail generalizing hist with
  | nil => simp
  | cons e tail ih =>
      have hnextFinal :
          ¬(graphAfterHistory base ((hist ++ [e]) ++ tail)).IsHamiltonian := by
        simpa [List.append_assoc] using hfinal
      have hih := ih (hist := hist ++ [e]) hnextFinal
      by_cases hhit : e ∈ graphProcessBoosters base hist
      · have hcurrent : ¬(graphAfterHistory base hist).IsHamiltonian := by
          intro hham
          apply hfinal
          exact hham.mono (graphOfEdges_mono (by
            intro x hx
            simp only [Finset.mem_union, List.mem_toFinset, List.mem_append,
              List.mem_cons] at hx ⊢
            tauto))
        have hboost :
            PathMax.IsBooster (graphAfterHistory base hist)
              (edgeEmbedding n e) := by
          rw [graphProcessBoosters, if_neg hcurrent] at hhit
          exact mem_edgeBoostersOfGraph.mp (by simpa [edgeBoostersAt] using hhit)
        have hnext : ¬(graphAfterHistory base (hist ++ [e])).IsHamiltonian := by
          intro hham
          apply hnextFinal
          exact hham.mono (graphOfEdges_mono (by
            intro x hx
            simp only [Finset.mem_union, List.mem_toFinset, List.mem_append,
              List.mem_cons] at hx ⊢
            tauto))
        have hstrict :
            PathMax.maxPathLength (graphAfterHistory base hist) <
              PathMax.maxPathLength (graphAfterHistory base (hist ++ [e])) := by
          rw [graphAfterHistory_append_singleton] at hnext ⊢
          exact hboost.hamiltonian_or_length_lt.resolve_left hnext
        simp only [graphProcessHitCountFrom_cons, if_pos hhit]
        simp only [List.append_assoc, List.singleton_append] at hih
        omega
      · have hmono :
            PathMax.maxPathLength (graphAfterHistory base hist) ≤
              PathMax.maxPathLength (graphAfterHistory base (hist ++ [e])) := by
          apply PathMax.maxPathLength_mono
          exact graphOfEdges_mono (by
            intro x hx
            simp only [Finset.mem_union, List.mem_toFinset, List.mem_append,
              List.mem_cons] at hx ⊢
            tauto)
        simp only [graphProcessHitCountFrom_cons, if_neg hhit, zero_add]
        simp only [List.append_assoc, List.singleton_append] at hih
        omega

/-- A non-Hamiltonian completed continuation contains at most `n-1` adaptive
booster hits. -/
theorem graphProcessHitCountFrom_le_pred {n : ℕ}
    (base : Finset (Edge n)) (hist tail : List (Edge n))
    (hfinal : ¬(graphAfterHistory base (hist ++ tail)).IsHamiltonian) :
    graphProcessHitCountFrom base hist tail ≤ n - 1 := by
  have hmain := graphProcessHitCountFrom_add_maxPathLength_le
    base hist tail hfinal
  by_cases hn0 : n = 0
  · have hbound := PathMax.maxPathLength_le_card
      (graphAfterHistory base (hist ++ tail))
    simp only [Fintype.card_fin, hn0] at hbound ⊢
    omega
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn0)
    have hbound := PathMax.maxPathLength_lt_card
      (graphAfterHistory base (hist ++ tail))
    simp only [Fintype.card_fin] at hbound
    omega

/-- Pósa's square booster bound, at expansion radius `n/4`, supplies the
uniform `1/16` proportion needed in the random graph process. -/
theorem one_sixteenth_edgeCount_le_boosters {n : ℕ}
    (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hconnected : G.Connected)
    (hexpander : G.IsTwoExpanderUpTo (n / 4))
    (hnotHam : ¬G.IsHamiltonian) :
    (1 / 16 : ℝ) * (edgeCount n : ℝ) ≤
      ((edgeBoostersOfGraph G).card : ℝ) := by
  have hk : 1 ≤ n / 4 := by omega
  have hposa := PosaAlternative.posa_boosterEdgeFinset_bound
    hconnected hnotHam hk hexpander
  have heq : edgeBoostersOfGraph G = PathMax.boosterEdgeFinset G := by
    ext e
    simp only [mem_edgeBoostersOfGraph, PathMax.mem_boosterEdgeFinset]
    rfl
  have hfloorNat : n ≤ 4 * (n / 4 + 1) := by omega
  have hfloorReal : (n : ℝ) / 4 ≤ (n / 4 + 1 : ℕ) := by
    have hcast : (n : ℝ) ≤ 4 * (n / 4 + 1 : ℕ) := by
      exact_mod_cast hfloorNat
    nlinarith
  have hchoose : (edgeCount n : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    rw [edgeCount, Nat.cast_choose_two]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hpred : (n : ℝ) - 1 ≤ n := by linarith
    nlinarith
  have hposaReal :
      ((n / 4 + 1 : ℕ) : ℝ) ^ 2 ≤
        2 * ((edgeBoostersOfGraph G).card : ℝ) := by
    rw [heq]
    exact_mod_cast hposa
  have hmul :
      0 ≤ ((((n / 4 + 1 : ℕ) : ℝ) - (n : ℝ) / 4) *
        (((n / 4 + 1 : ℕ) : ℝ) + (n : ℝ) / 4)) :=
    mul_nonneg (sub_nonneg.mpr hfloorReal) (by positivity)
  have hsquare :
      ((n : ℝ) / 4) ^ 2 ≤ ((n / 4 + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  nlinarith [hsquare]

/-- Conditional booster proportion in every history of a connected
quarter-two-expanding base graph. -/
theorem graphProcess_booster_proportion_one_sixteenth {n : ℕ}
    (hn : 8 ≤ n) (base : Finset (Edge n))
    (hconnected : (graphOfEdges base).Connected)
    (hexpander : (graphOfEdges base).IsTwoExpanderUpTo (n / 4)) :
    ∀ h, AdmissibleHistory (sprinklingAmbient base) h →
      h.length < (sprinklingAmbient base).card →
      (1 / 16 : ℝ) * ((remaining (sprinklingAmbient base) h).card : ℝ) ≤
        ((availableBoosters (sprinklingAmbient base)
          (graphProcessBoosters base) h).card : ℝ) := by
  intro h _hadmissible _hlength
  by_cases hham : (graphAfterHistory base h).IsHamiltonian
  · rw [available_graphProcessBoosters_of_hamiltonian base h hham]
    exact mul_le_of_le_one_left (by positivity) (by norm_num)
  · rw [available_graphProcessBoosters_of_not_hamiltonian base h hham]
    have hremaining :
        (remaining (sprinklingAmbient base) h).card ≤ edgeCount n := by
      calc
        (remaining (sprinklingAmbient base) h).card ≤
            (Finset.univ : Finset (Edge n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card (Edge n) := Finset.card_univ
        _ = edgeCount n := card_edge n
    have hscaled :
        (1 / 16 : ℝ) *
            ((remaining (sprinklingAmbient base) h).card : ℝ) ≤
          (1 / 16 : ℝ) * (edgeCount n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact_mod_cast hremaining
    exact hscaled.trans (one_sixteenth_edgeCount_le_boosters hn
      (graphAfterHistory base h)
      (graphAfterHistory_connected hconnected h)
      (graphAfterHistory_twoExpander hexpander h) hham)

/-- Exponential lower-tail bound with the exact Pósa proportion. -/
theorem graphProcessLowerTailMass_one_sixteenth {n R : ℕ}
    (hn : 8 ≤ n) (base : Finset (Edge n))
    (hconnected : (graphOfEdges base).Connected)
    (hexpander : (graphOfEdges base).IsTwoExpanderUpTo (n / 4))
    (hR : R ≤ (sprinklingAmbient base).card) :
    uniformBoosterLowerTailMass (sprinklingAmbient base)
        (graphProcessBoosters base) [] R (n - 1) ≤
      Real.exp ((n - 1 : ℕ) -
        (1 / 16 : ℝ) * (R : ℝ) * (1 - Real.exp (-1))) := by
  have hh : SamplingHorizon (sprinklingAmbient base) [] R := by
    constructor
    · simp [AdmissibleHistory]
    · simpa using hR
  simpa using
    (uniformBoosterLowerTailMass_le_exp_one_sixteenth
      (sprinklingAmbient base) (graphProcessBoosters base)
      (θ := (1 : ℝ)) (by norm_num)
      (graphProcess_booster_proportion_one_sixteenth hn base
        hconnected hexpander) hh)

/-- A uniform lower bound on the number of boosters in every relevant
non-Hamiltonian supergraph yields the conditional booster-proportion bound
needed by the adaptive MGF argument. -/
theorem graphProcess_booster_proportion {n k b : ℕ} {q : ℝ}
    (base : Finset (Edge n))
    (hqnonneg : 0 ≤ q) (hqone : q ≤ 1)
    (hqb : q * (edgeCount n : ℝ) ≤ (b : ℝ))
    (hconnected : (graphOfEdges base).Connected)
    (hexpander : (graphOfEdges base).IsTwoExpanderUpTo k)
    (hboosters : ∀ G : SimpleGraph (Fin n),
      graphOfEdges base ≤ G → G.Connected → G.IsTwoExpanderUpTo k →
      ¬ G.IsHamiltonian →
      b ≤ (edgeBoostersOfGraph G).card) :
    ∀ h, AdmissibleHistory (sprinklingAmbient base) h →
      h.length < (sprinklingAmbient base).card →
      q * ((remaining (sprinklingAmbient base) h).card : ℝ) ≤
        ((availableBoosters (sprinklingAmbient base)
          (graphProcessBoosters base) h).card : ℝ) := by
  intro h _hadmissible _hlength
  by_cases hham : (graphAfterHistory base h).IsHamiltonian
  · rw [available_graphProcessBoosters_of_hamiltonian base h hham]
    exact mul_le_of_le_one_left (by positivity) hqone
  · rw [available_graphProcessBoosters_of_not_hamiltonian base h hham]
    have hremaining :
        (remaining (sprinklingAmbient base) h).card ≤ edgeCount n := by
      calc
        (remaining (sprinklingAmbient base) h).card ≤
            (Finset.univ : Finset (Edge n)).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = Fintype.card (Edge n) := Finset.card_univ
        _ = edgeCount n := card_edge n
    have hqremaining :
        q * ((remaining (sprinklingAmbient base) h).card : ℝ) ≤
          q * (edgeCount n : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hqnonneg
      exact_mod_cast hremaining
    have hcard : b ≤ (edgeBoostersAt base h).card := by
      simpa [edgeBoostersAt] using hboosters (graphAfterHistory base h)
        (graphOfEdges_le_graphAfterHistory base h)
        (graphAfterHistory_connected hconnected h)
        (graphAfterHistory_twoExpander hexpander h) hham
    exact hqremaining.trans (hqb.trans (by exact_mod_cast hcard))

/-- **Finite graph-process sprinkling bound.**

Condition on any connected `k`-two-expanding base graph.  If every
non-Hamiltonian supergraph retaining those properties has at least `b`
boosters, and `q * |E(K_n)| ≤ b`, then the exact uniform-without-replacement
mass of histories with at most `r` successful booster steps is bounded by
the adaptive lower-tail exponential estimate. -/
theorem graphProcessLowerTailMass_le_exp {n k b R r : ℕ} {q : ℝ}
    (base : Finset (Edge n))
    (hqnonneg : 0 ≤ q) (hqone : q ≤ 1)
    (hqb : q * (edgeCount n : ℝ) ≤ (b : ℝ))
    (hconnected : (graphOfEdges base).Connected)
    (hexpander : (graphOfEdges base).IsTwoExpanderUpTo k)
    (hboosters : ∀ G : SimpleGraph (Fin n),
      graphOfEdges base ≤ G → G.Connected → G.IsTwoExpanderUpTo k →
      ¬ G.IsHamiltonian →
      b ≤ (edgeBoostersOfGraph G).card)
    (hR : R ≤ (sprinklingAmbient base).card) :
    uniformBoosterLowerTailMass (sprinklingAmbient base)
        (graphProcessBoosters base) [] R r ≤
      Real.exp ((r : ℝ) - q * (R : ℝ) * (1 - Real.exp (-1))) := by
  have hh : SamplingHorizon (sprinklingAmbient base) [] R := by
    constructor
    · simp [AdmissibleHistory]
    · simpa using hR
  have hp := graphProcess_booster_proportion base hqnonneg hqone hqb
    hconnected hexpander hboosters
  simpa using
    (uniformBoosterLowerTailMass_le_exp (sprinklingAmbient base)
      (graphProcessBoosters base) (q := q) (θ := (1 : ℝ)) (by norm_num)
      hp hh r)

/-! ## Adapter to conditioned ordered prefixes -/

/-- Read an ordered continuation as its chronological list of edges. -/
def continuationHistory {n m R : ℕ} {p : EdgePrefix n m}
    (c : EdgeContinuation p R) : List (Edge n) :=
  List.ofFn fun i ↦ (c i : UnusedEdge p).1

@[simp]
theorem length_continuationHistory {n m R : ℕ} {p : EdgePrefix n m}
    (c : EdgeContinuation p R) :
    (continuationHistory c).length = R := by
  simp [continuationHistory]

theorem edgePrefixSet_appendEdgeContinuation {n m R : ℕ}
    (p : EdgePrefix n m) (c : EdgeContinuation p R) :
    edgePrefixSet (appendEdgeContinuation p c) =
      edgePrefixSet p ∪ (continuationHistory c).toFinset := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_map.mp he with ⟨i, _hi, hi⟩
    refine Fin.addCases (motive := fun i : Fin (m + R) ↦
      appendEdgeContinuation p c i = e →
        e ∈ edgePrefixSet p ∪ (continuationHistory c).toFinset)
      (fun j hj ↦ ?_) (fun j hj ↦ ?_) i hi
    · apply Finset.mem_union_left
      rw [← hj, appendEdgeContinuation_castAdd]
      exact mem_edgePrefixSet p j
    · apply Finset.mem_union_right
      rw [← hj, appendEdgeContinuation_natAdd, List.mem_toFinset]
      exact (List.mem_ofFn' _ _).mpr ⟨j, rfl⟩
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_map.mp he with ⟨i, _hi, hi⟩
      apply Finset.mem_map.mpr
      refine ⟨Fin.castAdd R i, Finset.mem_univ _, ?_⟩
      simpa [appendEdgeContinuation_castAdd] using hi
    · rw [List.mem_toFinset] at he
      rcases (List.mem_ofFn' _ _).mp he with ⟨j, hj⟩
      apply Finset.mem_map.mpr
      refine ⟨Fin.natAdd m j, Finset.mem_univ _, ?_⟩
      simpa [appendEdgeContinuation_natAdd] using hj

theorem graph_appendEdgeContinuation {n m R : ℕ}
    (p : EdgePrefix n m) (c : EdgeContinuation p R) :
    graphOfEdges (edgePrefixSet (appendEdgeContinuation p c)) =
      graphAfterHistory (edgePrefixSet p) (continuationHistory c) := by
  rw [edgePrefixSet_appendEdgeContinuation]
  rfl

/-- A longer ordered prefix is exactly a shorter prefix together with an
ordered continuation through edges unused by that prefix. -/
def splitEdgePrefixEquiv (n m R : ℕ) :
    EdgePrefix n (m + R) ≃
      Σ p : EdgePrefix n m, EdgeContinuation p R :=
  (Equiv.sigmaFiberEquiv
      (fun q : EdgePrefix n (m + R) ↦ (Fin.castAddEmb R).trans q)).symm |>.trans
    (Equiv.sigmaCongrRight fun p ↦ addExtensionEquivContinuation p)

@[simp]
theorem splitEdgePrefixEquiv_fst {n m R : ℕ}
    (q : EdgePrefix n (m + R)) :
    (splitEdgePrefixEquiv n m R q).1 = (Fin.castAddEmb R).trans q := rfl

@[simp]
theorem splitEdgePrefixEquiv_symm_apply {n m R : ℕ}
    (p : EdgePrefix n m) (c : EdgeContinuation p R) :
    (splitEdgePrefixEquiv n m R).symm ⟨p, c⟩ =
      appendEdgeContinuation p c := rfl

theorem graph_splitEdgePrefixEquiv_symm {n m R : ℕ}
    (p : EdgePrefix n m) (c : EdgeContinuation p R) :
    graphOfEdges
        (edgePrefixSet ((splitEdgePrefixEquiv n m R).symm ⟨p, c⟩)) =
      graphAfterHistory (edgePrefixSet p) (continuationHistory c) := by
  rw [splitEdgePrefixEquiv_symm_apply, graph_appendEdgeContinuation]

/-- Every actual ordered continuation is an admissible history in the
without-replacement tree used above. -/
theorem admissibleHistory_continuationHistory {n m R : ℕ}
    (p : EdgePrefix n m) (c : EdgeContinuation p R) :
    AdmissibleHistory (sprinklingAmbient (edgePrefixSet p))
      (continuationHistory c) := by
  constructor
  · rw [continuationHistory, List.nodup_ofFn]
    exact (continuationAsEdges c).injective
  · intro e he
    rcases (List.mem_ofFn' _ _).mp he with ⟨i, rfl⟩
    simp [sprinklingAmbient, (c i).2]

@[simp]
theorem card_sprinklingAmbient_edgePrefixSet {n m : ℕ}
    (p : EdgePrefix n m) :
    (sprinklingAmbient (edgePrefixSet p)).card = edgeCount n - m := by
  rw [sprinklingAmbient, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, card_edgePrefixSet, card_edge]

/-- Exact count of the ordered continuations represented by the adaptive
sampling tree. -/
theorem card_edgeContinuation {n m R : ℕ} (p : EdgePrefix n m) :
    Fintype.card (EdgeContinuation p R) =
      (sprinklingAmbient (edgePrefixSet p)).card.descFactorial R := by
  calc
    Fintype.card (EdgeContinuation p R) =
        Fintype.card (AddExtension p R) :=
      (Fintype.card_congr (addExtensionEquivContinuation p)).symm
    _ = (edgeCount n - m).descFactorial R := card_addExtension p
    _ = (sprinklingAmbient (edgePrefixSet p)).card.descFactorial R := by
      rw [card_sprinklingAmbient_edgePrefixSet]

/-- Exact conditional uniformity of the next edge: after fixing an ordered
prefix, prescribing any one unused next edge leaves the same number of
ordered continuations.  This is the counting statement that identifies the
transition weights in `uniformBoosterLowerTailMass` with the uniform random
edge-ordering process. -/
theorem orderedPrefix_nextEdge_equiprobable {n m R : ℕ}
    (p : EdgePrefix n m) (e f : UnusedEdge p) :
    Fintype.card (ContinuationFirstFiber p e R) =
      Fintype.card (ContinuationFirstFiber p f R) :=
  card_continuationFirstFiber_eq p e f

/-- Ordered-prefix form of the finite graph-process sprinkling estimate.
The preceding two counting lemmas show that its left side is exactly the
conditional finite-tree mass arising from a uniform random edge ordering. -/
theorem orderedPrefixGraphProcessLowerTailMass_le_exp
    {n m k b R r : ℕ} {q : ℝ} (p : EdgePrefix n m)
    (hqnonneg : 0 ≤ q) (hqone : q ≤ 1)
    (hqb : q * (edgeCount n : ℝ) ≤ (b : ℝ))
    (hconnected : (graphOfEdges (edgePrefixSet p)).Connected)
    (hexpander : (graphOfEdges (edgePrefixSet p)).IsTwoExpanderUpTo k)
    (hboosters : ∀ G : SimpleGraph (Fin n),
      graphOfEdges (edgePrefixSet p) ≤ G → G.Connected →
      G.IsTwoExpanderUpTo k → ¬ G.IsHamiltonian →
      b ≤ (edgeBoostersOfGraph G).card)
    (hR : R ≤ edgeCount n - m) :
    uniformBoosterLowerTailMass
        (sprinklingAmbient (edgePrefixSet p))
        (graphProcessBoosters (edgePrefixSet p)) [] R r ≤
      Real.exp ((r : ℝ) - q * (R : ℝ) * (1 - Real.exp (-1))) := by
  apply graphProcessLowerTailMass_le_exp (edgePrefixSet p)
    hqnonneg hqone hqb hconnected hexpander hboosters
  simpa using hR

end

end Erdos746
