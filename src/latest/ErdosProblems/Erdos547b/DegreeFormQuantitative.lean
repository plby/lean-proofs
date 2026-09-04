/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.DegreeForm

open Finset
open scoped SimpleGraph

noncomputable section

namespace Erdos547b.ZhaoDegreeFormQuantitative

open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoStability

/-- The reduced graph formed from the cleaned graph itself.  Supplying the
stored decision procedure explicitly keeps this definition usable without a
global instance for `W.graph`. -/
def cleanedReducedGraph
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M)
    (δ : ℚ) : SimpleGraph {Q // Q ∈ W.partition.parts} :=
  @regularityReducedGraph _ _ W.graph W.graph_decidable
    (fun i : {Q // Q ∈ W.partition.parts} => i.1) ε δ

/-- At any positive cutoff, the cleaned reduced graph is a subgraph of the
source reduced graph stored in degree form.  A cleaned reduced edge has
positive density, hence contains an actual cleaned edge; `W.respects_reduced`
then transports that edge. -/
theorem cleanedReducedGraph_le_source
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M)
    {δ : ℚ} (hδ : 0 < δ) :
    cleanedReducedGraph W δ ≤
      regularityReducedGraph G
        (fun i : {Q // Q ∈ W.partition.parts} => i.1) ε d := by
  let : DecidableRel W.graph.Adj := W.graph_decidable
  intro i j hij
  have hdensity : 0 < W.graph.edgeDensity i.1 j.1 :=
    hδ.trans_le hij.2.2
  have hinter : (W.graph.interedges i.1 j.1).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hzero : W.graph.edgeDensity i.1 j.1 = 0 := by
      rw [W.graph.edgeDensity_def, hempty]
      simp
    rw [hzero] at hdensity
    exact lt_irrefl 0 hdensity
  obtain ⟨p, hp⟩ := hinter
  have hp' := (SimpleGraph.mem_interedges_iff W.graph).mp hp
  apply W.respects_reduced
    ((partitionAssignment_eq_some_iff W.exceptional W.partition p.1 i).mpr
      hp'.1)
    ((partitionAssignment_eq_some_iff W.exceptional W.partition p.2 j).mpr
      hp'.2.1)
    hp'.2.2

/-- If the new cutoff is at most the degree-form density threshold, every
cleaned edge respects the cleaned reduced graph.  Zero cleaned pairs contain
no edge, while every nonzero pair has density strictly above `d`. -/
theorem cleanedGraph_respects_cleanedReducedGraph
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M)
    {δ : ℚ} (hδd : δ ≤ d) :
    EdgesRespectReducedGraph
      (partitionAssignment W.exceptional W.partition) W.graph
      (cleanedReducedGraph W δ) := by
  let : DecidableRel W.graph.Adj := W.graph_decidable
  intro x y i j hxi hyj hxy
  have hxi' : x ∈ i.1 :=
    (partitionAssignment_eq_some_iff W.exceptional W.partition x i).mp hxi
  have hyj' : y ∈ j.1 :=
    (partitionAssignment_eq_some_iff W.exceptional W.partition y j).mp hyj
  have hij : i ≠ j := by
    intro hij
    subst j
    exact W.no_intra_edges i hxi' hyj' hxy
  have hdensityPos : 0 < W.graph.edgeDensity i.1 j.1 := by
    have hnum : 0 < (W.graph.interedges i.1 j.1).card :=
      Finset.card_pos.mpr ⟨(x, y),
        (SimpleGraph.mem_interedges_iff W.graph).mpr ⟨hxi', hyj', hxy⟩⟩
    have hnumQ : (0 : ℚ) < (W.graph.interedges i.1 j.1).card := by
      exact_mod_cast hnum
    have hclusterQ : (0 : ℚ) < W.clusterSize := by
      exact_mod_cast W.clusterSize_pos
    have hiCard : i.1.card = W.clusterSize := W.equal_clusters i.1 i.2
    have hjCard : j.1.card = W.clusterSize := W.equal_clusters j.1 j.2
    rw [W.graph.edgeDensity_def, hiCard, hjCard]
    positivity
  have hdensity : d < W.graph.edgeDensity i.1 j.1 := by
    rcases W.pair_density i j with hzero | hlarge
    · rw [hzero] at hdensityPos
      exact False.elim (lt_irrefl 0 hdensityPos)
    · exact hlarge
  exact ⟨hij, W.pair_uniform i j, hδd.trans hdensity.le⟩

theorem partition_card_mul_clusterSize
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M) :
    #W.partition.parts * W.clusterSize =
      #((Finset.univ : Finset (Fin n)) \ W.exceptional) := by
  calc
    #W.partition.parts * W.clusterSize =
        ∑ Q ∈ W.partition.parts, #Q := by
          symm
          exact Finset.sum_const_nat fun Q hQ => W.equal_clusters Q hQ
    _ = #((Finset.univ : Finset (Fin n)) \ W.exceptional) :=
      W.partition.sum_card_parts

theorem exceptional_add_clusters_eq_host
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M) :
    W.exceptional.card + #W.partition.parts * W.clusterSize = n := by
  rw [partition_card_mul_clusterSize W,
    Finset.card_sdiff_of_subset (Finset.subset_univ W.exceptional)]
  have hE : W.exceptional.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ W.exceptional)
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- Exact exceptional-set bound in terms of discarded clusters and trim. -/
theorem exceptional_card_lt_discard_trim
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M) :
    (W.exceptional.card : ℝ) <
      (W.ordinaryParts : ℝ) *
          ((n / W.ordinaryParts - W.clusterSize : ℕ) + 1) +
        ((W.ordinaryParts - #W.partition.parts : ℕ) : ℝ) *
          ((n / W.ordinaryParts + 1 : ℕ) : ℝ) := by
  let K := W.ordinaryParts
  let Q := #W.partition.parts
  let m := W.clusterSize
  let a := n / K
  let b := K - Q
  let r := a - m
  have hQK : Q ≤ K := W.cleaned_le_ordinary
  have hm : m ≤ a := W.clusterSize_le_average
  have hKpos : 0 < K := W.ordinaryParts_pos
  have hK : K = Q + b := by
    dsimp [b]
    omega
  have ha : a = m + r := by
    dsimp [r]
    omega
  have hnlt : n < K * (a + 1) := by
    dsimp [a]
    exact Nat.lt_mul_div_succ n hKpos
  have hhost : n = W.exceptional.card + Q * m := by
    simpa [Q, m, Nat.add_comm] using
      (exceptional_add_clusters_eq_host W).symm
  have hKR : (K : ℝ) = (Q : ℝ) + (b : ℝ) := by exact_mod_cast hK
  have hamR : (a : ℝ) = (m : ℝ) + (r : ℝ) := by exact_mod_cast ha
  have hnltR : (n : ℝ) < (K : ℝ) * ((a : ℝ) + 1) := by exact_mod_cast hnlt
  have hhostR : (n : ℝ) = (W.exceptional.card : ℝ) + (Q : ℝ) * (m : ℝ) := by
    exact_mod_cast hhost
  have hbound : (W.exceptional.card : ℝ) <
      (K : ℝ) * ((r + 1 : ℕ) : ℝ) + (b : ℝ) * ((a + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  simpa [K, Q, m, a, b, r] using hbound

/-- Exceptional-set bound containing only the stored cleanup fractions. -/
theorem exceptional_card_lt_cleanup_bound
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M) :
    (W.exceptional.card : ℝ) <
      (W.ordinaryParts : ℝ) *
          (cleanupFraction ε * ((n / W.ordinaryParts + 1 : ℕ) : ℝ) + 2) +
        cleanupFraction ε * (W.ordinaryParts : ℝ) *
          ((n / W.ordinaryParts + 1 : ℕ) : ℝ) := by
  have hraw := exceptional_card_lt_discard_trim W
  have htrim := W.trim_lt
  have hdiscard := W.discardedParts_lt
  have htrim' :
      (((n / W.ordinaryParts - W.clusterSize : ℕ) + 1 : ℕ) : ℝ) <
        cleanupFraction ε * ((n / W.ordinaryParts + 1 : ℕ) : ℝ) + 2 := by
    push_cast at htrim ⊢
    linarith
  calc
    (W.exceptional.card : ℝ) <
        (W.ordinaryParts : ℝ) *
            ((n / W.ordinaryParts - W.clusterSize : ℕ) + 1) +
          ((W.ordinaryParts - #W.partition.parts : ℕ) : ℝ) *
            ((n / W.ordinaryParts + 1 : ℕ) : ℝ) := hraw
    _ < (W.ordinaryParts : ℝ) *
            (cleanupFraction ε * ((n / W.ordinaryParts + 1 : ℕ) : ℝ) + 2) +
          cleanupFraction ε * (W.ordinaryParts : ℝ) *
            ((n / W.ordinaryParts + 1 : ℕ) : ℝ) := by
      have hKpos : (0 : ℝ) < W.ordinaryParts := by
        exact_mod_cast W.ordinaryParts_pos
      have haPos : (0 : ℝ) < ((n / W.ordinaryParts + 1 : ℕ) : ℝ) := by
        positivity
      have hfirst := mul_lt_mul_of_pos_left htrim' hKpos
      have hsecond := mul_lt_mul_of_pos_right hdiscard haPos
      push_cast at hfirst
      calc
        (W.ordinaryParts : ℝ) *
              ((n / W.ordinaryParts - W.clusterSize : ℕ) + 1) +
            ((W.ordinaryParts - #W.partition.parts : ℕ) : ℝ) *
              ((n / W.ordinaryParts + 1 : ℕ) : ℝ) <
            (W.ordinaryParts : ℝ) *
              (cleanupFraction ε * ((n / W.ordinaryParts + 1 : ℕ) : ℝ) + 2) +
            ((W.ordinaryParts - #W.partition.parts : ℕ) : ℝ) *
              ((n / W.ordinaryParts + 1 : ℕ) : ℝ) := by
          simpa [Nat.cast_add, add_comm] using
            (add_lt_add_right hfirst
              (((W.ordinaryParts - #W.partition.parts : ℕ) : ℝ) *
                ((n / W.ordinaryParts + 1 : ℕ) : ℝ)))
        _ < (W.ordinaryParts : ℝ) *
              (cleanupFraction ε * ((n / W.ordinaryParts + 1 : ℕ) : ℝ) + 2) +
            cleanupFraction ε * (W.ordinaryParts : ℝ) *
              ((n / W.ordinaryParts + 1 : ℕ) : ℝ) := by
          simpa [mul_assoc] using
            (add_lt_add_right hsecond
              ((W.ordinaryParts : ℝ) *
                (cleanupFraction ε *
                  ((n / W.ordinaryParts + 1 : ℕ) : ℝ) + 2)))

/-- The factor-five degree-form threshold forces the exceptional set below
half the host, independently of `ε`. -/
theorem exceptional_card_lt_half_host
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M)
    (hε : 0 < ε) (hn : 0 < n) :
    (W.exceptional.card : ℝ) < (n : ℝ) / 2 := by
  have hclean := exceptional_card_lt_cleanup_bound W
  let K := W.ordinaryParts
  let A := ((n / K + 1 : ℕ) : ℝ)
  have hq0 : 0 ≤ cleanupFraction ε := (cleanupFraction_pos hε).le
  have hq : cleanupFraction ε ≤ (1 : ℝ) / 64 :=
    cleanupFraction_le_one_div ε
  have hKA : (K : ℝ) * A ≤ (n : ℝ) + K := by
    have hdiv : (n / K) * K ≤ n := Nat.div_mul_le_self n K
    have hdivR : ((n / K : ℕ) : ℝ) * (K : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hdiv
    dsimp [A]
    push_cast
    nlinarith
  have hK : (5 : ℝ) * K ≤ n := by
    exact_mod_cast W.five_ordinaryParts_le_host
  have hX0 : 0 ≤ (K : ℝ) * A := by positivity
  have hqX : 2 * cleanupFraction ε * ((K : ℝ) * A) ≤
      ((K : ℝ) * A) / 32 := by
    have h2q : 2 * cleanupFraction ε ≤ (1 : ℝ) / 32 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2q hX0]
  have hform : (W.exceptional.card : ℝ) <
      2 * cleanupFraction ε * ((K : ℝ) * A) + 2 * K := by
    rw [show
      (W.ordinaryParts : ℝ) *
            (cleanupFraction ε *
                ((n / W.ordinaryParts + 1 : ℕ) : ℝ) + 2) +
          cleanupFraction ε * (W.ordinaryParts : ℝ) *
            ((n / W.ordinaryParts + 1 : ℕ) : ℝ) =
        2 * cleanupFraction ε * ((K : ℝ) * A) + 2 * K by
      dsimp [K, A]
      ring] at hclean
    exact hclean
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

theorem exceptional_card_lt_ramseyHalf
    {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M)
    (hε : 0 < ε) (hn : 2 ≤ n) :
    W.exceptional.card < n - 1 := by
  have hhost : 0 < 2 * n - 2 := by omega
  have h := exceptional_card_lt_half_host W hε hhost
  have hhalf : (((2 * n - 2 : ℕ) : ℝ) / 2) = (n - 1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n),
      Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring
  rw [hhalf] at h
  exact_mod_cast h

/-- Direct real upper bound for the pointwise degree loss. -/
theorem loss_lt_average_add_cleanup
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {ε d : ℚ} {m₀ M : ℕ} (W : DegreeFormWitness G ε d m₀ M)
    (hε : 0 < ε) (hd : 0 < d) :
    (W.loss : ℝ) <
      ((n / W.ordinaryParts : ℕ) : ℝ) +
        (2 * cleanupFraction ε + (d : ℝ) + 2 * ordinaryError ε) *
          ((n : ℝ) + W.ordinaryParts) + 1 := by
  let K := W.ordinaryParts
  let A := n / K + 1
  let f := 2 * cleanupFraction ε + (d : ℝ) + 2 * ordinaryError ε
  have hf0 : 0 ≤ f := by
    dsimp [f]
    have hq := (cleanupFraction_pos hε).le
    have hη := (ordinaryError_pos hε).le
    have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
    positivity
  have hKA : (K : ℝ) * (A : ℝ) ≤ (n : ℝ) + K := by
    have hdiv : (n / K) * K ≤ n := Nat.div_mul_le_self n K
    have hdivR : ((n / K : ℕ) : ℝ) * (K : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hdiv
    dsimp [A]
    push_cast
    nlinarith
  have hceil :
      (⌈f * (K : ℝ) * (A : ℝ)⌉₊ : ℝ) <
        f * (K : ℝ) * (A : ℝ) + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  have hfactor : f * (K : ℝ) * (A : ℝ) ≤ f * ((n : ℝ) + K) := by
    nlinarith [mul_le_mul_of_nonneg_left hKA hf0]
  rw [W.loss_eq]
  change
    ((W.clusterSize +
      ⌈f * (K : ℝ) * (A : ℝ)⌉₊ : ℕ) : ℝ) < _
  push_cast
  have hm : (W.clusterSize : ℝ) ≤ ((n / K : ℕ) : ℝ) := by
    exact_mod_cast W.clusterSize_le_average
  dsimp [K, f] at hm ⊢
  nlinarith

#print axioms partition_card_mul_clusterSize
#print axioms cleanedReducedGraph_le_source
#print axioms cleanedGraph_respects_cleanedReducedGraph
#print axioms exceptional_add_clusters_eq_host
#print axioms exceptional_card_lt_discard_trim
#print axioms exceptional_card_lt_cleanup_bound
#print axioms exceptional_card_lt_half_host
#print axioms exceptional_card_lt_ramseyHalf
#print axioms loss_lt_average_add_cleanup

end Erdos547b.ZhaoDegreeFormQuantitative
