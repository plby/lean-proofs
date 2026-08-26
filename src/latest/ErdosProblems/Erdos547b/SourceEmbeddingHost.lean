/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceDegreeFormRootRows
import ErdosProblems.Erdos547b.Claim615RichCoordinatePairFacts

/-!
# The regular-pair host associated with the actual source rows

The reduced graph uses the pre-cleanup graph. Its regular pairs therefore
live in that graph with the same whole-pair deletion, not necessarily in
the degree-form subgraph. The source graph is contained in this embedding
host, and its upper bounds transfer by monotonicity of pair density.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoSourceEmbeddingHost

open Finset SimpleGraph Erdos547EC2
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoClusterPairPruning
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoSourceDegreeFormRootRows
open Erdos547b.ZhaoRichClaim61Lemma611 Erdos547b.ZhaoClaim615RichCoordinatePairFacts

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

/-- Whole-pair deletion in the pre-cleanup graph, which defines the reduced
edges and hence supplies their regular-pair embedding hypotheses. -/
abbrev embeddingHost : SimpleGraph (Fin hostN) :=
  pairPrunedGraph (assignment W) (pruneSmallEdges G {v | q ≤ G.degree v}) (large W)

theorem host_le_embeddingHost : host W ≤ embeddingHost W := by
  intro u v huv
  exact ⟨W.graph_le huv.1, huv.2⟩

theorem embeddingHost_le_original : embeddingHost W ≤ G :=
  (pairPrunedGraph_le (assignment W) _ (large W)).trans (pruneSmallEdges_le G _)

theorem source_le_embeddingHost {Q : Certificate W} (F : CleanSourceWitness W Q) :
    F.source ≤ embeddingHost W :=
  F.source_le.trans (host_le_embeddingHost W)

/-- Pair density is monotone when its two vertex sets are fixed. -/
theorem edgeDensity_le_of_graph_le
    {V : Type*} (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : H ≤ K) (X Y : Finset V) : H.edgeDensity X Y ≤ K.edgeDensity X Y := by
  have hsub : H.interedges X Y ⊆ K.interedges X Y := by
    intro e he
    rw [SimpleGraph.mem_interedges_iff] at he ⊢
    exact ⟨he.1, he.2.1, hHK he.2.2⟩
  rw [SimpleGraph.edgeDensity_def, SimpleGraph.edgeDensity_def]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
    (by positivity)

private theorem uniform_real_of_rat
    {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    {ε : ℚ} {X Y : Finset V} (h : H.IsUniform ε X Y) : H.IsUniform (ε : ℝ) X Y := by
  intro X' hX Y' hY hXlarge hYlarge
  have hXQ : (X.card : ℚ) * ε ≤ (X'.card : ℚ) := by exact_mod_cast hXlarge
  have hYQ : (Y.card : ℚ) * ε ≤ (Y'.card : ℚ) := by exact_mod_cast hYlarge
  exact_mod_cast h hX hY hXQ hYQ

/-- Every reduced edge is a retained regular pair in the embedding host. -/
theorem embedding_pair_of_adj {i j : Index W} (hij : (reduced W).Adj i j) :
    (embeddingHost W).IsUniform (epsilon α : ℝ)
        (clusterVertices (assignment W) i) (clusterVertices (assignment W) j) ∧
      (densityCutoff α : ℝ) ≤ (embeddingHost W).edgeDensity
        (clusterVertices (assignment W) i) (clusterVertices (assignment W) j) := by
  have hcluster (k : Index W) : clusterVertices (assignment W) k = k.1 :=
    clusterVertices_partitionAssignment W.exceptional W.partition k
  have huniform : (pruneSmallEdges G {v | q ≤ G.degree v}).IsUniform (epsilon α)
      (clusterVertices (assignment W) i) (clusterVertices (assignment W) j) := by
    rw [hcluster, hcluster]
    exact hij.1.2.1
  constructor
  · exact uniform_real_of_rat _ (uniform_pair (assignment W) _ (large W) huniform)
  · have hdensity : densityCutoff α ≤ (embeddingHost W).edgeDensity
        (clusterVertices (assignment W) i) (clusterVertices (assignment W) j) := by
      have hkeep : i ∈ large W ∨ j ∈ large W := hij.2
      rw [density_subsets_eq (assignment W) _ (large W)
        (Finset.Subset.refl _) (Finset.Subset.refl _), if_pos hkeep, hcluster, hcluster]
      exact hij.1.2.2
    exact_mod_cast hdensity

/-- The actual host supplies the regular-pair record consumed by the
existing online embedding backend. Dummy clusters cannot be endpoints. -/
theorem embedding_pair_realization :
    ReducedPairRealization (assignment W) (reduced W) (embeddingHost W)
      (epsilon α : ℝ) (densityCutoff α : ℝ) := by
  refine ⟨?_⟩
  intro x y hxy
  cases x with
  | inr d => exact (padGraph_not_adj_inr_left (reduced W) d y hxy).elim
  | inl i =>
    cases y with
    | inr d => exact (padGraph_not_adj_inr_right (reduced W) (Sum.inl i) d hxy).elim
    | inl j =>
      exact embedding_pair_of_adj W ((padGraph_adj_inl (reduced W) i j).mp hxy)

/-- The normalized A-row is bounded above by the density of its actual
embedding pair plus the regularity error whenever the entry is positive. -/
theorem normalized_upper_A {Q : Certificate W} (F : CleanSourceWitness W Q)
    {j : Index W} (hjA : j ≠ Q.A) (hjB : j ≠ Q.B)
    (hpos : 0 < rootDensity W F (Sum.inl Q.A) (Sum.inl j)) :
    rootDensity W F (Sum.inl Q.A) (Sum.inl j) ≤
      (embeddingHost W).edgeDensity (clusterVertices (assignment W) Q.A)
        (clusterVertices (assignment W) j) + (epsilon α : ℝ) := by
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hcluster : clusterVertices (assignment W) j = j.1 :=
    clusterVertices_partitionAssignment W.exceptional W.partition j
  have heq : rootDensity W F (Sum.inl Q.A) (Sum.inl j) =
      (degreeInto F.source F.zA (clusterVertices (assignment W) j) : ℝ) / W.clusterSize := by
    simp only [rootDensity, twoRootSourceDensity_row_A, rootedSourceDensity, padCluster, hcluster]
  have hdegree : 0 < degreeInto F.source F.zA (clusterVertices (assignment W) j) := by
    rw [heq] at hpos
    exact_mod_cast (div_pos_iff_of_pos_right hN).mp hpos
  have hu := F.upperA j hjA hjB hdegree
  have hcard : (clusterVertices (assignment W) j).card = W.clusterSize := by
    rw [hcluster]
    exact W.equal_clusters j.1 j.2
  rw [hcard] at hu
  rw [heq]
  apply (div_le_iff₀ hN).mpr
  have hd : ((host W).edgeDensity (clusterVertices (assignment W) Q.A)
      (clusterVertices (assignment W) j) : ℝ) ≤
      (embeddingHost W).edgeDensity (clusterVertices (assignment W) Q.A)
        (clusterVertices (assignment W) j) := by
    exact_mod_cast edgeDensity_le_of_graph_le _ _ (host_le_embeddingHost W) _ _
  exact hu.trans (mul_le_mul_of_nonneg_right (add_le_add hd le_rfl) hN.le)

/-- The same normalized estimate for the B-row and the same embedding host. -/
theorem normalized_upper_B {Q : Certificate W} (F : CleanSourceWitness W Q)
    {j : Index W} (hjA : j ≠ Q.A) (hjB : j ≠ Q.B)
    (hpos : 0 < rootDensity W F (Sum.inl Q.B) (Sum.inl j)) :
    rootDensity W F (Sum.inl Q.B) (Sum.inl j) ≤
      (embeddingHost W).edgeDensity (clusterVertices (assignment W) Q.B)
        (clusterVertices (assignment W) j) + (epsilon α : ℝ) := by
  have hN : (0 : ℝ) < W.clusterSize := by exact_mod_cast W.clusterSize_pos
  have hcluster : clusterVertices (assignment W) j = j.1 :=
    clusterVertices_partitionAssignment W.exceptional W.partition j
  have hAB : (Sum.inl Q.A : EvenPadding (Index W)) ≠ Sum.inl Q.B := by
    exact fun h => Q.adj.ne (Sum.inl.inj h)
  have heq : rootDensity W F (Sum.inl Q.B) (Sum.inl j) =
      (degreeInto F.source F.zB (clusterVertices (assignment W) j) : ℝ) / W.clusterSize := by
    rw [rootDensity, twoRootSourceDensity_row_B _ _ _ _ _ _ _ hAB]
    simp only [rootedSourceDensity, padCluster, hcluster]
  have hdegree : 0 < degreeInto F.source F.zB (clusterVertices (assignment W) j) := by
    rw [heq] at hpos
    exact_mod_cast (div_pos_iff_of_pos_right hN).mp hpos
  have hu := F.upperB j hjA hjB hdegree
  have hcard : (clusterVertices (assignment W) j).card = W.clusterSize := by
    rw [hcluster]
    exact W.equal_clusters j.1 j.2
  rw [hcard] at hu
  rw [heq]
  apply (div_le_iff₀ hN).mpr
  have hd : ((host W).edgeDensity (clusterVertices (assignment W) Q.B)
      (clusterVertices (assignment W) j) : ℝ) ≤
      (embeddingHost W).edgeDensity (clusterVertices (assignment W) Q.B)
        (clusterVertices (assignment W) j) := by
    exact_mod_cast edgeDensity_le_of_graph_le _ _ (host_le_embeddingHost W) _ _
  exact hu.trans (mul_le_mul_of_nonneg_right (add_le_add hd le_rfl) hN.le)

/-- A positive A-row entry supplies one compatible regular pair and the
source-density upper bound, including for padded matching coordinates. -/
theorem source_pair_A {Q : Certificate W} (F : CleanSourceWitness W Q)
    {x : EvenPadding (Index W)} (hxA : x ≠ Sum.inl Q.A) (hxB : x ≠ Sum.inl Q.B)
    (hpos : 0 < rootDensity W F (Sum.inl Q.A) x) :
    let X := clusterVertices (assignment W) Q.A
    let Y := padCluster (clusterVertices (assignment W)) x
    (embeddingHost W).IsUniform (epsilon α : ℝ) X Y ∧
      (densityCutoff α : ℝ) ≤ (embeddingHost W).edgeDensity X Y ∧
      rootDensity W F (Sum.inl Q.A) x ≤
        (embeddingHost W).edgeDensity X Y + (epsilon α : ℝ) := by
  have hadj := (CleanSourceWitness.source_rows W F).supportA x hpos
  obtain ⟨hreg, hcut⟩ := (embedding_pair_realization W).pair_of_adj _ _ hadj
  refine ⟨hreg, hcut, ?_⟩
  cases x with
  | inr d => exact (padGraph_not_adj_inr_right (reduced W) (Sum.inl Q.A) d hadj).elim
  | inl j =>
    exact normalized_upper_A W F (fun h => hxA (congrArg Sum.inl h))
      (fun h => hxB (congrArg Sum.inl h)) hpos

/-- The analogous compatible source pair for the B-row. -/
theorem source_pair_B {Q : Certificate W} (F : CleanSourceWitness W Q)
    {x : EvenPadding (Index W)} (hxA : x ≠ Sum.inl Q.A) (hxB : x ≠ Sum.inl Q.B)
    (hpos : 0 < rootDensity W F (Sum.inl Q.B) x) :
    let X := clusterVertices (assignment W) Q.B
    let Y := padCluster (clusterVertices (assignment W)) x
    (embeddingHost W).IsUniform (epsilon α : ℝ) X Y ∧
      (densityCutoff α : ℝ) ≤ (embeddingHost W).edgeDensity X Y ∧
      rootDensity W F (Sum.inl Q.B) x ≤
        (embeddingHost W).edgeDensity X Y + (epsilon α : ℝ) := by
  have hadj := (CleanSourceWitness.source_rows W F).supportB x hpos
  obtain ⟨hreg, hcut⟩ := (embedding_pair_realization W).pair_of_adj _ _ hadj
  refine ⟨hreg, hcut, ?_⟩
  cases x with
  | inr d => exact (padGraph_not_adj_inr_right (reduced W) (Sum.inl Q.B) d hadj).elim
  | inl j =>
    exact normalized_upper_B W F (fun h => hxA (congrArg Sum.inl h))
      (fun h => hxB (congrArg Sum.inl h)) hpos

end Erdos547b.ZhaoSourceEmbeddingHost

#print axioms Erdos547b.ZhaoSourceEmbeddingHost.host_le_embeddingHost
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.embeddingHost_le_original
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.source_le_embeddingHost
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.edgeDensity_le_of_graph_le
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.embedding_pair_realization
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.normalized_upper_A
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.normalized_upper_B
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.source_pair_A
#print axioms Erdos547b.ZhaoSourceEmbeddingHost.source_pair_B
