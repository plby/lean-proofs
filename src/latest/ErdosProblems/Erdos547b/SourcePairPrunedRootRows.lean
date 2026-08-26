/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RichClaim61Lemma611
import ErdosProblems.Erdos547b.ClusterPairPruning

/-!
# Actual root rows after whole-pair pruning

The degree-form loss is used before whole-pair pruning. Only the degrees
on the two large root reservoirs are transported afterward; no global
degree-loss claim for the pair-pruned graph is needed.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoSourcePairPrunedRootRows

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoQuantitativeLargeClusters Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoEvenReducedPadding Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616 Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClusterPairPruning

/-- Construct the two literal source rows, avoiding any prescribed bad
sets smaller than the root reservoirs, on the actual pair-pruned graph. -/
theorem exists_pairPruned_rootRows
    {V I : Type*} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I]
    (Pcluster : ClusterAssignment V I)
    (Gdegree H : SimpleGraph V)
    [DecidableRel Gdegree.Adj] [DecidableRel H.Adj]
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (cluster : I → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (threshold quota miss clusterSize loss : ℕ)
    (hquota : 0 < quota) (hclusterSize : 0 < clusterSize)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (hloss : DegreeLossAtMost
      (pruneSmallEdges Gdegree {v | threshold ≤ Gdegree.degree v}) H loss)
    (hrespect : EdgesRespectReducedGraph Pcluster H R0)
    (badA badB : Finset V)
    (hbadA : badA.card < quota) (hbadB : badB.card < quota)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota
      (pruneSmallEdges R0 (largeClustersAtLeast Pcluster Gdegree threshold quota : Set I))
      (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
        Pcluster Gdegree threshold quota) miss) :
    ∃ zA ∈ Q.A₀, zA ∉ badA ∧ ∃ zB ∈ Q.B₀, zB ∉ badB ∧
      let Lp := padFinset
        (Erdos547b.ZhaoQuantitativeLargeClusters.largeClustersAtLeast
          Pcluster Gdegree threshold quota)
      let A : EvenPadding I := Sum.inl Q.A
      let B : EvenPadding I := Sum.inl Q.B
      let density := twoRootSourceDensity
        (pairPrunedGraph Pcluster H (largeClustersAtLeast Pcluster Gdegree threshold quota))
        (padCluster cluster)
        (clusterSize : ℝ) A B zA zB
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) A
          (allMatchingEdges Q.claim67.M)) ∧
      (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
          miss * clusterSize : ℕ) : ℝ) ≤
        sourceDegree Q.claim67.M Lp density (clusterSize : ℝ) B
          (allMatchingEdges Q.claim67.M)) ∧
      (∀ x, 0 ≤ density A x) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        0 ≤ (clusterSize : ℝ) *
          (density A (orientedEndpoint Q.claim67.M Lp e 0) +
            density A (orientedEndpoint Q.claim67.M Lp e 1))) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        0 ≤ (clusterSize : ℝ) *
          (density B (orientedEndpoint Q.claim67.M Lp e 0) +
            density B (orientedEndpoint Q.claim67.M Lp e 1))) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        (clusterSize : ℝ) *
          (density A (orientedEndpoint Q.claim67.M Lp e 0) +
            density A (orientedEndpoint Q.claim67.M Lp e 1)) ≤
              2 * clusterSize) ∧
      (∀ e : MatchingEdge Q.claim67.M,
        (clusterSize : ℝ) *
          (density B (orientedEndpoint Q.claim67.M Lp e 0) +
            density B (orientedEndpoint Q.claim67.M Lp e 1)) ≤
              2 * clusterSize) ∧
      (∀ x, 0 < density A x → (padGraph (pruneSmallEdges R0
        (largeClustersAtLeast Pcluster Gdegree threshold quota : Set I))).Adj A x) ∧
      (∀ x, 0 < density B x → (padGraph (pruneSmallEdges R0
        (largeClustersAtLeast Pcluster Gdegree threshold quota : Set I))).Adj B x) := by
  classical
  let L := largeClustersAtLeast Pcluster Gdegree threshold quota
  let H' := pairPrunedGraph Pcluster H L
  let R' := pruneSmallEdges R0 (L : Set I)
  have hrespect' : EdgesRespectReducedGraph (padAssignment Pcluster) H'
      (padGraph R') :=
    edgesRespect_pad Pcluster H' R'
      (respects_pruned_reduced_graph Pcluster H R0 L hrespect)
  apply exists_twoRootSourceDensity_of_richClaim61_localDegree Pcluster Gdegree H'
    R' cluster hcluster threshold quota miss clusterSize loss hquota hclusterSize
    hclusterCard hrespect' badA badB hbadA hbadB Q
  · intro z hz
    have hzP := (mem_clusterVertices Pcluster Q.A z).mp (Q.A₀_subset hz)
    change threshold - loss ≤ (pairPrunedGraph Pcluster H L).degree z
    rw [degree_eq_of_large_cluster Pcluster H L Q.A_mem hzP]
    exact cleaned_degree_ge_threshold_sub_loss
      (pruneSmallEdges Gdegree {v | threshold ≤ Gdegree.degree v}) H loss threshold
      hloss ((highDegree_iff_pruneSmallEdges_highDegree Gdegree threshold z).mpr
        (Q.A₀_high z hz))
  · intro z hz
    have hzP := (mem_clusterVertices Pcluster Q.B z).mp (Q.B₀_subset hz)
    change threshold - loss ≤ (pairPrunedGraph Pcluster H L).degree z
    rw [degree_eq_of_large_cluster Pcluster H L Q.B_mem hzP]
    exact cleaned_degree_ge_threshold_sub_loss
      (pruneSmallEdges Gdegree {v | threshold ≤ Gdegree.degree v}) H loss threshold
      hloss ((highDegree_iff_pruneSmallEdges_highDegree Gdegree threshold z).mpr
        (Q.B₀_high z hz))

end Erdos547b.ZhaoSourcePairPrunedRootRows

#print axioms Erdos547b.ZhaoSourcePairPrunedRootRows.exists_pairPruned_rootRows
