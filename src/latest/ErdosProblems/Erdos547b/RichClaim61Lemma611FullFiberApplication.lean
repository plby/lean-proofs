/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.RichClaim61Lemma611
import ErdosProblems.Erdos547b.Claim615RichExceptionalFullFiberForcing

/-!
# Lemma 6.11 after the concrete full-fiber Claim 6.15

The preliminary reserved matching used by Claim 6.15 has to be selected
before the exceptional-family estimates are known.  It is independent of
the optional reserved matching stored in the later Lemma-6.11 decomposition.
This file performs that ordering explicitly: Lemma 6.12 first chooses the
preliminary family, the synchronized full-fiber realization proves both
exceptional bounds by contraposition, and only then is the final matching
decomposition constructed.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication

open Finset Fintype SimpleGraph
open Erdos547b.TreePartition
open Erdos547b.ZhaoClaim68
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoLemma615
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616ResidualAllocation
open Erdos547b.ZhaoClaim615SourceSelection
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6EventualParameters
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim615RichHierarchicalAllocation
open Erdos547b.ZhaoClaim615RichExceptionalFullFiberForcing

universe u v w

variable {TreeVertex : Type u} [Fintype TreeVertex] [DecidableEq TreeVertex]
variable {T : SimpleGraph TreeVertex} [DecidableRel T.Adj]
variable {globalRoot : TreeVertex} {small : ℕ}
variable {V : Type v} {I : Type w}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

variable (Pcluster : ClusterAssignment V I)
variable (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R0 : SimpleGraph I) [DecidableRel R0.Adj]
variable {beta : ℚ}
variable {reducedK : ℕ}
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
    (largeClustersAtLeast Pcluster Gdegree threshold quota)
    (claim61Miss beta reducedK))
variable (density : EvenPadding I → EvenPadding I → ℝ)
variable (N nTree targetB fb cutoff error : ℝ)
variable (lowerV1 upperV1 upperV2 : ℕ)

/-- The source and scalar facts used by Lemma 6.11 before the two
exceptional-family estimates are available. -/
structure PreExceptionalFacts : Prop where
  reducedK_eq : reducedK = paddedHalf I
  reducedK_large : section6K₀ beta ≤ reducedK
  N_pos : 0 < N
  nTree_pos : 0 < nTree
  error_nonneg : 0 ≤ error
  targetB_nonneg : 0 ≤ targetB
  A_edge_nonneg : ∀ e : MatchingEdge Q.claim67.M,
    0 ≤ N * (density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 0) +
      density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 1))
  A_density_nonneg : ∀ x, 0 ≤ density (Sum.inl Q.A) x
  B_edge_nonneg : ∀ e : MatchingEdge Q.claim67.M,
    0 ≤ N * (density (Sum.inl Q.B)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 0) +
      density (Sum.inl Q.B)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 1))
  A_edge_cap : ∀ e : MatchingEdge Q.claim67.M,
    N * (density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 0) +
      density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 1)) ≤ 2 * N
  B_edge_cap : ∀ e : MatchingEdge Q.claim67.M,
    N * (density (Sum.inl Q.B)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 0) +
      density (Sum.inl Q.B)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e 1)) ≤ 2 * N
  degreeA :
    (1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N ≤
      sourceDegree Q.claim67.M
        (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
        density N (Sum.inl Q.A) (allMatchingEdges Q.claim67.M)
  degreeB :
    (1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N ≤
      sourceDegree Q.claim67.M
        (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
        density N (Sum.inl Q.B) (allMatchingEdges Q.claim67.M)
  density_adj_A : ∀ x, 0 < density (Sum.inl Q.A) x →
    (padGraph R0).Adj (Sum.inl Q.A) x
  density_adj_B : ∀ x, 0 < density (Sum.inl Q.B) x →
    (padGraph R0).Adj (Sum.inl Q.B) x
  B_total : targetB ≤ sourceDegree Q.claim67.M
    (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
    density N (Sum.inl Q.B) (allMatchingEdges Q.claim67.M)
  B_total_pos : 0 < sourceDegree Q.claim67.M
    (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
    density N (Sum.inl Q.B) (allMatchingEdges Q.claim67.M)
  B_card : ((allMatchingEdges Q.claim67.M).card : ℝ) * (targetB + 2 * N) ≤
    (claim617Q beta reducedK : ℝ) * sourceDegree Q.claim67.M
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      density N (Sum.inl Q.B) (allMatchingEdges Q.claim67.M)
  n_covered : nTree ≤ (reducedK : ℝ) * N + error
  cover : (reducedK : ℝ) * N ≤ nTree + N
  error_small : error ≤ (sigma beta : ℝ) * nTree
  cluster_small : N ≤ 3 * (sigma beta : ℝ) * nTree
  lower : ∀ S : Finset (MatchingEdge Q.claim67.M),
    S ⊆ allMatchingEdges Q.claim67.M →
    lemma611TargetA beta nTree < sourceDegree Q.claim67.M
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      density N (Sum.inl Q.A) S → lowerV1 ≤ 2 * S.card
  upper : 2 * minEdgeCap reducedK ≤ upperV1
  total_card : Fintype.card (EvenPadding I) ≤ lowerV1 + upperV2

/-- The canonical preliminary reserved family selected from the B-row before
the exceptional estimates are proved. -/
noncomputable def PreExceptionalFacts.preliminaryReservedEdges
    (F : PreExceptionalFacts Pcluster Gdegree threshold quota R0 Q density N
      nTree targetB error lowerV1 upperV1 upperV2) :
    PreliminaryReservedEdges Q density
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      N targetB (2 * N) (claim617Q beta reducedK) := by
  let L := padFinset
    (largeClustersAtLeast Pcluster Gdegree threshold quota)
  apply Classical.choice
  apply exists_preliminaryReservedEdges Q density L N targetB (2 * N)
    (claim617Q beta reducedK)
  · intro e _
    simpa [L] using F.B_edge_nonneg e
  · exact F.targetB_nonneg
  · linarith [F.N_pos]
  · intro e _
    simpa [L] using F.B_edge_cap e
  · exact F.B_total
  · exact F.B_total_pos
  · exact F.B_card

/-- All state-independent data needed to run both branches of Claim 6.15
against one independently chosen preliminary reserved family. -/
structure ExceptionalFullFiberContext
    (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    (Mb : PreliminaryReservedEdges Q density
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      N targetB (2 * N) (claim617Q beta reducedK))
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph V) [DecidableRel G.Adj] : Type (max u v w) where
  tree : T.IsTree
  nU : ℕ
  kU : ℕ
  nU_two : 2 ≤ nU
  ghost : SimpleGraph (Fin (2 * nU - 2))
  ghostAdj : DecidableRel ghost.Adj
  ghost_large : nU - 1 ≤
    #(Finset.univ.filter fun x ↦ nU - 1 ≤ ghost.degree x)
  ghost_not_extreme : ¬ ZhaoExtremalCaseOne beta ghost
  ghost_numeric : (2 * kU * ((nU - 1 : ℕ) : ℚ)) ≤
    beta * ((nU - 1 : ℕ) : ℚ) * ((nU - 1 : ℕ) : ℚ)
  tree_card_three : 3 ≤ Fintype.card TreeVertex
  tree_order : Fintype.card TreeVertex - 1 ≤ nU - 1
  tree_not_contained_ghost : ¬ T.IsContained ghost
  targetU : ℕ
  slackU : ℕ
  ratio : ℝ
  ratio_nonneg : 0 ≤ ratio
  ratio_half : ratio ≤ 1 / 2
  slackU_pos : 0 < slackU
  branch_small_U : ∀ j, (branchForest P).branches.size j ≤ slackU
  threshold_U : ((Fintype.card TreeVertex - (kU + 1) : ℕ) : ℝ) ≤
    (1 - 2 * ratio) *
        ((branchMass P (halfBranches P) : ℝ) - targetU) -
      2 * P.numParts
  gammaU : ℝ
  epsilonU : ℝ
  d : ℝ
  d_nonneg : 0 ≤ d
  nP : ℕ
  tree_card : Fintype.card TreeVertex = nP + 1
  original_leaves :
    (((partitionLevelOneLeaves P ∩ graphLeaves T).card : ℕ) : ℝ) <
      11 * Real.sqrt d * nP
  hierarchyF : 2 * (P.numParts : ℝ) < 1 + Real.sqrt d * nP
  hierarchyA : 3 * (P.numParts : ℝ) < 1 + 2 * Real.sqrt d * nP
  targetP : ℕ
  slackP : ℕ
  targetP_bound : (targetP : ℝ) <
    (nP : ℝ) / 2 - 12 * Real.sqrt d * nP
  slackP_pos : 0 < slackP
  branch_small_P : ∀ j, (branchForest P).branches.size j ≤ slackP
  gammaP : ℝ
  epsilonP : ℝ
  unbalanced : ∀ E0 : SelectedExceptionalEdges Q density
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      (eta beta : ℝ) .unbalanced
      (upperScale (((eta beta : ℝ) * reducedK) / 2)),
    UnbalancedFullFiberFacts Pcluster Gdegree threshold quota R0
      (claim61Miss beta reducedK) Q density Mb P tree E0 targetU slackU ratio
      gammaU epsilonU G
  nonextreme : ∀ E0 : SelectedExceptionalEdges Q density
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      (eta beta : ℝ) .nonextreme
      (upperScale (((eta beta : ℝ) * reducedK) / 2)),
    NonextremeFullFiberFacts Pcluster Gdegree threshold quota R0
      (claim61Miss beta reducedK) Q density Mb P tree E0 targetP slackP gammaP
      epsilonP G

/-- The concrete full-fiber Claim 6.15 supplies the two exceptional bounds
needed by the literal Lemma-6.11 constructor. -/
theorem ExceptionalFullFiberContext.exceptionalBounds
    (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    (Mb : PreliminaryReservedEdges Q density
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      N targetB (2 * N) (claim617Q beta reducedK))
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : ExceptionalFullFiberContext Pcluster Gdegree threshold quota R0 Q
      density N targetB hbeta hbetaOne Mb P G)
    (hreducedK : section6K₀ beta ≤ reducedK)
    (hN : 0 < N) (hnot : ¬ T.IsContained G) :
    (((unbalancedEdges
      (edgesAwayFromDistinguished Q.claim67.M
        (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
        (Sum.inl Q.A) (Sum.inl Q.B))
      (fun e c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e c)) (eta beta : ℝ)).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK ∧
    (((nonextremeEdges
      (edgesAwayFromDistinguished Q.claim67.M
        (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
        (Sum.inl Q.A) (Sum.inl Q.B))
      (fun e c ↦ density (Sum.inl Q.A)
        (orientedEndpoint Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          e c)) (eta beta : ℝ)).card : ℕ) : ℝ) <
        (eta beta : ℝ) * reducedK := by
  letI : DecidableRel C.ghost.Adj := C.ghostAdj
  exact exceptionalAway_families_lt_of_fullFiberFacts Pcluster Gdegree
    threshold quota R0 (claim61Miss beta reducedK) Q density Mb P hbeta hbetaOne
    hreducedK (Sum.inl Q.A) (Sum.inl Q.B) rfl rfl Mb.card_le C.tree
    C.nU_two C.ghost C.ghost_large C.ghost_not_extreme C.ghost_numeric
    C.tree_card_three C.tree_order C.tree_not_contained_ghost C.targetU C.slackU
    C.ratio C.ratio_nonneg C.ratio_half hN C.slackU_pos C.branch_small_U
    C.threshold_U C.gammaU C.epsilonU C.d C.d_nonneg C.nP C.tree_card
    C.original_leaves C.hierarchyF C.hierarchyA C.targetP C.slackP
    C.targetP_bound C.slackP_pos C.branch_small_P C.gammaP C.epsilonP G
    C.unbalanced C.nonextreme hnot

/-- Lemma 6.11 with its exceptional-family hypotheses discharged internally
by the synchronized, source-faithful full-fiber Claim 6.15.  No copy,
embedding, continuation, or exceptional-cardinality conclusion is an input. -/
noncomputable def explicitMatchingDecompositionOfRichClaim61OfFullFiberFacts
    (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    (F : PreExceptionalFacts Pcluster Gdegree threshold quota R0 Q density N
      nTree targetB error lowerV1 upperV1 upperV2)
    (P : ZhaoForestPartition T globalRoot small)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (context : ExceptionalFullFiberContext Pcluster Gdegree threshold quota R0
      Q density N targetB hbeta hbetaOne
      (F.preliminaryReservedEdges Pcluster Gdegree threshold quota R0 Q
        density) P G)
    (hnot : ¬ T.IsContained G) :
    RichLemma611Output Pcluster Gdegree threshold quota R0
      (claim61Miss beta reducedK) Q density N (eta beta : ℝ)
      (lemma611TargetA beta nTree) targetB fb cutoff lowerV1 upperV1 upperV2
      (claim617Q beta reducedK) (2 * claim617Q beta reducedK)
      ((1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N)
      ((1 - 10 * Real.sqrt (lemma611D beta)) * nTree + 4 * N)
      ((eta beta : ℝ) * reducedK) := by
  let Mb := F.preliminaryReservedEdges Pcluster Gdegree threshold quota R0 Q
    density
  have hb := context.exceptionalBounds Pcluster Gdegree threshold quota R0 Q
    density N targetB hbeta hbetaOne Mb P G F.reducedK_large F.N_pos hnot
  exact explicitMatchingDecompositionOfRichClaim61OfExceptionalBounds hbeta hbetaOne Pcluster
    Gdegree threshold quota reducedK F.reducedK_eq F.reducedK_large R0 Q
    density N nTree targetB fb cutoff error lowerV1 upperV1 upperV2 F.N_pos
    F.nTree_pos F.error_nonneg F.targetB_nonneg F.A_edge_nonneg
    F.A_density_nonneg F.B_edge_nonneg F.A_edge_cap F.B_edge_cap F.degreeA
    F.degreeB F.density_adj_A F.density_adj_B F.B_total F.B_total_pos F.B_card
    F.n_covered F.cover F.error_small F.cluster_small F.lower F.upper
    F.total_card hb.1 hb.2

end Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication

#print axioms Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication.ExceptionalFullFiberContext.exceptionalBounds
#print axioms Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication.explicitMatchingDecompositionOfRichClaim61OfFullFiberFacts

namespace Erdos547b.ZhaoRichClaim61Lemma611

/-- Public Lemma-6.11 rich constructor.  Its exceptional bounds are proved
internally by the full-fiber Claim 6.15 rather than accepted as hypotheses. -/
noncomputable abbrev explicitMatchingDecompositionOfRichClaim61 :=
  @Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication.explicitMatchingDecompositionOfRichClaim61OfFullFiberFacts

end Erdos547b.ZhaoRichClaim61Lemma611

#print axioms Erdos547b.ZhaoRichClaim61Lemma611.explicitMatchingDecompositionOfRichClaim61
