/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichDynamicRootLayout
import ErdosProblems.Erdos547b.Lemma58RootWitnessCleaning

/-!
# Source-witness cleaning for rich Claim 6.15

The two source-density rows are selected before the exceptional matching
families are known.  We therefore clean each distinguished reserve toward
every matching endpoint which is reduced-adjacent to that distinguished
cluster.  This target family depends only on the rich certificate, so the
selection is non-circular and covers every endpoint which can later carry a
positive source density.
-/

open scoped SimpleGraph BigOperators
noncomputable section

namespace Erdos547b.ZhaoClaim615RichSourceWitnessCleaning

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoLemma58RootWitnessCleaning
open Erdos547b.ZhaoRichClaim61Lemma611

universe v w

variable {Bv : Type v} {I : Type w}
variable [Fintype Bv] [DecidableEq Bv] [Fintype I] [DecidableEq I]
variable (Pcluster : ClusterAssignment Bv I)
variable (Gdegree : SimpleGraph Bv) [DecidableRel Gdegree.Adj]
variable (threshold quota : ℕ)
variable (R : SimpleGraph I) [DecidableRel R.Adj]
variable (miss : ℕ)
variable
  (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R
    (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)

/-- All possible matching endpoints, before any source-density-dependent
subfamily is selected. -/
abbrev SourceWitnessTarget :=
  {e : MatchingEdge Q.claim67.M // e ∈ allMatchingEdges Q.claim67.M} × Fin 2

/-- Padded reduced vertex of one distinguished source side. -/
def sourceWitnessRootCluster (side : Fin 2) : EvenPadding I :=
  Sum.inl (if side = 0 then Q.A else Q.B)

/-- Padded reduced vertex of one matching endpoint. -/
def sourceWitnessTargetCluster
    (t : SourceWitnessTarget Pcluster Gdegree threshold quota R miss Q) :
    EvenPadding I :=
  matchingEdgeEndpoint t.1.1.1 t.2

/-- Whole host cluster of one possible matching endpoint. -/
def sourceWitnessTargetWhole
    (t : SourceWitnessTarget Pcluster Gdegree threshold quota R miss Q) :
    Finset Bv :=
  padCluster (clusterVertices Pcluster)
    (sourceWitnessTargetCluster Pcluster Gdegree threshold quota R miss Q t)

/-- The matching endpoints reduced-adjacent to a distinguished source side.
Only these endpoints can later have positive source density. -/
def sourceWitnessTargets (side : Fin 2) :
    Finset (SourceWitnessTarget Pcluster Gdegree threshold quota R miss Q) :=
  Finset.univ.filter fun t ↦
    (padGraph R).Adj
      (sourceWitnessRootCluster Pcluster Gdegree threshold quota R miss Q side)
      (sourceWitnessTargetCluster Pcluster Gdegree threshold quota R miss Q t)

/-- There are at most two possible endpoint targets per matching edge. -/
theorem card_sourceWitnessTargets_le (side : Fin 2) :
    #(sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q side) ≤
      2 * #(allMatchingEdges Q.claim67.M) := by
  calc
    #(sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q side) ≤
        Fintype.card
          (SourceWitnessTarget Pcluster Gdegree threshold quota R miss Q) :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = 2 * #(allMatchingEdges Q.claim67.M) := by
      simp only [SourceWitnessTarget, Fintype.card_prod, Fintype.card_coe,
        Fintype.card_fin]
      omega

@[simp] theorem rootWholeSide_eq_padCluster (side : Fin 2) :
    rootWholeSide Pcluster Gdegree threshold quota R miss Q side =
      padCluster (clusterVertices Pcluster)
        (sourceWitnessRootCluster Pcluster Gdegree threshold quota R miss Q
          side) := by
  fin_cases side <;> rfl

/-- Upper-atypical witnesses in one distinguished reserve, simultaneously
over every possible later matching target. -/
def sourceWitnessHighBad
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho : ℝ) (side : Fin 2) : Finset Bv :=
  rootTargetHighBad G rho
    (rootWholeSide Pcluster Gdegree threshold quota R miss Q)
    (rootRawSide Pcluster Gdegree threshold quota R miss Q)
    (fun side ↦ sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q
      side)
    (sourceWitnessTargetWhole Pcluster Gdegree threshold quota R miss Q) side

/-- The source-witness bad set has the standard finite-union regularity
bound. -/
theorem card_sourceWitnessHighBad_le
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (side : Fin 2)
    (hrootLarge :
      rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
        quota)
    (hrho : rho ≤ 1) :
    (#(sourceWitnessHighBad Pcluster Gdegree threshold quota R miss Q G rho
      side) : ℝ) ≤
      (#(sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q side) :
          ℝ) *
        (rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q
          side)) := by
  apply card_rootTargetHighBad_le G rho
    (rootWholeSide Pcluster Gdegree threshold quota R miss Q)
    (rootRawSide Pcluster Gdegree threshold quota R miss Q)
    (fun side ↦ sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q
      side)
    (sourceWitnessTargetWhole Pcluster Gdegree threshold quota R miss Q) side
  · intro t ht
    have hadj := (Finset.mem_filter.mp ht).2
    have hp := H.pair_of_adj
      (sourceWitnessRootCluster Pcluster Gdegree threshold quota R miss Q side)
      (sourceWitnessTargetCluster Pcluster Gdegree threshold quota R miss Q t)
      hadj
    simpa only [rootWholeSide_eq_padCluster, sourceWitnessTargetWhole]
      using hp.1
  · exact rootRawSide_subset Pcluster Gdegree threshold quota R miss Q side
  · simpa only [card_rootRawSide] using hrootLarge
  · exact hrho

/-- A strict scalar union budget makes the upper-atypical set smaller than
the quantitative distinguished reserve. -/
theorem card_sourceWitnessHighBad_lt
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho density : ℝ)
    (H : ReducedPairRealization Pcluster R G rho density)
    (side : Fin 2)
    (hrootLarge :
      rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
        quota)
    (hrho : rho ≤ 1)
    (hbudget :
      (#(sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q side) :
          ℝ) *
          (rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q
            side)) < quota) :
    #(sourceWitnessHighBad Pcluster Gdegree threshold quota R miss Q G rho
      side) < quota := by
  have hreal := card_sourceWitnessHighBad_le Pcluster Gdegree threshold quota
    R miss Q G rho density H side hrootLarge hrho
  exact_mod_cast hreal.trans_lt hbudget

/-- A witness surviving the global upper cleaning has controlled degree
toward every reduced-adjacent matching endpoint. -/
theorem sourceWitness_target_degree_upper
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho : ℝ) (side : Fin 2) (z : Bv)
    (hzRaw : z ∈ rootRawSide Pcluster Gdegree threshold quota R miss Q side)
    (hzGood : z ∉ sourceWitnessHighBad Pcluster Gdegree threshold quota R
      miss Q G rho side)
    (t : SourceWitnessTarget Pcluster Gdegree threshold quota R miss Q)
    (hadj : (padGraph R).Adj
      (sourceWitnessRootCluster Pcluster Gdegree threshold quota R miss Q side)
      (sourceWitnessTargetCluster Pcluster Gdegree threshold quota R miss Q
        t)) :
    (#((sourceWitnessTargetWhole Pcluster Gdegree threshold quota R miss Q t).filter
      (G.Adj z)) : ℝ) ≤
      (G.edgeDensity
          (rootWholeSide Pcluster Gdegree threshold quota R miss Q side)
          (sourceWitnessTargetWhole Pcluster Gdegree threshold quota R miss Q
            t) + rho) *
        #(sourceWitnessTargetWhole Pcluster Gdegree threshold quota R miss Q
          t) := by
  apply rootWitness_target_degree_upper G rho
    (rootWholeSide Pcluster Gdegree threshold quota R miss Q)
    (rootRawSide Pcluster Gdegree threshold quota R miss Q)
    (fun side ↦ sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q
      side)
    (sourceWitnessTargetWhole Pcluster Gdegree threshold quota R miss Q)
    side z hzRaw hzGood t
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩

/-- Endpoint spelling of `sourceWitness_target_degree_upper`, convenient for
the physical matching families chosen after the source row. -/
theorem sourceWitness_matchingEndpoint_degree_upper
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (rho : ℝ) (side : Fin 2) (z : Bv)
    (hzRaw : z ∈ rootRawSide Pcluster Gdegree threshold quota R miss Q side)
    (hzGood : z ∉ sourceWitnessHighBad Pcluster Gdegree threshold quota R
      miss Q G rho side)
    (e : MatchingEdge Q.claim67.M) (he : e ∈ allMatchingEdges Q.claim67.M)
    (c : Fin 2)
    (hadj : (padGraph R).Adj
      (sourceWitnessRootCluster Pcluster Gdegree threshold quota R miss Q side)
      (matchingEdgeEndpoint e.1 c)) :
    (#((padCluster (clusterVertices Pcluster)
          (matchingEdgeEndpoint e.1 c)).filter (G.Adj z)) : ℝ) ≤
      (G.edgeDensity
          (rootWholeSide Pcluster Gdegree threshold quota R miss Q side)
          (padCluster (clusterVertices Pcluster)
            (matchingEdgeEndpoint e.1 c)) + rho) *
        #(padCluster (clusterVertices Pcluster)
          (matchingEdgeEndpoint e.1 c)) := by
  let t : SourceWitnessTarget Pcluster Gdegree threshold quota R miss Q :=
    (⟨e, he⟩, c)
  simpa only [t, sourceWitnessTargetWhole, sourceWitnessTargetCluster] using
    sourceWitness_target_degree_upper Pcluster Gdegree threshold quota R miss
      Q G rho side z hzRaw hzGood t hadj

/-- Multiplying a rooted density row by its nonzero normalization recovers
the literal target degree. -/
theorem mul_rootedSourceDensity_eq_degree
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (cluster : EvenPadding I → Finset Bv) (N : ℝ) (hN : N ≠ 0)
    (z : Bv) (j : EvenPadding I) :
    N * Erdos547b.ZhaoRichClaim61Lemma611.rootedSourceDensity G cluster N z j =
      (Erdos547EC2.degreeInto G z (cluster j) : ℝ) := by
  rw [Erdos547b.ZhaoRichClaim61Lemma611.rootedSourceDensity]
  field_simp

/-- The rich two-row source selector with the non-circular upper-typical
cleaning built in.  Its conclusion is the original Lemma-6.11 source package,
with the two additional witness-cleanliness certificates retained. -/
theorem exists_twoRootSourceDensity_of_richClaim61_witnessClean
    (Gsource : SimpleGraph Bv) [DecidableRel Gsource.Adj]
    (Ghost : SimpleGraph Bv) [DecidableRel Ghost.Adj]
    (cluster : I → Finset Bv)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (clusterSize loss : ℕ)
    (hquota : 0 < quota) (hclusterSize : 0 < clusterSize)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (hloss : DegreeLossAtMost Gdegree Gsource loss)
    (hrespect : EdgesRespectReducedGraph (padAssignment Pcluster) Gsource
      (padGraph R))
    (rho pairDensity : ℝ)
    (Hpair : ReducedPairRealization Pcluster R Ghost rho pairDensity)
    (hrho : rho ≤ 1)
    (hrootLarge : ∀ side,
      rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q side) ≤
        quota)
    (hbadBudget : ∀ side,
      (#(sourceWitnessTargets Pcluster Gdegree threshold quota R miss Q side) :
          ℝ) *
          (rho * #(rootWholeSide Pcluster Gdegree threshold quota R miss Q
            side)) < quota) :
    ∃ zA ∈ Q.A₀,
      zA ∉ sourceWitnessHighBad Pcluster Gdegree threshold quota R miss Q Ghost
        rho 0 ∧
      ∃ zB ∈ Q.B₀,
        zB ∉ sourceWitnessHighBad Pcluster Gdegree threshold quota R miss Q Ghost
          rho 1 ∧
        let Lp := padFinset
          (largeClustersAtLeast Pcluster Gdegree threshold quota)
        let A : EvenPadding I := Sum.inl Q.A
        let B : EvenPadding I := Sum.inl Q.B
        let sourceDensity := twoRootSourceDensity Gsource (padCluster cluster)
          (clusterSize : ℝ) A B zA zB
        (((threshold - loss - (exceptionalVertices
              (padAssignment Pcluster)).card - miss * clusterSize : ℕ) : ℝ) ≤
          sourceDegree Q.claim67.M Lp sourceDensity (clusterSize : ℝ) A
            (allMatchingEdges Q.claim67.M)) ∧
        (((threshold - loss - (exceptionalVertices
              (padAssignment Pcluster)).card - miss * clusterSize : ℕ) : ℝ) ≤
          sourceDegree Q.claim67.M Lp sourceDensity (clusterSize : ℝ) B
            (allMatchingEdges Q.claim67.M)) ∧
        (∀ x, 0 ≤ sourceDensity A x) ∧
        (∀ e : MatchingEdge Q.claim67.M,
          0 ≤ (clusterSize : ℝ) *
            (sourceDensity A (orientedEndpoint Q.claim67.M Lp e 0) +
              sourceDensity A (orientedEndpoint Q.claim67.M Lp e 1))) ∧
        (∀ e : MatchingEdge Q.claim67.M,
          0 ≤ (clusterSize : ℝ) *
            (sourceDensity B (orientedEndpoint Q.claim67.M Lp e 0) +
              sourceDensity B (orientedEndpoint Q.claim67.M Lp e 1))) ∧
        (∀ e : MatchingEdge Q.claim67.M,
          (clusterSize : ℝ) *
            (sourceDensity A (orientedEndpoint Q.claim67.M Lp e 0) +
              sourceDensity A (orientedEndpoint Q.claim67.M Lp e 1)) ≤
                2 * clusterSize) ∧
        (∀ e : MatchingEdge Q.claim67.M,
          (clusterSize : ℝ) *
            (sourceDensity B (orientedEndpoint Q.claim67.M Lp e 0) +
              sourceDensity B (orientedEndpoint Q.claim67.M Lp e 1)) ≤
                2 * clusterSize) ∧
        (∀ x, 0 < sourceDensity A x → (padGraph R).Adj A x) ∧
        (∀ x, 0 < sourceDensity B x → (padGraph R).Adj B x) := by
  have hbadA := card_sourceWitnessHighBad_lt Pcluster Gdegree threshold quota R
    miss Q Ghost rho pairDensity Hpair 0 (hrootLarge 0) hrho (hbadBudget 0)
  have hbadB := card_sourceWitnessHighBad_lt Pcluster Gdegree threshold quota R
    miss Q Ghost rho pairDensity Hpair 1 (hrootLarge 1) hrho (hbadBudget 1)
  have h := exists_twoRootSourceDensity_of_richClaim61 Pcluster Gdegree Gsource R
    cluster hcluster threshold quota miss clusterSize loss hquota hclusterSize
    hclusterCard hloss hrespect
    (sourceWitnessHighBad Pcluster Gdegree threshold quota R miss Q Ghost rho 0)
    (sourceWitnessHighBad Pcluster Gdegree threshold quota R miss Q Ghost rho 1)
    hbadA hbadB Q
  simpa only [rootRawSide, Fin.isValue] using h

end Erdos547b.ZhaoClaim615RichSourceWitnessCleaning

#print axioms Erdos547b.ZhaoClaim615RichSourceWitnessCleaning.card_sourceWitnessHighBad_le
#print axioms Erdos547b.ZhaoClaim615RichSourceWitnessCleaning.card_sourceWitnessTargets_le
#print axioms Erdos547b.ZhaoClaim615RichSourceWitnessCleaning.card_sourceWitnessHighBad_lt
#print axioms Erdos547b.ZhaoClaim615RichSourceWitnessCleaning.sourceWitness_target_degree_upper
#print axioms Erdos547b.ZhaoClaim615RichSourceWitnessCleaning.sourceWitness_matchingEndpoint_degree_upper
#print axioms Erdos547b.ZhaoClaim615RichSourceWitnessCleaning.mul_rootedSourceDensity_eq_degree
#print axioms Erdos547b.ZhaoClaim615RichSourceWitnessCleaning.exists_twoRootSourceDensity_of_richClaim61_witnessClean
