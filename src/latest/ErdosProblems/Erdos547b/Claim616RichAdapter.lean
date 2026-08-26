/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RichClaim61Lemma611
import ErdosProblems.Erdos547b.Claim616RichGraphTransport

/-!
# Equality transport from the rich Lemma 6.11 output to Claim 6.16

`RichLemma611Output` deliberately retains the literal Claim-6.7 certificate
on `padGraph R`.  The host embedding data, however, is stated for the
definitionally concrete graph
`regularityReducedGraph Hregular (padCluster cluster) epsilon density`.
These graphs are propositionally equal by `padGraph_regularityReducedGraph`.

This module performs that one equality elimination.  It does not ask the
caller for a second decomposition or an arbitrary graph isomorphism: the
matching decomposition remains `O.D`, and its host submatchings are merely
transported along the proved graph equality.  After eliminating that
equality, all transported objects reduce to the original ones.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616RichAdapter

open Finset SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoQuantitativeLargeClusters

universe u v

/-- The actual `RichLemma611Output` feeds Claim 6.16 directly.  The only
transport is along `padGraph_regularityReducedGraph`; there is no second
matching decomposition argument. -/
theorem exists_indexedHostSystem_of_richLemma611Output
    {B : Type u} {I : Type v}
    [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
    (Gdegree Hregular : SimpleGraph B)
    [DecidableRel Gdegree.Adj] [DecidableRel Hregular.Adj]
    (Pcluster : ClusterAssignment B I)
    (cluster : I → Finset B) (epsilon reducedDensity : ℚ)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (hregularSub : Hregular ≤ Gdegree)
    (threshold quota miss rhoK : ℕ)
    (hquota : 0 < quota) (hreducedDensity : 0 < reducedDensity)
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota
      (regularityReducedGraph Hregular cluster epsilon reducedDensity)
      (largeClustersAtLeast Pcluster Gdegree threshold quota) miss)
    (sourceDensity : EvenPadding I → EvenPadding I → ℝ)
    (N eta targetA targetB fb cutoff : ℝ)
    (lowerV1 upperV1 upperV2 mbEdgesBound mbBound : ℕ)
    (lowerA lowerB exceptionalBound : ℝ)
    (O : RichLemma611Output Pcluster Gdegree threshold quota
      (regularityReducedGraph Hregular cluster epsilon reducedDensity)
      miss Q sourceDensity N eta targetA targetB fb cutoff
      lowerV1 upperV1 upperV2 mbEdgesBound mbBound lowerA lowerB
      exceptionalBound)
    (heta : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hhierarchy : miss + mbBound ≤ rhoK)
    (hcross : rhoK * O.D.V2.card + O.D.V1.card * (9 * rhoK) <
      ((padGraph
        (regularityReducedGraph Hregular cluster epsilon reducedDensity)).interedges
          O.D.V1 O.D.V2).card) :
    let hEq := padGraph_regularityReducedGraph Hregular cluster epsilon
      reducedDensity hreducedDensity
    let Mout := transportSubgraph hEq O.D.Mout
    let Mb := transportSubgraph hEq O.D.Mb
    ∃ C : Finset (EvenPadding I),
      C ⊆ O.D.V1 ∧ C ⊆ Q.claim67.O ∧ C.card = rhoK ∧
      Nonempty (IndexedHostSystem Hregular (padCluster cluster) epsilon
        reducedDensity (Sum.inl Q.A) (Sum.inl Q.B) C Mout
        (O.D.V2 ∩ (matchingSupport Mout \ matchingSupport Mb)) rhoK
        (padAssignment Pcluster) threshold quota Gdegree) := by
  classical
  dsimp only
  let hEq := padGraph_regularityReducedGraph Hregular cluster epsilon
    reducedDensity hreducedDensity
  let transported := indexedHostDecompositionTransport
    (inferInstance : DecidableRel
      (padGraph
        (regularityReducedGraph Hregular cluster epsilon reducedDensity)).Adj)
    (inferInstance : DecidableRel
      (regularityReducedGraph Hregular (padCluster cluster) epsilon
        reducedDensity).Adj)
    hEq Q.claim67 sourceDensity N (Sum.inl Q.A) O.D eta
    O.min_subset_clean O.sourceDensityAdjA hcross
  let C67host := RichClaim61Certificate.hostClaim67 Gdegree Hregular
    Pcluster cluster epsilon reducedDensity threshold quota miss Q
    hreducedDensity
  have hC67 : transportClaim67Certificate hEq
      (inferInstance : DecidableRel
        (padGraph
          (regularityReducedGraph Hregular cluster epsilon reducedDensity)).Adj)
      (inferInstance : DecidableRel
        (regularityReducedGraph Hregular (padCluster cluster) epsilon
          reducedDensity).Adj)
      Q.claim67 = C67host := by
    rfl
  have hO : Q.claim67.O = C67host.O := by
    rw [← transported.certificate_O_eq]
    exact congrArg Claim67Certificate.O hC67
  let casted := indexedHostCertificateTransport transported C67host hC67 hO
  obtain ⟨C, hCV1, hCO, hCcard, hHost⟩ :=
    exists_indexedHostSystem_of_richClaim61_matchingDecomposition
      Gdegree Hregular Pcluster cluster epsilon reducedDensity hcluster
      hregularSub threshold quota miss rhoK hquota hreducedDensity Q
      sourceDensity N eta lowerV1 upperV1 upperV2 mbBound casted.target
      casted.min_subset_clean heta hetaHalf casted.sourceDensityAdj
      hhierarchy casted.crossing
  refine ⟨C, ?_, ?_, hCcard, ?_⟩
  · rw [← casted.V1_eq]
    exact hCV1
  · rw [hO]
    exact hCO
  · simpa only [casted.Mout_eq, casted.Mb_eq, casted.V2_eq] using hHost

end Erdos547b.ZhaoClaim616RichAdapter

#print axioms Erdos547b.ZhaoClaim616RichAdapter.exists_indexedHostSystem_of_richLemma611Output
