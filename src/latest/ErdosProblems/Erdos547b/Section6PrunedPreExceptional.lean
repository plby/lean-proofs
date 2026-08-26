/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Section6PreExceptionalAssembly

/-!
# The pruned-host pre-exceptional package

The rich Claim-6.1 certificate initially uses the original degree graph,
whereas its density rows and subsequent regular-pair embeddings use Zhao's
low--low-edge deletion.  This file performs the exact certificate transport
and packages the source roots selected by the degree-form constructor.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoSection6PrunedPreExceptional

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSection6RichHierarchy
open Erdos547b.ZhaoSection6EventualParameters
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication
open Erdos547b.ZhaoSection6PreExceptionalAssembly

abbrev PrunedHost {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2)))
    [DecidableRel G.Adj] :=
  pruneSmallEdges G {v | n - 1 ≤ G.degree v}

abbrev Witness (β : ℚ) {n : ℕ}
    (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj] :=
  DegreeFormWitness (PrunedHost G)
    (regularityEpsilon β) (reducedDensity β) (section6M₀ β)
    (degreeFormBound (regularityEpsilon β) (section6M₀ β))

abbrev ClusterIndex {β : ℚ} {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))}
    [DecidableRel G.Adj] (W : Witness β G) :=
  {C // C ∈ W.partition.parts}

abbrev Pcluster {β : ℚ} {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))}
    [DecidableRel G.Adj] (W : Witness β G) :
    ClusterAssignment (Fin (2 * n - 2)) (ClusterIndex W) :=
  partitionAssignment W.exceptional W.partition

abbrev Rgraph {β : ℚ} {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))}
    [DecidableRel G.Adj] (W : Witness β G) : SimpleGraph (ClusterIndex W) :=
  regularityReducedGraph (PrunedHost G) (fun i : ClusterIndex W ↦ i.1)
    (regularityEpsilon β) (reducedDensity β)

def richQuotaW {β : ℚ} {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))}
    [DecidableRel G.Adj] (W : Witness β G) : ℕ :=
  richQuota (sigma β : ℝ) W.clusterSize

abbrev OriginalCertificate
    {β : ℚ} {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2)))
    [DecidableRel G.Adj] (W : Witness β G) :=
  RichClaim61Certificate (Pcluster W) G (n - 1) (richQuotaW W)
    (Rgraph W) (largeClustersAtLeast (Pcluster W) G (n - 1) (richQuotaW W))
    (claim61Miss β (paddedHalf (ClusterIndex W)))

abbrev PrunedCertificate
    {β : ℚ} {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2)))
    [DecidableRel G.Adj] (W : Witness β G) :=
  RichClaim61Certificate (Pcluster W) (PrunedHost G) (n - 1)
    (richQuotaW W) (Rgraph W)
    (largeClustersAtLeast (Pcluster W) (PrunedHost G) (n - 1)
      (richQuotaW W))
    (claim61Miss β (paddedHalf (ClusterIndex W)))

noncomputable def TransportedCertificate
    {β : ℚ} {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2)))
    [DecidableRel G.Adj] (W : Witness β G)
    (Q : OriginalCertificate G W) : PrunedCertificate G W :=
  transportRichClaim61CertificateToPruneSmallEdges
    (Pcluster W) G (n - 1) (richQuotaW W) (Rgraph W)
    (claim61Miss β (paddedHalf (ClusterIndex W))) Q

def SourceDensity
    {β : ℚ} {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))}
    [DecidableRel G.Adj] (W : Witness β G)
    (Q : PrunedCertificate G W)
    (zA zB : Fin (2 * n - 2)) :
    EvenPadding (ClusterIndex W) → EvenPadding (ClusterIndex W) → ℝ := by
  letI : DecidableRel W.graph.Adj := W.graph_decidable
  exact twoRootSourceDensity W.graph
    (padCluster (fun i : ClusterIndex W ↦ i.1)) (W.clusterSize : ℝ)
    (Sum.inl Q.A) (Sum.inl Q.B) zA zB

/-- The two selected source roots and the complete pre-exceptional
Lemma-6.11 package on the pruned degree graph. -/
structure PreExceptionalData
    {β : ℚ} {n : ℕ} {G : SimpleGraph (Fin (2 * n - 2))}
    [DecidableRel G.Adj] (W : Witness β G)
    (Q : PrunedCertificate G W) (targetB : ℝ) : Type where
  zA : Fin (2 * n - 2)
  zA_mem : zA ∈ Q.A₀
  zB : Fin (2 * n - 2)
  zB_mem : zB ∈ Q.B₀
  facts : PreExceptionalFacts
    (Pcluster W) (PrunedHost G) (n - 1) (richQuotaW W) (Rgraph W) Q
    (SourceDensity W Q zA zB) (W.clusterSize : ℝ) ((n - 1 : ℕ) : ℝ)
    targetB ((W.exceptional.card : ℝ) / 2)
    (paddedHalf (ClusterIndex W) -
      8 * claim617H β (paddedHalf (ClusterIndex W)))
    (paddedHalf (ClusterIndex W))
    (paddedHalf (ClusterIndex W) +
      8 * claim617H β (paddedHalf (ClusterIndex W)))

/-- A compact existential boundary for the transport.  Keeping the pruned
certificate as a field prevents callers from normalizing the transport
definition merely to state that the package exists. -/
structure Package
    {β : ℚ} {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2)))
    [DecidableRel G.Adj] (W : Witness β G)
    (Q : OriginalCertificate G W) (targetB : ℝ) : Type where
  pruned : PrunedCertificate G W
  pruned_eq : pruned = TransportedCertificate G W Q
  data : PreExceptionalData W pruned targetB

end Erdos547b.ZhaoSection6PrunedPreExceptional

#print axioms Erdos547b.ZhaoSection6PrunedPreExceptional.TransportedCertificate
