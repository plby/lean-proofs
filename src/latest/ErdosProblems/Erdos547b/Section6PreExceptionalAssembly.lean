/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Claim615RichSourceWitnessCleaning
import ErdosProblems.Erdos547b.RichClaim61Lemma611FullFiberApplication

/-!
# Assembling the pre-exceptional Lemma-6.11 data

The rich Claim-6.1 source selector already proves every graph-dependent fact
about the two distinguished density rows.  This file separates those facts
from the scalar estimates which only involve the eventual Section-6
parameters, and then packages the two layers into `PreExceptionalFacts`.

Keeping this assembly explicit is useful for the final stability proof: the
choice of the two source vertices is made only once, with the global
source-witness cleaning, while all later matching constructions use the same
two density rows.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoSection6PreExceptionalAssembly

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoDegreeFormQuantitative
open Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim617BranchCount
open Erdos547b.ZhaoClaim616
open Erdos547b.ZhaoClaim61RichFull
open Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoRoundedScales
open Erdos547b.ZhaoSection6EventualParameters
open Erdos547b.ZhaoRichClaim61Lemma611
open Erdos547b.ZhaoClaim615RichCoordinatePairFacts
open Erdos547b.ZhaoClaim615RichDynamicRootLayout
open Erdos547b.ZhaoClaim615RichSourceWitnessCleaning
open Erdos547b.ZhaoRichClaim61Lemma611FullFiberApplication

universe v w

variable {V : Type v} {I : Type w}
variable [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- The common lower bound supplied by the rich Claim-6.1 degree argument
after cleaning the host graph. -/
def richSourceLower
    (Pcluster : ClusterAssignment V I)
    (threshold loss clusterSize : ℕ) (beta : ℚ) (reducedK : ℕ) : ℝ :=
  (((threshold - loss - (exceptionalVertices (padAssignment Pcluster)).card -
      claim61Miss beta reducedK * clusterSize : ℕ) : ℝ))

/-- A rich Claim-6.1 certificate depends on its degree graph only through the
statement that the two exact root reservoirs consist of high-degree
vertices.  Hence it transports across graphs with the same threshold set. -/
def transportRichClaim61CertificateDegreeGraph
    (Pcluster : ClusterAssignment V I)
    (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (threshold quota : ℕ)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (L : Finset I) (miss : ℕ)
    (Q : RichClaim61Certificate Pcluster G threshold quota R0 L miss)
    (hhigh : ∀ v, threshold ≤ G.degree v ↔ threshold ≤ G'.degree v) :
    RichClaim61Certificate Pcluster G' threshold quota R0 L miss where
  A := Q.A
  B := Q.B
  adj := Q.adj
  A_mem := Q.A_mem
  B_mem := Q.B_mem
  A₀ := Q.A₀
  B₀ := Q.B₀
  A₀_subset := Q.A₀_subset
  B₀_subset := Q.B₀_subset
  A₀_card := Q.A₀_card
  B₀_card := Q.B₀_card
  A₀_high v hv := (hhigh v).mp (Q.A₀_high v hv)
  B₀_high v hv := (hhigh v).mp (Q.B₀_high v hv)
  claim67 := Q.claim67
  A_in_claim67O := Q.A_in_claim67O
  B_in_claim67O := Q.B_in_claim67O
  matching_edge_meets_large := Q.matching_edge_meets_large

/-- The quantitative large-cluster family is determined solely by the
threshold-degree vertex set. -/
theorem largeClustersAtLeast_eq_of_highDegree_iff
    (Pcluster : ClusterAssignment V I)
    (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (threshold quota : ℕ)
    (hhigh : ∀ v, threshold ≤ G.degree v ↔ threshold ≤ G'.degree v) :
    largeClustersAtLeast Pcluster G threshold quota =
      largeClustersAtLeast Pcluster G' threshold quota := by
  classical
  have hvertices : highDegreeVertices G threshold =
      highDegreeVertices G' threshold := by
    ext v
    simp only [mem_highDegreeVertices]
    exact hhigh v
  simp only [largeClustersAtLeast, largeVertexReservoir, hvertices]
  rfl

/-- Canonical version of `transportDegreeGraph`, with the large-cluster
family rewritten to the target graph. -/
noncomputable def transportRichClaim61CertificateDegreeGraphCanonical
    (Pcluster : ClusterAssignment V I)
    (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (threshold quota : ℕ)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (miss : ℕ)
    (Q : RichClaim61Certificate Pcluster G threshold quota R0
      (largeClustersAtLeast Pcluster G threshold quota) miss)
    (hhigh : ∀ v, threshold ≤ G.degree v ↔ threshold ≤ G'.degree v) :
    RichClaim61Certificate Pcluster G' threshold quota R0
      (largeClustersAtLeast Pcluster G' threshold quota) miss := by
  rw [← largeClustersAtLeast_eq_of_highDegree_iff Pcluster G G' threshold
    quota hhigh]
  exact transportRichClaim61CertificateDegreeGraph Pcluster G G' threshold
    quota R0 (largeClustersAtLeast Pcluster G threshold quota) miss Q hhigh

/-- Specialization of certificate transport to Zhao's deletion of all
low--low edges. -/
noncomputable def transportRichClaim61CertificateToPruneSmallEdges
    (Pcluster : ClusterAssignment V I)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (threshold quota : ℕ)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    (miss : ℕ)
    (Q : RichClaim61Certificate Pcluster G threshold quota R0
      (largeClustersAtLeast Pcluster G threshold quota) miss) :
    RichClaim61Certificate Pcluster
      (pruneSmallEdges G {v | threshold ≤ G.degree v}) threshold quota R0
      (largeClustersAtLeast Pcluster
        (pruneSmallEdges G {v | threshold ≤ G.degree v}) threshold quota)
      miss :=
  transportRichClaim61CertificateDegreeGraphCanonical Pcluster G
    (pruneSmallEdges G {v | threshold ≤ G.degree v}) threshold quota R0 miss Q
    (fun v ↦ (highDegree_iff_pruneSmallEdges_highDegree G threshold v).symm)

/-- The explicit degree-form hierarchy leaves the full Lemma-6.11 source
margin after charging cleanup, exceptional vertices, missed clusters, and
the four-cluster distinguished-source reserve. -/
theorem degreeForm_degreeTarget_le_richSourceLower
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {N q : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon beta) (reducedDensity beta)
      (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : N = 2 * q) (hN : section6N₀ beta ≤ N) :
    let I := {Q // Q ∈ W.partition.parts}
    let Pcluster : ClusterAssignment (Fin N) I :=
      partitionAssignment W.exceptional W.partition
    let reducedK := paddedHalf I
    (1 - 10 * Real.sqrt (lemma611D beta)) * (q : ℝ) +
        4 * (W.clusterSize : ℝ) ≤
      richSourceLower Pcluster q W.loss W.clusterSize beta reducedK := by
  classical
  let I := {Q // Q ∈ W.partition.parts}
  let Pcluster : ClusterAssignment (Fin N) I :=
    partitionAssignment W.exceptional W.partition
  let reducedK := paddedHalf I
  dsimp only
  have hbounds := degreeForm_preExceptional_bounds hbeta hbetaOne W hNq hN
  dsimp only at hbounds
  have hcleanup := hbounds.2.2.2.2
  have hq : 0 < q := by
    subst N
    have hpositive : 0 < 5 * W.ordinaryParts :=
      Nat.mul_pos (by norm_num) W.ordinaryParts_pos
    have hhostPositive : 0 < 2 * q :=
      lt_of_lt_of_le hpositive W.five_ordinaryParts_le_host
    omega
  have hfourthSmall : (fourthRootD beta : ℝ) ≤ 1 / 1000 := by
    have h := fourthRootD_le_eta_div_1000 hbeta hbetaOne
    have heta : (eta beta : ℝ) ≤ 1 :=
      (eta_le_rho_div_1000 hbeta hbetaOne).trans (by
        have hr : (rho beta : ℝ) ≤ 1 := by
          exact_mod_cast rho_le_one hbeta hbetaOne
        linarith)
    linarith
  have hcleanupQ :
      ((W.loss + W.exceptional.card +
          claim61Miss beta reducedK * W.clusterSize +
          4 * W.clusterSize : ℕ) : ℝ) < q := by
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    exact hcleanup.trans (by nlinarith)
  have hcleanupNat :
      W.loss + W.exceptional.card +
          claim61Miss beta reducedK * W.clusterSize +
          4 * W.clusterSize < q := by
    exact_mod_cast hcleanupQ
  have hbaseLe : W.loss + W.exceptional.card +
      claim61Miss beta reducedK * W.clusterSize ≤ q := by omega
  have hsub :
      q - W.loss - W.exceptional.card -
          claim61Miss beta reducedK * W.clusterSize =
        q - (W.loss + W.exceptional.card +
          claim61Miss beta reducedK * W.clusterSize) := by
    omega
  rw [richSourceLower]
  simp only [exceptionalVertices_padAssignment,
    exceptionalVertices_partitionAssignment]
  rw [hsub, Nat.cast_sub hbaseLe, sqrt_lemma611D hbeta, lemma611DSqrt]
  push_cast at hcleanup ⊢
  nlinarith

/-- In particular, the canonical rich source lower bound is strictly
positive. -/
theorem degreeForm_richSourceLower_pos
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {N q : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (regularityEpsilon beta) (reducedDensity beta)
      (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : N = 2 * q) (hN : section6N₀ beta ≤ N) :
    let I := {Q // Q ∈ W.partition.parts}
    let Pcluster : ClusterAssignment (Fin N) I :=
      partitionAssignment W.exceptional W.partition
    let reducedK := paddedHalf I
    0 < richSourceLower Pcluster q W.loss W.clusterSize beta reducedK := by
  classical
  let I := {Q // Q ∈ W.partition.parts}
  let Pcluster : ClusterAssignment (Fin N) I :=
    partitionAssignment W.exceptional W.partition
  let reducedK := paddedHalf I
  dsimp only
  have hlower := degreeForm_degreeTarget_le_richSourceLower
    hbeta hbetaOne W hNq hN
  have hq : 0 < q := by
    subst N
    have hpositive : 0 < 5 * W.ordinaryParts :=
      Nat.mul_pos (by norm_num) W.ordinaryParts_pos
    have hhostPositive : 0 < 2 * q :=
      lt_of_lt_of_le hpositive W.five_ordinaryParts_le_host
    omega
  have hfourthSmall : (fourthRootD beta : ℝ) ≤ 1 / 1000 := by
    have h := fourthRootD_le_eta_div_1000 hbeta hbetaOne
    have heta : (eta beta : ℝ) ≤ 1 :=
      (eta_le_rho_div_1000 hbeta hbetaOne).trans (by
        have hr : (rho beta : ℝ) ≤ 1 := by
          exact_mod_cast rho_le_one hbeta hbetaOne
        linarith)
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [sqrt_lemma611D hbeta] at hlower
  have htargetPos : 0 <
      (1 - 10 * (fourthRootD beta : ℝ)) * q +
        4 * (W.clusterSize : ℝ) := by
    have hm : (0 : ℝ) ≤ W.clusterSize := by positivity
    nlinarith
  exact htargetPos.trans_le hlower

/-- Taking one cluster as the preliminary `B`-row target satisfies both
the total-capacity and greedy-submatching estimates.  This is the canonical
choice used below: it is positive, independent of the eventual forest
partition, and small compared with the `sqrt d` matching budget. -/
theorem degreeForm_clusterSize_B_bounds
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (Gdegree : SimpleGraph (Fin Nhost)) [DecidableRel Gdegree.Adj]
    (quota : ℕ)
    (R0 : SimpleGraph {Q // Q ∈ W.partition.parts})
    [DecidableRel R0.Adj]
    (Q : RichClaim61Certificate
      (partitionAssignment W.exceptional W.partition) Gdegree q quota R0
      (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota)
      (claim61Miss beta (paddedHalf {Q // Q ∈ W.partition.parts}))) :
    let k := paddedHalf {Q // Q ∈ W.partition.parts}
    let sourceLower := richSourceLower
      (partitionAssignment W.exceptional W.partition) q W.loss
        W.clusterSize beta k
    0 < (W.clusterSize : ℝ) ∧
      (W.clusterSize : ℝ) ≤ sourceLower ∧
      ((allMatchingEdges Q.claim67.M).card : ℝ) *
          ((W.clusterSize : ℝ) + 2 * (W.clusterSize : ℝ)) ≤
        (claim617Q beta k : ℝ) * sourceLower := by
  classical
  let I := {Q // Q ∈ W.partition.parts}
  let k := paddedHalf I
  let sourceLower := richSourceLower
    (partitionAssignment W.exceptional W.partition) q W.loss W.clusterSize
      beta k
  dsimp only
  have hbounds := degreeForm_preExceptional_bounds hbeta hbetaOne W hNq
    hNhost
  dsimp only at hbounds
  have hmSmall := hbounds.2.2.2.1
  have htarget := degreeForm_degreeTarget_le_richSourceLower
    hbeta hbetaOne W hNq hNhost
  have hlowerPos := degreeForm_richSourceLower_pos
    hbeta hbetaOne W hNq hNhost
  have hmPos : (0 : ℝ) < W.clusterSize := by
    exact_mod_cast W.clusterSize_pos
  have hqNonneg : (0 : ℝ) ≤ q := by positivity
  have hsPos : (0 : ℝ) < (fourthRootD beta : ℝ) := by
    exact_mod_cast fourthRootD_pos hbeta
  have hsSmall : (fourthRootD beta : ℝ) ≤ 1 / 1000 := by
    have h := fourthRootD_le_eta_div_1000 hbeta hbetaOne
    have heta : (eta beta : ℝ) ≤ 1 :=
      (eta_le_rho_div_1000 hbeta hbetaOne).trans (by
        have hr : (rho beta : ℝ) ≤ 1 := by
          exact_mod_cast rho_le_one hbeta hbetaOne
        linarith)
    linarith
  have hsigmaLe := sigma_le_fourthRootD hbeta hbetaOne
  have hsigmaNonneg : (0 : ℝ) ≤ (sigma beta : ℝ) := by
    exact_mod_cast (sigma_pos hbeta).le
  have hmLeFourth : (W.clusterSize : ℝ) ≤
      (fourthRootD beta : ℝ) * q / 400 := by
    have hmul := mul_le_mul_of_nonneg_right hsigmaLe hqNonneg
    nlinarith
  have hlower99 : (99 / 100 : ℝ) * q ≤
      richSourceLower (partitionAssignment W.exceptional W.partition) q
        W.loss W.clusterSize beta
        (paddedHalf {Q // Q ∈ W.partition.parts}) := by
    rw [sqrt_lemma611D hbeta, lemma611DSqrt] at htarget
    have hmNonneg : (0 : ℝ) ≤ W.clusterSize := hmPos.le
    nlinarith
  have hthreeM : 3 * (W.clusterSize : ℝ) ≤
      (fourthRootD beta : ℝ) *
        richSourceLower (partitionAssignment W.exceptional W.partition) q
          W.loss W.clusterSize beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) := by
    have hscaled := mul_le_mul_of_nonneg_left hlower99 hsPos.le
    nlinarith [hmLeFourth]
  have hfourthLower : (fourthRootD beta : ℝ) *
      richSourceLower (partitionAssignment W.exceptional W.partition) q
        W.loss W.clusterSize beta
        (paddedHalf {Q // Q ∈ W.partition.parts}) ≤
      richSourceLower (partitionAssignment W.exceptional W.partition) q
        W.loss W.clusterSize beta
        (paddedHalf {Q // Q ∈ W.partition.parts}) := by
    have hfourthOne : (fourthRootD beta : ℝ) ≤ 1 :=
      hsSmall.trans (by norm_num)
    have hproduct := mul_nonneg (sub_nonneg.mpr hfourthOne) hlowerPos.le
    nlinarith
  have hmLower : (W.clusterSize : ℝ) ≤
      richSourceLower (partitionAssignment W.exceptional W.partition) q
        W.loss W.clusterSize beta
        (paddedHalf {Q // Q ∈ W.partition.parts}) := by
    nlinarith [hthreeM.trans hfourthLower]
  have hcardNat : (allMatchingEdges Q.claim67.M).card ≤
      paddedHalf {Q // Q ∈ W.partition.parts} :=
    allMatchingEdges_card_le_paddedHalf Q.claim67.M Q.claim67.isMatching
      (padFinset (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota))
  have hcard : ((allMatchingEdges Q.claim67.M).card : ℝ) ≤
      paddedHalf {Q // Q ∈ W.partition.parts} := by
    exact_mod_cast hcardNat
  have hround : (fourthRootD beta : ℝ) *
      paddedHalf {Q // Q ∈ W.partition.parts} ≤
        (claim617Q beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) : ℝ) :=
    le_upperScale_cast _
  refine ⟨hmPos, hmLower, ?_⟩
  calc
    ((allMatchingEdges Q.claim67.M).card : ℝ) *
          ((W.clusterSize : ℝ) + 2 * (W.clusterSize : ℝ)) =
        ((allMatchingEdges Q.claim67.M).card : ℝ) *
          (3 * (W.clusterSize : ℝ)) := by ring
    _ ≤ (paddedHalf {Q // Q ∈ W.partition.parts} : ℝ) *
          (3 * (W.clusterSize : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ ((fourthRootD beta : ℝ) *
          paddedHalf {Q // Q ∈ W.partition.parts}) *
        richSourceLower (partitionAssignment W.exceptional W.partition) q
          W.loss W.clusterSize beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) := by
      have hmul := mul_le_mul_of_nonneg_left hthreeM
        (show (0 : ℝ) ≤ paddedHalf {Q // Q ∈ W.partition.parts} by
          positivity)
      nlinarith
    _ ≤ (claim617Q beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) : ℝ) *
        richSourceLower (partitionAssignment W.exceptional W.partition) q
          W.loss W.clusterSize beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) :=
      mul_le_mul_of_nonneg_right hround hlowerPos.le

/-- A generic reduction for the preliminary `B` reservation.  Once the
tree-dependent target plus the one-edge overshoot is below a
`fourthRootD` fraction of the source lower bound, the target and cardinality
premises of the decreasing-prefix constructor follow automatically. -/
theorem degreeForm_target_B_bounds
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (Gdegree : SimpleGraph (Fin Nhost)) [DecidableRel Gdegree.Adj]
    (quota : ℕ)
    (R0 : SimpleGraph {Q // Q ∈ W.partition.parts})
    [DecidableRel R0.Adj]
    (Q : RichClaim61Certificate
      (partitionAssignment W.exceptional W.partition) Gdegree q quota R0
      (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota)
      (claim61Miss beta (paddedHalf {Q // Q ∈ W.partition.parts})))
    (targetB : ℝ) (htargetB : 0 ≤ targetB)
    (hscaled : targetB + 2 * (W.clusterSize : ℝ) ≤
      (fourthRootD beta : ℝ) *
        richSourceLower (partitionAssignment W.exceptional W.partition) q
          W.loss W.clusterSize beta
          (paddedHalf {Q // Q ∈ W.partition.parts})) :
    targetB ≤
        richSourceLower (partitionAssignment W.exceptional W.partition) q
          W.loss W.clusterSize beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) ∧
      ((allMatchingEdges Q.claim67.M).card : ℝ) *
          (targetB + 2 * (W.clusterSize : ℝ)) ≤
        (claim617Q beta
            (paddedHalf {Q // Q ∈ W.partition.parts}) : ℝ) *
          richSourceLower (partitionAssignment W.exceptional W.partition) q
            W.loss W.clusterSize beta
            (paddedHalf {Q // Q ∈ W.partition.parts}) := by
  let k := paddedHalf {Q // Q ∈ W.partition.parts}
  let sourceLower := richSourceLower
    (partitionAssignment W.exceptional W.partition) q W.loss W.clusterSize
      beta k
  have hlowerPos : 0 < sourceLower := by
    simpa only [sourceLower, k] using
      (degreeForm_richSourceLower_pos hbeta hbetaOne W hNq hNhost)
  have hfourthOne : (fourthRootD beta : ℝ) ≤ 1 :=
    (fourthRootD_le_eta_div_1000 hbeta hbetaOne).trans <| by
      have heta := eta_le_rho_div_1000 hbeta hbetaOne
      have hrho : (rho beta : ℝ) ≤ 1 := by
        exact_mod_cast rho_le_one hbeta hbetaOne
      linarith
  have htargetLower : targetB ≤ sourceLower := by
    have hscaled' : targetB ≤ (fourthRootD beta : ℝ) * sourceLower := by
      linarith [show (0 : ℝ) ≤ W.clusterSize by positivity]
    have hproduct : (fourthRootD beta : ℝ) * sourceLower ≤ sourceLower :=
      (mul_le_iff_le_one_left hlowerPos).2 hfourthOne
    exact hscaled'.trans hproduct
  have hcardNat : (allMatchingEdges Q.claim67.M).card ≤ k :=
    allMatchingEdges_card_le_paddedHalf Q.claim67.M Q.claim67.isMatching
      (padFinset (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota))
  have hcard : ((allMatchingEdges Q.claim67.M).card : ℝ) ≤ k := by
    exact_mod_cast hcardNat
  have htargetCap : 0 ≤ targetB + 2 * (W.clusterSize : ℝ) := by positivity
  have hround : (fourthRootD beta : ℝ) * k ≤
      (claim617Q beta k : ℝ) := le_upperScale_cast _
  refine ⟨by simpa only [sourceLower, k] using htargetLower, ?_⟩
  calc
    ((allMatchingEdges Q.claim67.M).card : ℝ) *
          (targetB + 2 * (W.clusterSize : ℝ)) ≤
        (k : ℝ) * (targetB + 2 * (W.clusterSize : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard htargetCap
    _ ≤ (k : ℝ) * ((fourthRootD beta : ℝ) * sourceLower) :=
      mul_le_mul_of_nonneg_left hscaled (by positivity)
    _ = ((fourthRootD beta : ℝ) * k) * sourceLower := by ring
    _ ≤ (claim617Q beta k : ℝ) * sourceLower :=
      mul_le_mul_of_nonneg_right hround hlowerPos.le

/-- In the small-`f_b` branch, Zhao's literal reservation target
`f_b + 3 * gamma * n` plus the one-edge overshoot lies below the generic
`fourthRootD` source allowance. -/
theorem degreeForm_smallMinor_target_scaled
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (minorMass : ℝ) (hminorMass : 0 ≤ minorMass)
    (hminorSmall : minorMass ≤
      (fourthRootD beta : ℝ) / 2 * q) :
    minorMass + 3 * (embeddingGamma beta : ℝ) * q +
        2 * (W.clusterSize : ℝ) ≤
      (fourthRootD beta : ℝ) *
        richSourceLower (partitionAssignment W.exceptional W.partition) q
          W.loss W.clusterSize beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) := by
  let x : ℝ := (fourthRootD beta : ℝ)
  have hx0 : 0 < x := by
    dsimp only [x]
    exact_mod_cast fourthRootD_pos hbeta
  have hxSmall : x ≤ 1 / 1000 := by
    dsimp only [x]
    have h := fourthRootD_le_eta_div_1000 hbeta hbetaOne
    have heta := eta_le_rho_div_1000 hbeta hbetaOne
    have hrho : (rho beta : ℝ) ≤ 1 := by
      exact_mod_cast rho_le_one hbeta hbetaOne
    linarith
  have hsigma : (sigma beta : ℝ) = x ^ 2 := by
    simp only [sigma, x]
    push_cast
    rfl
  have hgamma : (embeddingGamma beta : ℝ) = x ^ 4 / 1000 := by
    simp only [embeddingGamma, sigma, x]
    push_cast
    ring
  have hgammaLe : (embeddingGamma beta : ℝ) ≤ x ^ 2 / 1000 := by
    rw [hgamma]
    have hx1 : x ≤ 1 := hxSmall.trans (by norm_num)
    have hsq : x ^ 4 ≤ x ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr
        (show x ^ 2 ≤ 1 by nlinarith [sq_nonneg x]))]
    linarith
  have hbounds := degreeForm_preExceptional_bounds hbeta hbetaOne W hNq
    hNhost
  dsimp only at hbounds
  have hcluster := hbounds.2.2.2.1
  rw [hsigma] at hcluster
  have hsource := degreeForm_degreeTarget_le_richSourceLower
    hbeta hbetaOne W hNq hNhost
  rw [sqrt_lemma611D hbeta, lemma611DSqrt] at hsource
  change (1 - 10 * x) * (q : ℝ) + 4 * (W.clusterSize : ℝ) ≤ _
    at hsource
  have hsourceMul := mul_le_mul_of_nonneg_left hsource hx0.le
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hxq0 : 0 ≤ x * (q : ℝ) := mul_nonneg hx0.le hq0
  have hxxq : x ^ 2 * (q : ℝ) ≤ (1 / 1000 : ℝ) * (x * q) := by
    have h := mul_le_mul_of_nonneg_right hxSmall hxq0
    nlinarith
  have hgammaQ := mul_le_mul_of_nonneg_right hgammaLe hq0
  have hminorSmall' : minorMass ≤ x / 2 * q := by
    simpa only [x] using hminorSmall
  nlinarith [show (0 : ℝ) ≤ W.clusterSize by positivity]

/-- Zhao's preliminary `B`-row target in the small-minor-side branch. -/
def smallMinorTarget (beta : ℚ) (q : ℕ) (minorMass : ℝ) : ℝ :=
  minorMass + 3 * (embeddingGamma beta : ℝ) * q

/-- Ready-to-use target, lower-bound, and cardinality facts for the literal
small-`f_b` reservation. -/
theorem degreeForm_smallMinor_B_bounds
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (Gdegree : SimpleGraph (Fin Nhost)) [DecidableRel Gdegree.Adj]
    (quota : ℕ)
    (R0 : SimpleGraph {Q // Q ∈ W.partition.parts})
    [DecidableRel R0.Adj]
    (Q : RichClaim61Certificate
      (partitionAssignment W.exceptional W.partition) Gdegree q quota R0
      (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota)
      (claim61Miss beta (paddedHalf {Q // Q ∈ W.partition.parts})))
    (minorMass : ℝ) (hminorMass : 0 ≤ minorMass)
    (hminorSmall : minorMass ≤
      (fourthRootD beta : ℝ) / 2 * q) :
    0 ≤ smallMinorTarget beta q minorMass ∧
      smallMinorTarget beta q minorMass ≤
        richSourceLower (partitionAssignment W.exceptional W.partition) q
          W.loss W.clusterSize beta
          (paddedHalf {Q // Q ∈ W.partition.parts}) ∧
      ((allMatchingEdges Q.claim67.M).card : ℝ) *
          (smallMinorTarget beta q minorMass +
            2 * (W.clusterSize : ℝ)) ≤
        (claim617Q beta
            (paddedHalf {Q // Q ∈ W.partition.parts}) : ℝ) *
          richSourceLower (partitionAssignment W.exceptional W.partition) q
            W.loss W.clusterSize beta
            (paddedHalf {Q // Q ∈ W.partition.parts}) := by
  have htarget0 : 0 ≤ smallMinorTarget beta q minorMass := by
    unfold smallMinorTarget
    have hgamma : (0 : ℝ) ≤ (embeddingGamma beta : ℝ) := by
      exact_mod_cast (embeddingGamma_pos hbeta).le
    positivity
  have hscaled := degreeForm_smallMinor_target_scaled hbeta hbetaOne W hNq
    hNhost minorMass hminorMass hminorSmall
  have hb := degreeForm_target_B_bounds hbeta hbetaOne W hNq hNhost Gdegree
    quota R0 Q (smallMinorTarget beta q minorMass) htarget0 (by
      simpa only [smallMinorTarget, add_assoc] using hscaled)
  exact ⟨htarget0, hb.1, hb.2⟩

/-- The state-independent estimates still needed after the two source rows
have been selected.  Only `lower` mentions the selected density: it is the
literal finite-cardinality implication needed by Lemma 6.11. -/
structure PreExceptionalScalarFacts
    (Pcluster : ClusterAssignment V I)
    (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
    (threshold quota : ℕ)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    {beta : ℚ} {reducedK : ℕ}
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (largeClustersAtLeast Pcluster Gdegree threshold quota)
      (claim61Miss beta reducedK))
    (density : EvenPadding I → EvenPadding I → ℝ)
    (clusterSize loss : ℕ)
    (nTree targetB error : ℝ)
    (lowerV1 upperV1 upperV2 : ℕ) : Prop where
  reducedK_eq : reducedK = paddedHalf I
  reducedK_large : section6K₀ beta ≤ reducedK
  nTree_pos : 0 < nTree
  error_nonneg : 0 ≤ error
  targetB_nonneg : 0 ≤ targetB
  degree_target_le_lower :
    (1 - 10 * Real.sqrt (lemma611D beta)) * nTree +
        4 * (clusterSize : ℝ) ≤
      richSourceLower Pcluster threshold loss clusterSize beta reducedK
  targetB_le_lower :
    targetB ≤ richSourceLower Pcluster threshold loss clusterSize beta reducedK
  source_lower_pos :
    0 < richSourceLower Pcluster threshold loss clusterSize beta reducedK
  B_card_lower :
    ((allMatchingEdges Q.claim67.M).card : ℝ) *
        (targetB + 2 * (clusterSize : ℝ)) ≤
      (claim617Q beta reducedK : ℝ) *
        richSourceLower Pcluster threshold loss clusterSize beta reducedK
  n_covered :
    nTree ≤ (reducedK : ℝ) * (clusterSize : ℝ) + error
  cover : (reducedK : ℝ) * (clusterSize : ℝ) ≤
    nTree + (clusterSize : ℝ)
  error_small : error ≤ (sigma beta : ℝ) * nTree
  cluster_small : (clusterSize : ℝ) ≤ 3 * (sigma beta : ℝ) * nTree
  lower : ∀ S : Finset (MatchingEdge Q.claim67.M),
    S ⊆ allMatchingEdges Q.claim67.M →
    lemma611TargetA beta nTree < sourceDegree Q.claim67.M
      (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
      density (clusterSize : ℝ) (Sum.inl Q.A) S →
        lowerV1 ≤ 2 * S.card
  upper : 2 * minEdgeCap reducedK ≤ upperV1
  total_card : Fintype.card (EvenPadding I) ≤ lowerV1 + upperV2

/-- Canonical scalar package for an actual degree-form witness.  The only
remaining caller inputs concern the B-row target, since that target is fixed
later from the chosen tree partition.  The A-row cardinality implication is
proved here with the necessary one-cluster parity slack from odd padding. -/
theorem preExceptionalScalarFacts_of_degreeForm
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (Gdegree : SimpleGraph (Fin Nhost)) [DecidableRel Gdegree.Adj]
    (quota : ℕ)
    (R0 : SimpleGraph {Q // Q ∈ W.partition.parts})
    [DecidableRel R0.Adj]
    (Q : RichClaim61Certificate
      (partitionAssignment W.exceptional W.partition) Gdegree q quota R0
      (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota)
      (claim61Miss beta (paddedHalf {Q // Q ∈ W.partition.parts})))
    (density : EvenPadding {Q // Q ∈ W.partition.parts} →
      EvenPadding {Q // Q ∈ W.partition.parts} → ℝ)
    (hdensityOne : ∀ x, density (Sum.inl Q.A) x ≤ 1)
    (targetB : ℝ) (htargetB : 0 ≤ targetB)
    (htargetBLower : targetB ≤
      richSourceLower (partitionAssignment W.exceptional W.partition) q
        W.loss W.clusterSize beta
        (paddedHalf {Q // Q ∈ W.partition.parts}))
    (hBcard :
      ((allMatchingEdges Q.claim67.M).card : ℝ) *
          (targetB + 2 * (W.clusterSize : ℝ)) ≤
        (claim617Q beta
            (paddedHalf {Q // Q ∈ W.partition.parts}) : ℝ) *
          richSourceLower (partitionAssignment W.exceptional W.partition) q
            W.loss W.clusterSize beta
            (paddedHalf {Q // Q ∈ W.partition.parts})) :
    PreExceptionalScalarFacts
      (partitionAssignment W.exceptional W.partition) Gdegree q quota R0 Q
      density W.clusterSize W.loss (q : ℝ) targetB
      ((W.exceptional.card : ℝ) / 2)
      (paddedHalf {Q // Q ∈ W.partition.parts} -
        8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts}))
      (paddedHalf {Q // Q ∈ W.partition.parts})
      (paddedHalf {Q // Q ∈ W.partition.parts} +
        8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts})) := by
  classical
  let I := {Q // Q ∈ W.partition.parts}
  let k := paddedHalf I
  let h := claim617H beta k
  have hk : section6K₀ beta ≤ k := by
    dsimp only [k, I]
    exact section6K₀_le_witnessPaddedHalf W
  have hbounds := degreeForm_preExceptional_bounds hbeta hbetaOne W hNq hNhost
  dsimp only at hbounds
  obtain ⟨hcover, hcovered, herror, hcluster, hcleanup⟩ := hbounds
  have hdegree := degreeForm_degreeTarget_le_richSourceLower
    hbeta hbetaOne W hNq hNhost
  have hsourcePos := degreeForm_richSourceLower_pos
    hbeta hbetaOne W hNq hNhost
  have hq : 0 < q := by
    subst Nhost
    have hpositive : 0 < 5 * W.ordinaryParts :=
      Nat.mul_pos (by norm_num) W.ordinaryParts_pos
    have hhostPositive : 0 < 2 * q :=
      lt_of_lt_of_le hpositive W.five_ordinaryParts_le_host
    omega
  have hround := claim617_rounding_inequality hbeta hbetaOne hk
  have hrpos : 0 < mainScale beta k := mainScale_pos hbeta hbetaOne hk
  have hhsmall : 8 * h + 1 ≤ k := by
    dsimp only [h] at hround ⊢
    have h80 : 80 * claim617H beta k < k := by
      by_contra hnot
      have hle : k ≤ 80 * claim617H beta k := Nat.le_of_not_gt hnot
      have hmul := Nat.mul_le_mul_left (mainScale beta k) hle
      nlinarith
    omega
  have hetaSmall : (eta beta : ℝ) ≤ 1 / 1000 := by
    have heta := eta_le_rho_div_1000 hbeta hbetaOne
    have hr : (rho beta : ℝ) ≤ 1 := by
      exact_mod_cast rho_le_one hbeta hbetaOne
    linarith
  have hhLower : (eta beta : ℝ) * k ≤ h := by
    exact le_upperScale_cast _
  have hm0 : (0 : ℝ) ≤ W.clusterSize := by positivity
  have hhMul := mul_le_mul_of_nonneg_right hhLower hm0
  have hlowerCast :
      ((k - 8 * h - 1 : ℕ) : ℝ) = (k : ℝ) - 8 * h - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k - 8 * h),
      Nat.cast_sub (by omega : 8 * h ≤ k)]
    push_cast
    ring
  have hlowerTarget :
      ((k - 8 * h - 1 : ℕ) : ℝ) * W.clusterSize ≤
        lemma611TargetA beta (q : ℝ) := by
    rw [hlowerCast, lemma611TargetA, lemma611EpsilonOne]
    have hfactor : (0 : ℝ) ≤ 1 - 8 * (eta beta : ℝ) := by
      linarith
    have hscaled := mul_le_mul_of_nonneg_left hcover hfactor
    nlinarith
  refine
    { reducedK_eq := rfl
      reducedK_large := hk
      nTree_pos := by exact_mod_cast hq
      error_nonneg := by positivity
      targetB_nonneg := htargetB
      degree_target_le_lower := hdegree
      targetB_le_lower := htargetBLower
      source_lower_pos := hsourcePos
      B_card_lower := hBcard
      n_covered := hcovered
      cover := hcover
      error_small := herror
      cluster_small := hcluster.trans ?_
      lower := ?_
      upper := twice_minEdgeCap_le k
      total_card := ?_ }
  · have hs0 : (0 : ℝ) ≤ (sigma beta : ℝ) := by
      exact_mod_cast (sigma_pos hbeta).le
    have hq0 : (0 : ℝ) ≤ q := by positivity
    have hs : (0 : ℝ) ≤ (sigma beta : ℝ) * q :=
      mul_nonneg hs0 hq0
    nlinarith
  · intro S hS hsource
    have hsourceUpper := sourceDegree_le_two_mul_N_mul_card
      Q.claim67.M
      (padFinset (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota))
      density (W.clusterSize : ℝ) (Sum.inl Q.A) S hm0
      (fun e _he c ↦ hdensityOne _)
    by_contra hnot
    change ¬ k - 8 * h ≤ 2 * S.card at hnot
    have hcardNat : 2 * S.card ≤ k - 8 * h - 1 := by omega
    have hcardR : (2 * S.card : ℕ) ≤ k - 8 * h - 1 := hcardNat
    have hcardCast : ((2 * S.card : ℕ) : ℝ) ≤
        ((k - 8 * h - 1 : ℕ) : ℝ) := by exact_mod_cast hcardR
    have hmul := mul_le_mul_of_nonneg_right hcardCast hm0
    have hupperTarget : sourceDegree Q.claim67.M
        (padFinset (largeClustersAtLeast
          (partitionAssignment W.exceptional W.partition) Gdegree q quota))
        density (W.clusterSize : ℝ) (Sum.inl Q.A) S ≤
          lemma611TargetA beta (q : ℝ) := by
      calc
        sourceDegree Q.claim67.M
              (padFinset (largeClustersAtLeast
                (partitionAssignment W.exceptional W.partition) Gdegree q
                  quota)) density (W.clusterSize : ℝ) (Sum.inl Q.A) S
            ≤ 2 * (W.clusterSize : ℝ) * S.card := hsourceUpper
        _ = (W.clusterSize : ℝ) * ((2 * S.card : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ (W.clusterSize : ℝ) *
            ((k - 8 * h - 1 : ℕ) : ℝ) := by
          simpa only [mul_comm] using hmul
        _ ≤ lemma611TargetA beta (q : ℝ) := by
          simpa only [mul_comm] using hlowerTarget
    linarith
  · rw [card_evenPadding]
    omega

/-- The preceding scalar package with its canonical `B`-target specialized
to one cluster. -/
theorem preExceptionalScalarFacts_of_degreeForm_clusterSizeTarget
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (Gdegree : SimpleGraph (Fin Nhost)) [DecidableRel Gdegree.Adj]
    (quota : ℕ)
    (R0 : SimpleGraph {Q // Q ∈ W.partition.parts})
    [DecidableRel R0.Adj]
    (Q : RichClaim61Certificate
      (partitionAssignment W.exceptional W.partition) Gdegree q quota R0
      (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Gdegree q quota)
      (claim61Miss beta (paddedHalf {Q // Q ∈ W.partition.parts})))
    (density : EvenPadding {Q // Q ∈ W.partition.parts} →
      EvenPadding {Q // Q ∈ W.partition.parts} → ℝ)
    (hdensityOne : ∀ x, density (Sum.inl Q.A) x ≤ 1) :
    PreExceptionalScalarFacts
      (partitionAssignment W.exceptional W.partition) Gdegree q quota R0 Q
      density W.clusterSize W.loss (q : ℝ) (W.clusterSize : ℝ)
      ((W.exceptional.card : ℝ) / 2)
      (paddedHalf {Q // Q ∈ W.partition.parts} -
        8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts}))
      (paddedHalf {Q // Q ∈ W.partition.parts})
      (paddedHalf {Q // Q ∈ W.partition.parts} +
        8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts})) := by
  have hB := degreeForm_clusterSize_B_bounds hbeta hbetaOne W hNq hNhost
    Gdegree quota R0 Q
  dsimp only at hB
  exact preExceptionalScalarFacts_of_degreeForm hbeta hbetaOne W hNq
    hNhost Gdegree quota R0 Q density hdensityOne (W.clusterSize : ℝ)
      hB.1.le hB.2.1 hB.2.2

/-- Every entry in a normalized rooted density row is at most one when all
ordinary clusters have size at most the normalizing cluster size. -/
theorem twoRootSourceDensity_row_A_le_one
    {J : Type*} [Fintype J] [DecidableEq J]
    {Bv : Type*} [Fintype Bv] [DecidableEq Bv]
    (G : SimpleGraph Bv) [DecidableRel G.Adj]
    (cluster : J → Finset Bv) (clusterSize : ℕ)
    (hclusterSize : 0 < clusterSize)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (A B : EvenPadding J) (zA zB : Bv) (x : EvenPadding J) :
    twoRootSourceDensity G (padCluster cluster) (clusterSize : ℝ)
        A B zA zB A x ≤ 1 := by
  rw [twoRootSourceDensity_row_A, rootedSourceDensity]
  apply (div_le_one (by exact_mod_cast hclusterSize)).mpr
  have hpad : (padCluster cluster x).card ≤ clusterSize := by
    cases x with
    | inl i => simpa [padCluster] using hclusterCard i
    | inr i => simp [padCluster]
  exact_mod_cast (Erdos547EC2.degreeInto_le_card G zA
    (padCluster cluster x)).trans hpad

/-- Package the rich source-row conclusions with the scalar Section-6
estimates. -/
theorem preExceptionalFacts_of_sourceBounds
    (Pcluster : ClusterAssignment V I)
    (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
    (threshold quota : ℕ)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    {beta : ℚ} {reducedK : ℕ}
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (largeClustersAtLeast Pcluster Gdegree threshold quota)
      (claim61Miss beta reducedK))
    (density : EvenPadding I → EvenPadding I → ℝ)
    (clusterSize loss : ℕ)
    (hclusterSize : 0 < clusterSize)
    (nTree targetB error : ℝ)
    (lowerV1 upperV1 upperV2 : ℕ)
    (hdegreeA :
      richSourceLower Pcluster threshold loss clusterSize beta reducedK ≤
        sourceDegree Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          density (clusterSize : ℝ) (Sum.inl Q.A)
          (allMatchingEdges Q.claim67.M))
    (hdegreeB :
      richSourceLower Pcluster threshold loss clusterSize beta reducedK ≤
        sourceDegree Q.claim67.M
          (padFinset (largeClustersAtLeast Pcluster Gdegree threshold quota))
          density (clusterSize : ℝ) (Sum.inl Q.B)
          (allMatchingEdges Q.claim67.M))
    (hA_density_nonneg : ∀ x, 0 ≤ density (Sum.inl Q.A) x)
    (hA_edge_nonneg : ∀ e : MatchingEdge Q.claim67.M,
      0 ≤ (clusterSize : ℝ) *
        (density (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 0) +
          density (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 1)))
    (hB_edge_nonneg : ∀ e : MatchingEdge Q.claim67.M,
      0 ≤ (clusterSize : ℝ) *
        (density (Sum.inl Q.B)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 0) +
          density (Sum.inl Q.B)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 1)))
    (hA_edge_cap : ∀ e : MatchingEdge Q.claim67.M,
      (clusterSize : ℝ) *
        (density (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 0) +
          density (Sum.inl Q.A)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 1)) ≤
        2 * (clusterSize : ℝ))
    (hB_edge_cap : ∀ e : MatchingEdge Q.claim67.M,
      (clusterSize : ℝ) *
        (density (Sum.inl Q.B)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 0) +
          density (Sum.inl Q.B)
            (orientedEndpoint Q.claim67.M
              (padFinset
                (largeClustersAtLeast Pcluster Gdegree threshold quota)) e 1)) ≤
        2 * (clusterSize : ℝ))
    (hdensity_adj_A : ∀ x, 0 < density (Sum.inl Q.A) x →
      (padGraph R0).Adj (Sum.inl Q.A) x)
    (hdensity_adj_B : ∀ x, 0 < density (Sum.inl Q.B) x →
      (padGraph R0).Adj (Sum.inl Q.B) x)
    (F : PreExceptionalScalarFacts Pcluster Gdegree threshold quota R0 Q
      density clusterSize loss nTree targetB error lowerV1 upperV1 upperV2) :
    PreExceptionalFacts Pcluster Gdegree threshold quota R0 Q density
      (clusterSize : ℝ) nTree targetB error lowerV1 upperV1 upperV2 := by
  refine
    { reducedK_eq := F.reducedK_eq
      reducedK_large := F.reducedK_large
      N_pos := ?_
      nTree_pos := F.nTree_pos
      error_nonneg := F.error_nonneg
      targetB_nonneg := F.targetB_nonneg
      A_edge_nonneg := hA_edge_nonneg
      A_density_nonneg := hA_density_nonneg
      B_edge_nonneg := hB_edge_nonneg
      A_edge_cap := hA_edge_cap
      B_edge_cap := hB_edge_cap
      degreeA := F.degree_target_le_lower.trans hdegreeA
      degreeB := F.degree_target_le_lower.trans hdegreeB
      density_adj_A := hdensity_adj_A
      density_adj_B := hdensity_adj_B
      B_total := F.targetB_le_lower.trans hdegreeB
      B_total_pos := F.source_lower_pos.trans_le hdegreeB
      B_card := ?_
      n_covered := F.n_covered
      cover := F.cover
      error_small := F.error_small
      cluster_small := F.cluster_small
      lower := F.lower
      upper := F.upper
      total_card := F.total_card }
  · exact_mod_cast hclusterSize
  · calc
      ((allMatchingEdges Q.claim67.M).card : ℝ) *
            (targetB + 2 * (clusterSize : ℝ)) ≤
          (claim617Q beta reducedK : ℝ) *
            richSourceLower Pcluster threshold loss clusterSize beta reducedK :=
        F.B_card_lower
      _ ≤ (claim617Q beta reducedK : ℝ) *
          sourceDegree Q.claim67.M
            (padFinset
              (largeClustersAtLeast Pcluster Gdegree threshold quota)) density
            (clusterSize : ℝ) (Sum.inl Q.B)
            (allMatchingEdges Q.claim67.M) :=
      mul_le_mul_of_nonneg_left hdegreeB (by positivity)

/-- Select the two rich source roots and assemble the pre-exceptional
package, without yet imposing the stronger simultaneous typicality used by
the later full-fiber exceptional argument. -/
theorem exists_preExceptionalFacts_of_richClaim61
    (Pcluster : ClusterAssignment V I)
    (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
    (threshold quota : ℕ)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    {beta : ℚ} {reducedK : ℕ}
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (largeClustersAtLeast Pcluster Gdegree threshold quota)
      (claim61Miss beta reducedK))
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (cluster : I → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (clusterSize loss : ℕ)
    (hquota : 0 < quota) (hclusterSize : 0 < clusterSize)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (hloss : DegreeLossAtMost Gdegree G loss)
    (hrespect : EdgesRespectReducedGraph (padAssignment Pcluster) G
      (padGraph R0))
    (nTree targetB error : ℝ)
    (lowerV1 upperV1 upperV2 : ℕ)
    (hscalar : ∀ zA zB,
      PreExceptionalScalarFacts Pcluster Gdegree threshold quota R0 Q
        (twoRootSourceDensity G (padCluster cluster) (clusterSize : ℝ)
          (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
        clusterSize loss nTree targetB error lowerV1 upperV1 upperV2) :
    ∃ zA ∈ Q.A₀, ∃ zB ∈ Q.B₀,
      PreExceptionalFacts Pcluster Gdegree threshold quota R0 Q
        (twoRootSourceDensity G (padCluster cluster) (clusterSize : ℝ)
          (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
        (clusterSize : ℝ) nTree targetB error lowerV1 upperV1 upperV2 := by
  obtain ⟨zA, hzA, _hzAclean, zB, hzB, _hzBclean, hsource⟩ :=
    exists_twoRootSourceDensity_of_richClaim61 Pcluster Gdegree G R0 cluster
      hcluster threshold quota (claim61Miss beta reducedK) clusterSize loss
      hquota hclusterSize hclusterCard hloss hrespect ∅ ∅ (by simpa using
        hquota) (by simpa using hquota) Q
  dsimp only at hsource
  rcases hsource with
    ⟨hdegreeA, hdegreeB, hA_density_nonneg, hA_edge_nonneg,
      hB_edge_nonneg, hA_edge_cap, hB_edge_cap, hdensity_adj_A,
      hdensity_adj_B⟩
  refine ⟨zA, hzA, zB, hzB, ?_⟩
  apply preExceptionalFacts_of_sourceBounds Pcluster Gdegree threshold quota
    R0 Q
    (twoRootSourceDensity G (padCluster cluster) (clusterSize : ℝ)
      (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
    clusterSize loss hclusterSize nTree targetB error lowerV1 upperV1 upperV2
    hdegreeA hdegreeB hA_density_nonneg hA_edge_nonneg hB_edge_nonneg
    hA_edge_cap hB_edge_cap hdensity_adj_A hdensity_adj_B
  exact hscalar zA zB

/-- Complete pre-exceptional package with a caller-specified `B`-row target.
This is the source-faithful interface needed after the tree partition is
known: in Zhao's small-`f_b` branch the target is `f_b + 3 * gamma * n`, not
one cluster.  The three displayed hypotheses are exactly the scalar premises
of the decreasing-prefix reservation lemma. -/
theorem exists_preExceptionalFacts_of_degreeForm_target
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (quota : ℕ) (hquota : 0 < quota)
    (Q : RichClaim61Certificate
      (partitionAssignment W.exceptional W.partition) Hhost q quota
      (regularityReducedGraph Hhost
        (fun i : {Q // Q ∈ W.partition.parts} ↦ i.1)
        (regularityEpsilon beta) (reducedDensity beta))
      (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Hhost q quota)
      (claim61Miss beta (paddedHalf {Q // Q ∈ W.partition.parts})))
    (targetB : ℝ) (htargetB : 0 ≤ targetB)
    (htargetBLower : targetB ≤
      richSourceLower (partitionAssignment W.exceptional W.partition) q
        W.loss W.clusterSize beta
        (paddedHalf {Q // Q ∈ W.partition.parts}))
    (hBcard :
      ((allMatchingEdges Q.claim67.M).card : ℝ) *
          (targetB + 2 * (W.clusterSize : ℝ)) ≤
        (claim617Q beta
            (paddedHalf {Q // Q ∈ W.partition.parts}) : ℝ) *
          richSourceLower (partitionAssignment W.exceptional W.partition) q
            W.loss W.clusterSize beta
            (paddedHalf {Q // Q ∈ W.partition.parts})) :
    letI : DecidableRel W.graph.Adj := W.graph_decidable
    ∃ zA ∈ Q.A₀, ∃ zB ∈ Q.B₀,
      PreExceptionalFacts
        (partitionAssignment W.exceptional W.partition) Hhost q quota
        (regularityReducedGraph Hhost
          (fun i : {Q // Q ∈ W.partition.parts} ↦ i.1)
          (regularityEpsilon beta) (reducedDensity beta))
        Q
        (twoRootSourceDensity W.graph
          (padCluster (fun i : {Q // Q ∈ W.partition.parts} ↦ i.1))
          (W.clusterSize : ℝ) (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
        (W.clusterSize : ℝ) (q : ℝ) targetB
        ((W.exceptional.card : ℝ) / 2)
        (paddedHalf {Q // Q ∈ W.partition.parts} -
          8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts}))
        (paddedHalf {Q // Q ∈ W.partition.parts})
        (paddedHalf {Q // Q ∈ W.partition.parts} +
          8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts})) := by
  classical
  let I := {Q // Q ∈ W.partition.parts}
  let Pcluster : ClusterAssignment (Fin Nhost) I :=
    partitionAssignment W.exceptional W.partition
  let cluster : I → Finset (Fin Nhost) := fun i ↦ i.1
  let R0 : SimpleGraph I := regularityReducedGraph Hhost cluster
    (regularityEpsilon beta) (reducedDensity beta)
  letI : DecidableRel W.graph.Adj := W.graph_decidable
  have hcluster : ∀ i, cluster i = clusterVertices Pcluster i := by
    intro i
    exact (clusterVertices_partitionAssignment W.exceptional W.partition i).symm
  have hclusterCard : ∀ i, (cluster i).card ≤ W.clusterSize := by
    intro i
    exact (W.equal_clusters i.1 i.2).le
  have hrespect : EdgesRespectReducedGraph (padAssignment Pcluster) W.graph
      (padGraph R0) := by
    apply edgesRespect_pad
    simpa only [Pcluster, R0, cluster] using W.respects_reduced
  have hscalar : ∀ zA zB,
      PreExceptionalScalarFacts Pcluster Hhost q quota R0 Q
        (twoRootSourceDensity W.graph (padCluster cluster)
          (W.clusterSize : ℝ) (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
        W.clusterSize W.loss (q : ℝ) targetB
        ((W.exceptional.card : ℝ) / 2)
        (paddedHalf I - 8 * claim617H beta (paddedHalf I))
        (paddedHalf I)
        (paddedHalf I + 8 * claim617H beta (paddedHalf I)) := by
    intro zA zB
    apply preExceptionalScalarFacts_of_degreeForm hbeta hbetaOne W hNq
      hNhost Hhost quota R0 Q
      (twoRootSourceDensity W.graph (padCluster cluster)
        (W.clusterSize : ℝ) (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
      (fun x ↦ twoRootSourceDensity_row_A_le_one W.graph cluster W.clusterSize
        W.clusterSize_pos hclusterCard (Sum.inl Q.A) (Sum.inl Q.B) zA zB x)
      targetB htargetB htargetBLower hBcard
  have hex := exists_preExceptionalFacts_of_richClaim61 Pcluster Hhost q
    quota R0 Q W.graph cluster hcluster W.clusterSize W.loss hquota
    W.clusterSize_pos hclusterCard W.degree_loss hrespect (q : ℝ)
    targetB ((W.exceptional.card : ℝ) / 2)
    (paddedHalf I - 8 * claim617H beta (paddedHalf I)) (paddedHalf I)
    (paddedHalf I + 8 * claim617H beta (paddedHalf I)) hscalar
  simpa only [I, Pcluster, cluster, R0] using hex

/-- Complete canonical pre-exceptional package from a degree-form witness and
a rich certificate on the degree-form input graph.  The density rows live in
the cleaned graph `W.graph`, while the distinguished roots retain their
threshold degree through `W.degree_loss`.  This one-cluster specialization is
retained for callers that genuinely need that target; Claim 6.15 uses the
tree-dependent theorem above. -/
theorem exists_preExceptionalFacts_of_degreeForm
    {beta : ℚ} (hbeta : 0 < beta) (hbetaOne : beta ≤ 1 / 4)
    {Nhost q : ℕ} {Hhost : SimpleGraph (Fin Nhost)}
    [DecidableRel Hhost.Adj]
    (W : DegreeFormWitness Hhost (regularityEpsilon beta)
      (reducedDensity beta) (section6M₀ beta)
      (degreeFormBound (regularityEpsilon beta) (section6M₀ beta)))
    (hNq : Nhost = 2 * q) (hNhost : section6N₀ beta ≤ Nhost)
    (quota : ℕ) (hquota : 0 < quota)
    (Q : RichClaim61Certificate
      (partitionAssignment W.exceptional W.partition) Hhost q quota
      (regularityReducedGraph Hhost
        (fun i : {Q // Q ∈ W.partition.parts} ↦ i.1)
        (regularityEpsilon beta) (reducedDensity beta))
      (largeClustersAtLeast
        (partitionAssignment W.exceptional W.partition) Hhost q quota)
      (claim61Miss beta (paddedHalf {Q // Q ∈ W.partition.parts}))) :
    letI : DecidableRel W.graph.Adj := W.graph_decidable
    ∃ zA ∈ Q.A₀, ∃ zB ∈ Q.B₀,
      PreExceptionalFacts
        (partitionAssignment W.exceptional W.partition) Hhost q quota
        (regularityReducedGraph Hhost
          (fun i : {Q // Q ∈ W.partition.parts} ↦ i.1)
          (regularityEpsilon beta) (reducedDensity beta))
        Q
        (twoRootSourceDensity W.graph
          (padCluster (fun i : {Q // Q ∈ W.partition.parts} ↦ i.1))
          (W.clusterSize : ℝ) (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
        (W.clusterSize : ℝ) (q : ℝ) (W.clusterSize : ℝ)
        ((W.exceptional.card : ℝ) / 2)
        (paddedHalf {Q // Q ∈ W.partition.parts} -
          8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts}))
        (paddedHalf {Q // Q ∈ W.partition.parts})
        (paddedHalf {Q // Q ∈ W.partition.parts} +
          8 * claim617H beta (paddedHalf {Q // Q ∈ W.partition.parts})) := by
  classical
  let I := {Q // Q ∈ W.partition.parts}
  let Pcluster : ClusterAssignment (Fin Nhost) I :=
    partitionAssignment W.exceptional W.partition
  let cluster : I → Finset (Fin Nhost) := fun i ↦ i.1
  let R0 : SimpleGraph I := regularityReducedGraph Hhost cluster
    (regularityEpsilon beta) (reducedDensity beta)
  letI : DecidableRel W.graph.Adj := W.graph_decidable
  have hcluster : ∀ i, cluster i = clusterVertices Pcluster i := by
    intro i
    exact (clusterVertices_partitionAssignment W.exceptional W.partition i).symm
  have hclusterCard : ∀ i, (cluster i).card ≤ W.clusterSize := by
    intro i
    exact (W.equal_clusters i.1 i.2).le
  have hrespect : EdgesRespectReducedGraph (padAssignment Pcluster) W.graph
      (padGraph R0) := by
    apply edgesRespect_pad
    simpa only [Pcluster, R0, cluster] using W.respects_reduced
  have hscalar : ∀ zA zB,
      PreExceptionalScalarFacts Pcluster Hhost q quota R0 Q
        (twoRootSourceDensity W.graph (padCluster cluster)
          (W.clusterSize : ℝ) (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
        W.clusterSize W.loss (q : ℝ) (W.clusterSize : ℝ)
        ((W.exceptional.card : ℝ) / 2)
        (paddedHalf I - 8 * claim617H beta (paddedHalf I))
        (paddedHalf I)
        (paddedHalf I + 8 * claim617H beta (paddedHalf I)) := by
    intro zA zB
    apply preExceptionalScalarFacts_of_degreeForm_clusterSizeTarget hbeta
      hbetaOne W hNq hNhost Hhost quota R0 Q
    intro x
    exact twoRootSourceDensity_row_A_le_one W.graph cluster W.clusterSize
      W.clusterSize_pos hclusterCard (Sum.inl Q.A) (Sum.inl Q.B) zA zB x
  have hex := exists_preExceptionalFacts_of_richClaim61 Pcluster Hhost q
    quota R0 Q W.graph cluster hcluster W.clusterSize W.loss hquota
    W.clusterSize_pos hclusterCard W.degree_loss hrespect (q : ℝ)
    (W.clusterSize : ℝ) ((W.exceptional.card : ℝ) / 2)
    (paddedHalf I - 8 * claim617H beta (paddedHalf I)) (paddedHalf I)
    (paddedHalf I + 8 * claim617H beta (paddedHalf I)) hscalar
  simpa only [I, Pcluster, cluster, R0] using hex

/-- Select globally cleaned rich source witnesses and immediately assemble
the corresponding pre-exceptional Lemma-6.11 package.  The scalar data are
required uniformly in the two selected vertices, which makes the theorem
usable before their finite choices are exposed. -/
theorem exists_preExceptionalFacts_of_richClaim61_witnessClean
    (Pcluster : ClusterAssignment V I)
    (Gdegree : SimpleGraph V) [DecidableRel Gdegree.Adj]
    (threshold quota : ℕ)
    (R0 : SimpleGraph I) [DecidableRel R0.Adj]
    {beta : ℚ} {reducedK : ℕ}
    (Q : RichClaim61Certificate Pcluster Gdegree threshold quota R0
      (largeClustersAtLeast Pcluster Gdegree threshold quota)
      (claim61Miss beta reducedK))
    (Gsource : SimpleGraph V) [DecidableRel Gsource.Adj]
    (Ghost : SimpleGraph V) [DecidableRel Ghost.Adj]
    (cluster : I → Finset V)
    (hcluster : ∀ i, cluster i = clusterVertices Pcluster i)
    (clusterSize loss : ℕ)
    (hquota : 0 < quota) (hclusterSize : 0 < clusterSize)
    (hclusterCard : ∀ i, (cluster i).card ≤ clusterSize)
    (hloss : DegreeLossAtMost Gdegree Gsource loss)
    (hrespect : EdgesRespectReducedGraph (padAssignment Pcluster) Gsource
      (padGraph R0))
    (rho pairDensity : ℝ)
    (Hpair : ReducedPairRealization Pcluster R0 Ghost rho pairDensity)
    (hrho : rho ≤ 1)
    (hrootLarge : ∀ side,
      rho * #(rootWholeSide Pcluster Gdegree threshold quota R0
        (claim61Miss beta reducedK) Q side) ≤ quota)
    (hbadBudget : ∀ side,
      (#(sourceWitnessTargets Pcluster Gdegree threshold quota R0
          (claim61Miss beta reducedK) Q side) : ℝ) *
          (rho * #(rootWholeSide Pcluster Gdegree threshold quota R0
            (claim61Miss beta reducedK) Q side)) < quota)
    (nTree targetB error : ℝ)
    (lowerV1 upperV1 upperV2 : ℕ)
    (hscalar : ∀ zA zB,
      PreExceptionalScalarFacts Pcluster Gdegree threshold quota R0 Q
        (twoRootSourceDensity Gsource (padCluster cluster) (clusterSize : ℝ)
          (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
        clusterSize loss nTree targetB error lowerV1 upperV1 upperV2) :
    ∃ zA ∈ Q.A₀,
      zA ∉ sourceWitnessHighBad Pcluster Gdegree threshold quota R0
        (claim61Miss beta reducedK) Q Ghost rho 0 ∧
      ∃ zB ∈ Q.B₀,
        zB ∉ sourceWitnessHighBad Pcluster Gdegree threshold quota R0
          (claim61Miss beta reducedK) Q Ghost rho 1 ∧
        PreExceptionalFacts Pcluster Gdegree threshold quota R0 Q
          (twoRootSourceDensity Gsource (padCluster cluster) (clusterSize : ℝ)
            (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
          (clusterSize : ℝ) nTree targetB error lowerV1 upperV1 upperV2 := by
  obtain ⟨zA, hzA, hzAclean, zB, hzB, hzBclean, hsource⟩ :=
    exists_twoRootSourceDensity_of_richClaim61_witnessClean Pcluster Gdegree
      threshold quota R0 (claim61Miss beta reducedK) Q Gsource Ghost cluster hcluster
      clusterSize loss hquota hclusterSize hclusterCard hloss hrespect rho
      pairDensity Hpair hrho hrootLarge hbadBudget
  dsimp only at hsource
  rcases hsource with
    ⟨hdegreeA, hdegreeB, hA_density_nonneg, hA_edge_nonneg,
      hB_edge_nonneg, hA_edge_cap, hB_edge_cap, hdensity_adj_A,
      hdensity_adj_B⟩
  refine ⟨zA, hzA, hzAclean, zB, hzB, hzBclean, ?_⟩
  apply preExceptionalFacts_of_sourceBounds Pcluster Gdegree threshold quota
    R0 Q
    (twoRootSourceDensity Gsource (padCluster cluster) (clusterSize : ℝ)
      (Sum.inl Q.A) (Sum.inl Q.B) zA zB)
    clusterSize loss hclusterSize nTree targetB error lowerV1 upperV1 upperV2
    hdegreeA hdegreeB hA_density_nonneg hA_edge_nonneg hB_edge_nonneg
    hA_edge_cap hB_edge_cap hdensity_adj_A hdensity_adj_B
  exact hscalar zA zB

end Erdos547b.ZhaoSection6PreExceptionalAssembly

#print axioms Erdos547b.ZhaoSection6PreExceptionalAssembly.preExceptionalFacts_of_sourceBounds
#print axioms Erdos547b.ZhaoSection6PreExceptionalAssembly.exists_preExceptionalFacts_of_richClaim61_witnessClean
