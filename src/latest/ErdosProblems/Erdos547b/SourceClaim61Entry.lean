/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceClaim61Numerics
import ErdosProblems.Erdos547b.SourceDegreeFormBounds

/-!
# Unconditional source-threshold entry to rich Claim 6.1

Every graph satisfying the half-high-degree hypothesis has an actual
degree-form witness and the dense-case/rich-certificate dichotomy. The
only scalar hypotheses are the positive extremal cap and the explicit
finite order threshold; all cleanup, quota, and matching scales are proved.
-/

noncomputable section

namespace Erdos547b.ZhaoSourceClaim61Entry

open Finset SimpleGraph
open Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSection6Dichotomy Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClaim61RichFull Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoSection6RichHierarchy Erdos547b.ZhaoSourceClaim61Numerics
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoDegreeFormQuantitative Erdos547b.ZhaoPrunedReducedLargeEdges
open Erdos547b.ZhaoClusterPairPruning

/-- Tree order threshold, with the source's edge count equal to `n - 1`. -/
def sourceRamseyThreshold (α : ℚ) : ℕ :=
  orderThreshold α (degreeFormBound (epsilon α) (requestedClusters α)) + 1

private theorem reservoir_gates_of_host_eq
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {N q M : ℕ} (hN : N = 2 * q)
    {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    (W.exceptional.card : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q / 4 ∧
      (W.loss : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q / 4 ∧
      (W.clusterSize : ℝ) ≤ (fourthRoot α : ℝ) ^ 2 * q := by
  subst N
  exact degreeForm_reservoir_gates hα hα1 W hq

/-- All numerical premises of the repaired rich constructor are supplied
by the source parameter schedule, with no graph-embedding premise. -/
theorem rich_claim61_of_source_order
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {n M : ℕ} (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
      (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices G (n - 1)).card)
    (horder : orderThreshold α M ≤ n - 1) :
    let ι := {Q // Q ∈ W.partition.parts}
    let P := partitionAssignment W.exceptional W.partition
    let quota := richQuota ((fourthRoot α : ℝ) ^ 2) W.clusterSize
    let L := largeClustersAtLeast P G (n - 1) quota
    let R := pruneSmallEdges
      (regularityReducedGraph (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
        (fun i : ι => i.1) (epsilon α) (densityCutoff α)) (L : Set ι)
    ZhaoExtremalCaseOne α G ∨
      Nonempty (RichClaim61Certificate P G (n - 1) quota R L
        (2 * matchingDefect ((fourthRoot α : ℝ) ^ 2) (paddedHalf ι) + 1)) := by
  classical
  obtain ⟨hsigma, hsigmaSmall, hαsigma, _, _, _⟩ := reservoir_cleanup_bounds hα hα1
  obtain ⟨hE, hloss, hm⟩ := reservoir_gates_of_host_eq hα hα1
    (show 2 * n - 2 = 2 * (n - 1) by omega) W horder
  have hsmallQ : 16 * fourthRoot α ^ 2 ≤ 1 := by linarith only [hsigmaSmall]
  have hsmallR : 16 * (fourthRoot α : ℝ) ^ 2 ≤ 1 := by exact_mod_cast hsmallQ
  exact pairPruned_rich_entry G W hn hlarge ((fourthRoot α : ℝ) ^ 2)
    (by exact_mod_cast hsigma) (by linarith only [hsmallR])
    hE hloss hm (by exact_mod_cast hαsigma)

/-- An actual witness and rich Claim-6.1 dichotomy for every sufficiently
large half-high-degree graph, using the source-faithful density cutoff. -/
theorem exists_source_claim61
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {n : ℕ} (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (hn : sourceRamseyThreshold α ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices G (n - 1)).card) :
    ∃ W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
      (epsilon α) (densityCutoff α) (requestedClusters α)
      (degreeFormBound (epsilon α) (requestedClusters α)),
      let ι := {Q // Q ∈ W.partition.parts}
      let P := partitionAssignment W.exceptional W.partition
      let quota := richQuota ((fourthRoot α : ℝ) ^ 2) W.clusterSize
      let L := largeClustersAtLeast P G (n - 1) quota
      let R := pruneSmallEdges
        (regularityReducedGraph (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
          (fun i : ι => i.1) (epsilon α) (densityCutoff α)) (L : Set ι)
      ZhaoExtremalCaseOne α G ∨
        Nonempty (RichClaim61Certificate P G (n - 1) quota R L
          (2 * matchingDefect ((fourthRoot α : ℝ) ^ 2) (paddedHalf ι) + 1)) := by
  classical
  obtain ⟨_, _, _, _, _, hcut, _, he⟩ := parameter_pos hα
  have hn2 : 2 ≤ n := by
    unfold sourceRamseyThreshold orderThreshold at hn
    omega
  have horder : orderThreshold α
      (degreeFormBound (epsilon α) (requestedClusters α)) ≤ n - 1 := by
    unfold sourceRamseyThreshold at hn
    omega
  have hregularity : degreeFormThreshold (epsilon α) (requestedClusters α) ≤
      2 * n - 2 := by
    unfold degreeFormThreshold
    unfold orderThreshold at horder
    omega
  obtain ⟨W⟩ := exists_degreeFormWitness he hcut (requestedClusters α)
    (2 * n - 2) hregularity (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
  exact ⟨W, rich_claim61_of_source_order hα hα1 G W hn2 hlarge horder⟩

/-- Cleanup and the matching defect cost less than `9 * sqrt d`, leaving
the last `sqrt d` of the source's row-loss budget for atypical targets.
The possible padded cluster is included in the exact cardinality argument. -/
theorem preExceptional_cleanup_bound_nine
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    let k := paddedHalf {Q // Q ∈ W.partition.parts}
    ((W.loss + W.exceptional.card +
      (2 * matchingDefect ((fourthRoot α : ℝ) ^ 2) k + 1) * W.clusterSize +
        4 * W.clusterSize : ℕ) : ℝ) < 9 * (fourthRoot α : ℝ) ^ 2 * q := by
  classical
  dsimp only
  let ι := {Q // Q ∈ W.partition.parts}
  let k := paddedHalf ι
  let sigma : ℝ := (fourthRoot α : ℝ) ^ 2
  let c := matchingDefect sigma k
  obtain ⟨hE, hloss, hm⟩ := degreeForm_source_bounds hα hα1 W hq
  obtain ⟨hsigmaQ, hsigmaSmallQ, _, hdSmallQ, _, _⟩ := reservoir_cleanup_bounds hα hα1
  have hsigma : 0 < sigma := by dsimp only [sigma]; exact_mod_cast hsigmaQ
  have hsigma16Q : 16 * fourthRoot α ^ 2 ≤ 1 := by linarith only [hsigmaSmallQ]
  have hsigma16 : 16 * sigma ≤ 1 := by dsimp only [sigma]; exact_mod_cast hsigma16Q
  have hdSmall : (degreeError α : ℝ) ≤ sigma / 100 := by
    dsimp only [sigma]
    exact_mod_cast hdSmallQ
  have hqpos : (0 : ℝ) < q := by
    have h := W.five_ordinaryParts_le_host
    have hk := W.ordinaryParts_pos
    have : 0 < q := by omega
    exact_mod_cast this
  have hhost : (W.exceptional.card : ℝ) + (Fintype.card ι : ℝ) * W.clusterSize =
      2 * q := by
    have h : W.exceptional.card + Fintype.card ι * W.clusterSize = 2 * q := by
      simpa [ι] using exceptional_add_clusters_eq_host W
    exact_mod_cast h
  have hpad : (2 : ℝ) * k * W.clusterSize ≤
      ((Fintype.card ι : ℝ) + 1) * W.clusterSize := by
    exact_mod_cast Nat.mul_le_mul_right W.clusterSize (paddedCard_le_card_add_one ι)
  have hcover : (k : ℝ) * W.clusterSize ≤ (q : ℝ) + W.clusterSize := by
    nlinarith only [hhost, hpad, show (0 : ℝ) ≤ W.exceptional.card by positivity,
      show (0 : ℝ) ≤ W.clusterSize by positivity]
  have hceil : (c : ℝ) < 4 * sigma * k + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceilMul := mul_le_mul_of_nonneg_right hceil.le
    (show (0 : ℝ) ≤ 2 * W.clusterSize by positivity)
  have hcoverMul := mul_le_mul_of_nonneg_left hcover (show 0 ≤ 8 * sigma by positivity)
  have hsmallMul := mul_le_mul_of_nonneg_right hsigma16
    (show (0 : ℝ) ≤ W.clusterSize by positivity)
  have hmiss : ((2 * c + 1 : ℕ) : ℝ) * W.clusterSize + 4 * W.clusterSize ≤
      8 * sigma * q + 8 * W.clusterSize := by
    push_cast
    nlinarith only [hceilMul, hcoverMul, hsmallMul,
      show (0 : ℝ) ≤ W.clusterSize by positivity]
  have hdq := mul_le_mul_of_nonneg_right hdSmall hqpos.le
  have hpositive : 0 < sigma * q := mul_pos hsigma hqpos
  change ((W.loss + W.exceptional.card + (2 * c + 1) * W.clusterSize +
    4 * W.clusterSize : ℕ) : ℝ) < 9 * sigma * q
  push_cast at hmiss ⊢
  linarith only [hE, hloss, hm, hmiss, hdq, hpositive]

/-- The weaker source budget remains available to existing consumers. -/
theorem preExceptional_cleanup_bound
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {q M : ℕ} {G : SimpleGraph (Fin (2 * q))} [DecidableRel G.Adj]
    (W : DegreeFormWitness G (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hq : orderThreshold α M ≤ q) :
    let k := paddedHalf {Q // Q ∈ W.partition.parts}
    ((W.loss + W.exceptional.card +
      (2 * matchingDefect ((fourthRoot α : ℝ) ^ 2) k + 1) * W.clusterSize +
        4 * W.clusterSize : ℕ) : ℝ) < 10 * (fourthRoot α : ℝ) ^ 2 * q := by
  have h := preExceptional_cleanup_bound_nine hα hα1 W hq
  dsimp only at h ⊢
  have hnonneg : 0 ≤ (fourthRoot α : ℝ) ^ 2 * q := by positivity
  linarith only [h, hnonneg]

/-- Whole-pair pruning costs fewer than `8 * sqrt d * q^2` edges.
This counts deletions from the degree-form cleaned graph, not the initial
low--low deletion, whose cost need not be small. -/
theorem source_pair_pruning_cost
    {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    {n M : ℕ} (G : SimpleGraph (Fin (2 * n - 2))) [DecidableRel G.Adj]
    (W : DegreeFormWitness
      (pruneSmallEdges G {v | n - 1 ≤ G.degree v})
      (epsilon α) (densityCutoff α) (requestedClusters α) M)
    (hn : 2 ≤ n)
    (hlarge : n - 1 ≤ (highDegreeVertices G (n - 1)).card)
    (horder : orderThreshold α M ≤ n - 1) :
    let _ : DecidableRel W.graph.Adj := W.graph_decidable
    let P := partitionAssignment W.exceptional W.partition
    let quota := richQuota ((fourthRoot α : ℝ) ^ 2) W.clusterSize
    let L := largeClustersAtLeast P G (n - 1) quota
    ((W.graph.edgeFinset \ (pairPrunedGraph P W.graph L).edgeFinset).card : ℝ) <
      8 * (fourthRoot α : ℝ) ^ 2 * ((n - 1 : ℕ) : ℝ) ^ 2 := by
  classical
  let _ : DecidableRel W.graph.Adj := W.graph_decidable
  dsimp only
  let P := partitionAssignment W.exceptional W.partition
  let sigma : ℝ := (fourthRoot α : ℝ) ^ 2
  let quota := richQuota sigma W.clusterSize
  let L := largeClustersAtLeast P G (n - 1) quota
  let error := nonLargeHighError P G (n - 1) quota
  obtain ⟨hsigmaQ, hsigmaSmallQ, _, _, _, _⟩ := reservoir_cleanup_bounds hα hα1
  have hsigma : 0 < sigma := by dsimp only [sigma]; exact_mod_cast hsigmaQ
  have hsmallQ : 16 * fourthRoot α ^ 2 ≤ 1 := by linarith only [hsigmaSmallQ]
  have hsmallR : 16 * sigma ≤ 1 := by dsimp only [sigma]; exact_mod_cast hsmallQ
  have hsigmaSmall : sigma ≤ 1 / 16 := by linarith only [hsmallR]
  have herror : (error : ℝ) ≤ 3 * sigma * (n - 1 : ℕ) :=
    degreeForm_nonlarge_error_le G W hn hlarge sigma hsigma hsigmaSmall
  obtain ⟨hE, _, _⟩ := reservoir_gates_of_host_eq hα hα1
    (show 2 * n - 2 = 2 * (n - 1) by omega) W horder
  have hraw := quantitative_card_deleted_edges_le P G W.graph (n - 1) quota W.graph_le
  have hrawNat :
      (W.graph.edgeFinset \ (pairPrunedGraph P W.graph L).edgeFinset).card ≤
        (W.exceptional.card + error) * (2 * (n - 1)) := by
    have hhost : 2 * n - 2 = 2 * (n - 1) := by omega
    simpa only [P, exceptionalVertices_partitionAssignment, Fintype.card_fin, hhost] using hraw
  have hrawR :
      ((W.graph.edgeFinset \ (pairPrunedGraph P W.graph L).edgeFinset).card : ℝ) ≤
        ((W.exceptional.card : ℝ) + error) * (2 * (n - 1 : ℕ)) := by
    exact_mod_cast hrawNat
  have hcombined : (W.exceptional.card : ℝ) + error ≤
      (13 / 4 : ℝ) * sigma * (n - 1 : ℕ) := by
    linarith only [hE, herror]
  have hcombinedMul := mul_le_mul_of_nonneg_right hcombined
    (show (0 : ℝ) ≤ 2 * (n - 1 : ℕ) by positivity)
  have hqpos : (0 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hpositive : 0 < sigma * ((n - 1 : ℕ) : ℝ) ^ 2 := by positivity
  change ((W.graph.edgeFinset \ (pairPrunedGraph P W.graph L).edgeFinset).card : ℝ) < _
  nlinarith only [hrawR, hcombinedMul, hpositive]

end Erdos547b.ZhaoSourceClaim61Entry

#print axioms Erdos547b.ZhaoSourceClaim61Entry.rich_claim61_of_source_order
#print axioms Erdos547b.ZhaoSourceClaim61Entry.exists_source_claim61
#print axioms Erdos547b.ZhaoSourceClaim61Entry.preExceptional_cleanup_bound
#print axioms Erdos547b.ZhaoSourceClaim61Entry.preExceptional_cleanup_bound_nine
#print axioms Erdos547b.ZhaoSourceClaim61Entry.source_pair_pruning_cost
