/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCutLosses

/-! # A balanced sparse cut in the vertex-pruned actual host -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceSparseCut

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSection6Dichotomy Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceNearFullMatching Erdos547b.ZhaoSourceNearFullNumerics
open Erdos547b.ZhaoSourceOrdinaryCut Erdos547b.ZhaoSourceCutGeometry
open Erdos547b.ZhaoSourceCutLosses Erdos547b.ZhaoCutRestoration
open Erdos547b.ZhaoSourceThresholdGraphs Erdos547b.ZhaoEvenReducedPadding
open Erdos547b.ZhaoLemma611Claim618Adapter

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G) (Q : Certificate W) (S : CleanSourceWitness W Q)
variable {fb : ℝ} (O : Output W Q S fb)

local instance : DecidableRel W.graph.Adj := W.graph_decidable

theorem exists_balanced_sparse_cut
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q)
    (hcross : (((threshold W (4 * (eta α : ℝ))).interedges O.D.V1 O.D.V2).card : ℝ) <
      16 * ((rho α : ℝ) + (rhoOne α : ℝ)) * (paddedHalf (Index W) : ℝ) ^ 2) :
    ∃ A B : Finset (Fin hostN), Disjoint A B ∧ A ∪ B = Finset.univ ∧
      A.card = q ∧ B.card = q ∧
      ((((pruneSmallEdges G {v | q ≤ G.degree v}).interedges A B).card : ℝ) <
        (α : ℝ) * (q : ℝ) ^ 2) := by
  let G0 := pruneSmallEdges G {v | q ≤ G.degree v}
  let X := leftSide W Q S O
  let Y := rightSide W Q S O
  let b := moveBudget W
  obtain ⟨hXY, hcover⟩ := cut_partition W Q S O
  change Disjoint X Y at hXY
  change X ∪ Y = Finset.univ at hcover
  have hV : Fintype.card (Fin hostN) = 2 * q := (Fintype.card_fin _).trans hhost
  obtain ⟨hu, hl⟩ := leftSide_near_half W Q S O hα hα1 hhost horder
  obtain ⟨A, hA, hXA, hAX⟩ := exists_exact_half_near X q b hV hu hl
  let B := Finset.univ \ A
  have hB : B.card = q := by
    dsimp only [B]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hV, hA]
    omega
  refine ⟨A, B, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ A), hA, hB, ?_⟩
  have hrebalance := card_interedges_rebalance_le G0 X Y A q hXY hcover hV hA
  have hmoveNat : q * ((A \ X).card + (X \ A).card) ≤ 2 * q * b := by
    have h := Nat.mul_le_mul_left q (Nat.add_le_add hAX hXA)
    nlinarith only [h]
  have hrebalanceR : ((G0.interedges A B).card : ℝ) ≤ (G0.interedges X Y).card + 2 * q * b := by
    have h := hrebalance.trans (Nat.add_le_add_left hmoveNat _)
    exact_mod_cast h
  have hrestore := cluster_cut_restoration_le G0 W.graph (padAssignment (assignment W)) (host W)
    W.graph_le W.loss W.degree_loss O.D.V1 O.D.V2 (reducedCut_of_decomposition O.D).1
  rw [exceptionalVertices_padAssignment, exceptionalVertices_partitionAssignment] at hrestore
  have hrestoreR : ((G0.interedges X Y).card : ℝ) ≤
      ((host W).interedges (clusterUnion (padAssignment (assignment W)) O.D.V1)
        (clusterUnion (padAssignment (assignment W)) O.D.V2)).card +
      (X.card : ℝ) * ((W.exceptional.card : ℝ) + W.loss) +
      (W.graph.edgeFinset \ (host W).edgeFinset).card := by
    have hn : (G0.interedges X Y).card ≤
        ((host W).interedges (clusterUnion (padAssignment (assignment W)) O.D.V1)
          (clusterUnion (padAssignment (assignment W)) O.D.V2)).card +
        X.card * (W.exceptional.card + W.loss) + (W.graph.edgeFinset \ (host W).edgeFinset).card := by
      simpa only [X, Y, leftSide, rightSide, exceptionalVertices_padAssignment,
        exceptionalVertices_partitionAssignment] using hrestore
    exact_mod_cast hn
  obtain ⟨hE, hLoss, hN⟩ := cleanup_bounds W hα hα1 hhost horder
  have hd : (0 : ℝ) ≤ degreeError α := by exact_mod_cast (parameter_pos hα).2.2.2.2.1.le
  have hd1 : (degreeError α : ℝ) ≤ 1 := by
    exact_mod_cast (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hdq := mul_le_mul_of_nonneg_right hd1 hq
  have hXcard : (X.card : ℝ) = (O.D.V1.card : ℝ) * W.clusterSize := by
    exact_mod_cast leftSide_card W Q S O
  have hV1 : (O.D.V1.card : ℝ) ≤ paddedHalf (Index W) := by exact_mod_cast O.D.V1_card_upper
  have hXvolume := mul_le_mul_of_nonneg_right hV1 (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ _)
  have hvol := (sharp_paddedVolume W hα hα1 hhost horder).2
  have hXupper : (X.card : ℝ) ≤ 2 * q := by linarith only [hXcard, hXvolume, hvol, hN, hdq]
  have hEL : (W.exceptional.card : ℝ) + W.loss ≤ 2 * (degreeError α : ℝ) * q := by
    linarith only [hE, hLoss]
  have hcleanupProduct := mul_le_mul hXupper hEL (by positivity : (0 : ℝ) ≤ W.exceptional.card + W.loss)
    (by positivity : (0 : ℝ) ≤ 2 * q)
  have hcleanup : (X.card : ℝ) * ((W.exceptional.card : ℝ) + W.loss) ≤
      4 * (degreeError α : ℝ) * (q : ℝ) ^ 2 := by nlinarith only [hcleanupProduct]
  have hdeleted := pair_deleted_edges_le W hα hα1 hhost horder
  have hbudget := moveBudget_le W hα hα1 hhost horder
  have hmoveProduct := mul_le_mul_of_nonneg_left hbudget (by positivity : (0 : ℝ) ≤ 2 * q)
  have hmove : 2 * (q : ℝ) * b ≤ (16 * (eta α : ℝ) + 4 * (degreeError α : ℝ)) * (q : ℝ) ^ 2 := by
    change 2 * (q : ℝ) * moveBudget W ≤ _
    nlinarith only [hmoveProduct]
  have hordinary := ordinary_crossing_lt W Q S O hα hα1 hhost horder hcross
  have hordinary' : (((host W).interedges (clusterUnion (padAssignment (assignment W)) O.D.V1)
      (clusterUnion (padAssignment (assignment W)) O.D.V2)).card : ℝ) <
      2 * coefficient (α := α) * (q : ℝ) ^ 2 := by
    convert hordinary using 1
    congr!
  have hqpos : 0 < q := by
    have h := W.five_ordinaryParts_le_host
    have hp := W.ordinaryParts_pos
    omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hparameter := mul_lt_mul_of_pos_right (cut_coefficient_lt hα hα1) (sq_pos_of_pos hqR)
  change ((G0.interedges A B).card : ℝ) < (α : ℝ) * (q : ℝ) ^ 2
  have hrestored := hrestoreR.trans_lt (add_lt_add_of_lt_of_le
    (add_lt_add_of_lt_of_le hordinary' hcleanup) hdeleted)
  have hcombined := hrebalanceR.trans_lt (add_lt_add_of_lt_of_le hrestored hmove)
  have heq : 2 * coefficient (α := α) * (q : ℝ) ^ 2 +
      4 * (degreeError α : ℝ) * (q : ℝ) ^ 2 +
      (2 * (degreeError α : ℝ) + 8 * (fourthRoot α : ℝ) ^ 2) * (q : ℝ) ^ 2 +
      (16 * (eta α : ℝ) + 4 * (degreeError α : ℝ)) * (q : ℝ) ^ 2 =
      (2 * coefficient (α := α) + 16 * (eta α : ℝ) + 10 * (degreeError α : ℝ) +
        8 * (fourthRoot α : ℝ) ^ 2) * (q : ℝ) ^ 2 := by ring
  rw [heq] at hcombined
  exact hcombined.trans hparameter

end Erdos547b.ZhaoSourceSparseCut

#print axioms Erdos547b.ZhaoSourceSparseCut.exists_balanced_sparse_cut
