/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceCutGeometry
import ErdosProblems.Erdos547b.CutRestoration

/-! # Actual cleanup and whole-pair deletion costs for the final sparse cut -/

open scoped SimpleGraph Classical
noncomputable section
namespace Erdos547b.ZhaoSourceCutLosses

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceParameterSchedule
open Erdos547b.ZhaoSourceDegreeFormBounds Erdos547b.ZhaoSection6RichHierarchy
open Erdos547b.ZhaoClusterPairPruning Erdos547b.ZhaoPrunedReducedLargeEdges
open Erdos547b.ZhaoClusterDegreeAccounting Erdos547b.ZhaoSourceOrdinaryCut

theorem cut_coefficient_lt {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    2 * coefficient (α := α) + 16 * (eta α : ℝ) + 10 * (degreeError α : ℝ) +
      8 * (fourthRoot α : ℝ) ^ 2 < (α : ℝ) := by
  have hu := parameter_upper_bounds hα hα1
  have hc := reservoir_cleanup_bounds hα hα1
  have h : 32 * (rho α + rhoOne α) + 24 * eta α + 10 * degreeError α +
      8 * fourthRoot α ^ 2 < α := by
    have hr1 : rhoOne α = α / 1000 := rfl
    linarith only [hr1, hu.2.1, hu.2.2.1, hc.2.2.1, hc.2.2.2.1, hα]
  have hR : 32 * ((rho α : ℝ) + (rhoOne α : ℝ)) + 24 * (eta α : ℝ) +
      10 * (degreeError α : ℝ) + 8 * (fourthRoot α : ℝ) ^ 2 < (α : ℝ) := by exact_mod_cast h
  unfold coefficient
  linarith only [hR]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

theorem cleanup_bounds (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    (W.exceptional.card : ℝ) < (degreeError α : ℝ) * q ∧
      (W.loss : ℝ) < (degreeError α : ℝ) * q ∧
      (W.clusterSize : ℝ) ≤ (degreeError α : ℝ) * q / 500 := by
  subst hostN
  exact degreeForm_source_bounds hα hα1 W horder

theorem nonlarge_error_le (hα : 0 < α) (hhost : hostN = 2 * q) :
    (nonLargeHighError (assignment W) G q (sourceQuota W) : ℝ) ≤
      4 * (fourthRoot α : ℝ) ^ 2 * q := by
  have ht : (0 : ℝ) < fourthRoot α := by exact_mod_cast (parameter_pos hα).2.2.2.1
  have hquota : ((sourceQuota W - 1 : ℕ) : ℝ) ≤ 2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize :=
    (richQuota_sub_one_cast_lt (sq_pos_of_pos ht) W.clusterSize_pos).le
  have he : (nonLargeHighError (assignment W) G q (sourceQuota W) : ℝ) ≤
      (Fintype.card (Index W) : ℝ) * (sourceQuota W - 1 : ℕ) := by
    exact_mod_cast nonLargeHighError_le_card_mul (assignment W) G q (sourceQuota W)
  have hscale := mul_le_mul_of_nonneg_left hquota
    (Nat.cast_nonneg (Fintype.card (Index W)) : (0 : ℝ) ≤ _)
  have hvolNat := clusterVolume_le_card (assignment W) W.clusterSize (fun i => by
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters i.val i.property)
  have hvolNat' : Fintype.card (Index W) * W.clusterSize ≤ 2 * q :=
    hvolNat.trans_eq ((Fintype.card_fin _).trans hhost)
  have hvol : (Fintype.card (Index W) : ℝ) * W.clusterSize ≤ 2 * q := by exact_mod_cast hvolNat'
  have hvol' := mul_le_mul_of_nonneg_left hvol (by positivity : 0 ≤ 2 * (fourthRoot α : ℝ) ^ 2)
  nlinarith only [he, hscale, hvol']

local instance : DecidableRel W.graph.Adj := W.graph_decidable

theorem pair_deleted_edges_le (hα : 0 < α) (hα1 : α ≤ 1 / 4)
    (hhost : hostN = 2 * q) (horder : orderThreshold α M ≤ q) :
    ((W.graph.edgeFinset \ (host W).edgeFinset).card : ℝ) ≤
      (2 * (degreeError α : ℝ) + 8 * (fourthRoot α : ℝ) ^ 2) * (q : ℝ) ^ 2 := by
  have h := quantitative_card_deleted_edges_le (assignment W) G W.graph q (sourceQuota W) W.graph_le
  change (W.graph.edgeFinset \ (host W).edgeFinset).card ≤
    ((exceptionalVertices (assignment W)).card + nonLargeHighError (assignment W) G q (sourceQuota W)) *
      Fintype.card (Fin hostN) at h
  rw [exceptionalVertices_partitionAssignment, Fintype.card_fin] at h
  have h' := h.trans_eq (congrArg
    (fun m => (W.exceptional.card + nonLargeHighError (assignment W) G q (sourceQuota W)) * m) hhost)
  have hR : ((W.graph.edgeFinset \ (host W).edgeFinset).card : ℝ) ≤
      ((W.exceptional.card : ℝ) + nonLargeHighError (assignment W) G q (sourceQuota W)) * (2 * q) := by
    exact_mod_cast h'
  have he := (cleanup_bounds W hα hα1 hhost horder).1
  have hn := nonlarge_error_le W hα hhost
  have hsum : (W.exceptional.card : ℝ) + nonLargeHighError (assignment W) G q (sourceQuota W) ≤
      ((degreeError α : ℝ) + 4 * (fourthRoot α : ℝ) ^ 2) * q := by linarith only [he, hn]
  have hm := mul_le_mul_of_nonneg_right hsum (by positivity : (0 : ℝ) ≤ 2 * q)
  nlinarith only [hR, hm]

end Erdos547b.ZhaoSourceCutLosses

#print axioms Erdos547b.ZhaoSourceCutLosses.cut_coefficient_lt
#print axioms Erdos547b.ZhaoSourceCutLosses.nonlarge_error_le
#print axioms Erdos547b.ZhaoSourceCutLosses.pair_deleted_edges_le
