/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.SourceNearLargeVertices
import ErdosProblems.Erdos547b.SourceFreshChunkBounds

/-! # The two actual, disjoint, rounded midpoint reservoirs -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceMidpointReservoirs

open Finset SimpleGraph Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoSourceNearLargeVertices Erdos547b.ZhaoSourceFreshChunkBounds

theorem reservoir_coefficient_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    2 * fourthRoot α ^ 2 + rootTypicality α + 2 * epsilon α ≤ 1 := by
  obtain ⟨hσ, hσsmall, _, hd, he, _⟩ := reservoir_cleanup_bounds hα hα1
  have hδ := (rootTypicality_margin hα hα1).2
  linarith only [hσ, hσsmall, hd, he, hδ]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

structure Reservoirs (C : Index W) where
  high : Finset (Fin hostN)
  low : Finset (Fin hostN)
  high_subset : high ⊆ clusterVertices (assignment W) C
  low_subset : low ⊆ clusterVertices (assignment W) C
  disjoint : Disjoint high low
  high_card : high.card = sourceQuota W
  low_card : (W.clusterSize : ℝ) ≤ (low.card : ℝ) + sourceQuota W +
    (rootTypicality α : ℝ) * W.clusterSize
  high_degree : ∀ z ∈ high, q ≤ G.degree z
  low_degree : ∀ z ∈ low, (1 - 5 * (degreeError α : ℝ)) * q ≤ (G.degree z : ℝ)

theorem exists_reservoirs
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (C : Index W) (hC : C ∈ large W) :
    Nonempty (Reservoirs W C) := by
  obtain ⟨high, hhigh, hcard, hdegree⟩ :=
    exists_reservoir_card_eq (assignment W) G q (sourceQuota W) hC
  let A := clusterVertices (assignment W) C
  let bad := nearLargeBad W C
  let low := A \ (bad ∪ high)
  refine ⟨{
    high := high
    low := low
    high_subset := hhigh
    low_subset := Finset.sdiff_subset
    disjoint := ?_
    high_card := hcard
    low_card := ?_
    high_degree := hdegree
    low_degree := ?_ }⟩
  · apply Finset.disjoint_left.mpr
    intro z hz hzlow
    exact (Finset.mem_sdiff.mp hzlow).2 (Finset.mem_union_right _ hz)
  · have hsplit := Finset.card_sdiff_add_card_inter A (bad ∪ high)
    change low.card + (A ∩ (bad ∪ high)).card = A.card at hsplit
    have hinter := (Finset.card_le_card (Finset.inter_subset_right : A ∩ (bad ∪ high) ⊆ bad ∪ high)).trans
      (Finset.card_union_le bad high)
    have hN : A.card = W.clusterSize := by
      change (clusterVertices (assignment W) C).card = _
      rw [clusterVertices_partitionAssignment]
      exact W.equal_clusters C.val C.property
    have hnat : W.clusterSize ≤ low.card + high.card + bad.card := by omega
    have hreal : (W.clusterSize : ℝ) ≤ (low.card : ℝ) + sourceQuota W + bad.card := by
      rw [hcard] at hnat
      exact_mod_cast hnat
    exact hreal.trans (add_le_add le_rfl (nearLargeBad_card W hα hα1 C))
  · intro z hz
    exact nearLarge_degree W hα hα1 hhost horder C hC (Finset.mem_sdiff.mp hz).1
      (fun h => (Finset.mem_sdiff.mp hz).2 (Finset.mem_union_left _ h))

variable {C : Index W} (R : Reservoirs W C)

theorem high_large (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    (epsilon α : ℝ) * W.clusterSize ≤ (R.high.card : ℝ) := by
  obtain ⟨hσ, _, _, hd, he, _⟩ := reservoir_cleanup_bounds hα hα1
  have hεσ : (epsilon α : ℝ) ≤ 2 * (fourthRoot α : ℝ) ^ 2 := by
    exact_mod_cast (show epsilon α ≤ 2 * fourthRoot α ^ 2 by linarith only [hσ, hd, he])
  rw [R.high_card]
  exact (mul_le_mul_of_nonneg_right hεσ (Nat.cast_nonneg W.clusterSize)).trans (Nat.le_ceil _)

theorem low_large (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) :
    (epsilon α : ℝ) * W.clusterSize ≤ (R.low.card : ℝ) := by
  have hceil : (sourceQuota W : ℝ) < 2 * (fourthRoot α : ℝ) ^ 2 * W.clusterSize + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hscale : (2 : ℝ) < (epsilon α : ℝ) * W.clusterSize := by
    subst hostN
    exact epsilon_mul_clusterSize_gt_two hα hα1 W horder
  have hm : 2 * (fourthRoot α : ℝ) ^ 2 + (rootTypicality α : ℝ) + 2 * (epsilon α : ℝ) ≤ 1 := by
    exact_mod_cast reservoir_coefficient_margin hα hα1
  have hmN := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg W.clusterSize : (0 : ℝ) ≤ W.clusterSize)
  nlinarith only [hceil, hscale, hmN, R.low_card]

end Erdos547b.ZhaoSourceMidpointReservoirs

#print axioms Erdos547b.ZhaoSourceMidpointReservoirs.exists_reservoirs
#print axioms Erdos547b.ZhaoSourceMidpointReservoirs.high_large
#print axioms Erdos547b.ZhaoSourceMidpointReservoirs.low_large
