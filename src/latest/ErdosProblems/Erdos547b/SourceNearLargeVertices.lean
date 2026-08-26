/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RegularRowConcentration
import ErdosProblems.Erdos547b.SourceDegreeFormRootRows

/-! # Actual near-large vertices in each source large cluster -/

open scoped SimpleGraph BigOperators Classical
noncomputable section

namespace Erdos547b.ZhaoSourceNearLargeVertices

open Finset SimpleGraph Erdos547EC2 Erdos547b.ZhaoStability Erdos547b.ZhaoDegreeForm
open Erdos547b.ZhaoSourceDegreeFormRootRows Erdos547b.ZhaoSourceDegreeFormBounds
open Erdos547b.ZhaoSourceParameterSchedule Erdos547b.ZhaoQuantitativeLargeClusters
open Erdos547b.ZhaoClusterDegreeAccounting Erdos547b.ZhaoRegularRowConcentration

theorem concentration_error_margin {α : ℚ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) :
    4 * (epsilon α + rootTypicality α) ≤ degreeError α := by
  obtain ⟨_, _, _, _, hd, _, hg, _⟩ := parameter_pos hα
  obtain ⟨_, _, _, _, _, hgd, hepg⟩ := parameter_upper_bounds hα hα1
  have hd1 := (reservoir_cleanup_bounds hα hα1).2.2.2.2.2
  have hg1 : gamma α ≤ 1 := by linarith only [hgd, hd1]
  have hg6 : gamma α ^ 6 ≤ gamma α := pow_succ_le_self hg.le hg1 5
  unfold rootTypicality
  linarith only [hg6, hgd, hepg, hd]

variable {α : ℚ} {hostN q M : ℕ}
variable {G : SimpleGraph (Fin hostN)} [DecidableRel G.Adj]
variable (W : Witness α q M G)

local instance : DecidableRel W.graph.Adj := W.graph_decidable

private theorem uniform_real_of_rat
    {V : Type*} (H : SimpleGraph V) [DecidableRel H.Adj]
    {ε : ℚ} {X Y : Finset V} (h : H.IsUniform ε X Y) : H.IsUniform (ε : ℝ) X Y := by
  intro X' hX Y' hY hXlarge hYlarge
  have hXQ : (X.card : ℚ) * ε ≤ (X'.card : ℚ) := by exact_mod_cast hXlarge
  have hYQ : (Y.card : ℚ) * ε ≤ (Y'.card : ℚ) := by exact_mod_cast hYlarge
  exact_mod_cast h hX hY hXQ hYQ

theorem graph_pair_uniform (C j : Index W) :
    W.graph.IsUniform (epsilon α : ℝ)
      (clusterVertices (assignment W) C) (clusterVertices (assignment W) j) := by
  apply uniform_real_of_rat
  simpa only [clusterVertices_partitionAssignment] using W.pair_uniform C j

def nearLargeBad (C : Index W) : Finset (Fin hostN) :=
  lowerBad W.graph (clusterVertices (assignment W) C) Finset.univ
    (clusterVertices (assignment W)) (epsilon α : ℝ) (rootTypicality α : ℝ)

theorem nearLargeBad_subset (C : Index W) :
    nearLargeBad W C ⊆ clusterVertices (assignment W) C := Finset.filter_subset _ _

theorem nearLargeBad_card (hα : 0 < α) (hα1 : α ≤ 1 / 4) (C : Index W) :
    ((nearLargeBad W C).card : ℝ) ≤ (rootTypicality α : ℝ) * W.clusterSize := by
  have h := card_lowerBad_le W.graph (clusterVertices (assignment W) C) Finset.univ
    (clusterVertices (assignment W)) (epsilon α : ℝ) (rootTypicality α : ℝ)
    (by exact_mod_cast (rootTypicality_margin hα hα1).1)
    (by exact_mod_cast (rootTypicality_sq α).symm.le)
    (fun j _ => graph_pair_uniform W C j)
  simpa only [nearLargeBad, clusterVertices_partitionAssignment, W.equal_clusters C.val C.property] using h

theorem nearLarge_degree
    (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hhost : hostN = 2 * q)
    (horder : orderThreshold α M ≤ q) (C : Index W) (hC : C ∈ large W)
    {v : Fin hostN} (hv : v ∈ clusterVertices (assignment W) C) (hbad : v ∉ nearLargeBad W C) :
    (1 - 5 * (degreeError α : ℝ)) * q ≤ (G.degree v : ℝ) := by
  let A := clusterVertices (assignment W) C
  let whole := clusterVertices (assignment W)
  let J : Finset (Index W) := Finset.univ
  let B := upperBad W.graph A J whole (epsilon α : ℝ) (rootTypicality α : ℝ)
  have hN (j : Index W) : (whole j).card = W.clusterSize := by
    change (clusterVertices (assignment W) j).card = _
    rw [clusterVertices_partitionAssignment]
    exact W.equal_clusters j.val j.property
  have hδ : (0 : ℝ) < rootTypicality α := by exact_mod_cast (rootTypicality_margin hα hα1).1
  have hε : (0 : ℝ) ≤ epsilon α := by exact_mod_cast (parameter_pos hα).2.2.2.2.2.2.2.le
  have hεδ : (epsilon α : ℝ) ≤ (rootTypicality α : ℝ) ^ 2 := by
    exact_mod_cast (rootTypicality_sq α).symm.le
  have hB : (B.card : ℝ) ≤ (rootTypicality α : ℝ) * W.clusterSize := by
    have h := card_upperBad_le W.graph A J whole (epsilon α : ℝ) (rootTypicality α : ℝ)
      hδ hεδ (fun j _ => graph_pair_uniform W C j)
    exact h.trans_eq (congrArg (fun n : ℕ => (rootTypicality α : ℝ) * n) (hN C))
  obtain ⟨pool, hpool, hpoolCard, hpoolHigh⟩ :=
    exists_reservoir_card_eq (assignment W) G q (sourceQuota W) hC
  have hδsmall : (rootTypicality α : ℝ) < 2 * (fourthRoot α : ℝ) ^ 2 := by
    have hm : 4 * (rootTypicality α : ℝ) < (fourthRoot α : ℝ) ^ 2 / 2 := by
      exact_mod_cast (rootTypicality_margin hα hα1).2
    nlinarith only [hm, hδ]
  have hpoolLarge : (rootTypicality α : ℝ) * W.clusterSize < pool.card := by
    rw [hpoolCard]
    exact (mul_lt_mul_of_pos_right hδsmall
      (by exact_mod_cast W.clusterSize_pos)).trans_le (Nat.le_ceil _)
  have hBpool : B.card < pool.card := by exact_mod_cast hB.trans_lt hpoolLarge
  obtain ⟨z, hz, hzB⟩ := Finset.exists_mem_notMem_of_card_lt_card hBpool
  have hu := upper_sum_le W.graph A J whole (epsilon α : ℝ) (rootTypicality α : ℝ)
    W.clusterSize (fun j _ => hN j) hε (hpool hz) hzB
  have hl := lower_sum_le W.graph A J whole (epsilon α : ℝ) (rootTypicality α : ℝ)
    W.clusterSize (fun j _ => hN j) hε hv hbad
  have hretNat : q ≤ W.graph.degree z + W.loss :=
    ((highDegree_iff_pruneSmallEdges_highDegree G q z).mpr (hpoolHigh z hz)).trans (W.degree_loss z)
  have hret : (q : ℝ) ≤ (W.graph.degree z : ℝ) + W.loss := by exact_mod_cast hretNat
  have hupper : (W.graph.degree z : ℝ) ≤ (W.exceptional.card : ℝ) +
      ∑ j ∈ J, (degreeInto W.graph z (whole j) : ℝ) := by
    have h := degree_le_exceptional_add_sum (assignment W) W.graph z
    rw [exceptionalVertices_partitionAssignment] at h
    exact_mod_cast h
  have hlower : (∑ j ∈ J, (degreeInto W.graph v (whole j) : ℝ)) ≤ (G.degree v : ℝ) := by
    have h := (sum_degreeInto_le_degree (assignment W) W.graph J v).trans
      (degree_le_of_le (v := v) (W.graph_le.trans (pruneSmallEdges_le G _)))
    exact_mod_cast h
  have hvolume : (W.clusterSize : ℝ) * J.card ≤ 2 * (q : ℝ) := by
    have h := clusterVolume_le_card (assignment W) W.clusterSize hN
    have h' : Fintype.card (Index W) * W.clusterSize ≤ 2 * q :=
      h.trans_eq ((Fintype.card_fin hostN).trans hhost)
    have hc : J.card = Fintype.card (Index W) := Finset.card_univ
    rw [hc]
    exact_mod_cast (by simpa only [Nat.mul_comm] using h')
  have hmargin : 4 * ((epsilon α : ℝ) + (rootTypicality α : ℝ)) ≤ degreeError α := by
    exact_mod_cast concentration_error_margin hα hα1
  have hcost := mul_le_mul_of_nonneg_left hvolume (add_nonneg hε hδ.le)
  have hmarginq := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hcleanup : (W.exceptional.card : ℝ) < (degreeError α : ℝ) * q ∧
      (W.loss : ℝ) < (degreeError α : ℝ) * q := by
    subst hostN
    have h := degreeForm_source_bounds hα hα1 W horder
    exact ⟨h.1, h.2.1⟩
  have hdq := mul_nonneg (show (0 : ℝ) ≤ degreeError α by
    exact_mod_cast (parameter_pos hα).2.2.2.2.1.le) (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith only [hu, hl, hret, hupper, hlower, hcost, hmarginq, hcleanup.1, hcleanup.2, hdq]

end Erdos547b.ZhaoSourceNearLargeVertices

#print axioms Erdos547b.ZhaoSourceNearLargeVertices.concentration_error_margin
#print axioms Erdos547b.ZhaoSourceNearLargeVertices.nearLargeBad_card
#print axioms Erdos547b.ZhaoSourceNearLargeVertices.nearLarge_degree
