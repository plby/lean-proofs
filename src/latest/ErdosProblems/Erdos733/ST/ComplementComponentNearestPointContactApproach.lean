import ErdosProblems.Erdos733.ST.ComplementComponent
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Affine.AddTorsor

open Classical
noncomputable section

-- [TABLET NODE: ComplementComponentNearestPointContactApproach]
lemma ComplementComponentNearestPointContactApproach
    (K C : Set (EuclideanSpace ℝ (Fin 2)))
    (p x : EuclideanSpace ℝ (Fin 2)) :
    ComplementComponent K C →
      p ∈ C →
        x ∈ K →
          Metric.infDist p K = dist p x →
            ∀ U : Set (EuclideanSpace ℝ (Fin 2)),
              IsOpen U → x ∈ U →
                ∃ y, y ∈ C ∧ y ∈ U ∧ y ∈ Kᶜ ∧ y ≠ x := by
-- BODY
  intro hC hpC hxK hnearest U hUopen hxU
  rcases hC with ⟨_hCne, hCcompl, hCconn, hCmax⟩
  have hpCompl : p ∈ Kᶜ := hCcompl hpC
  have hpx_ne : p ≠ x := by
    intro hpx
    exact hpCompl (hpx.symm ▸ hxK)
  have hdist_pos : 0 < dist p x := dist_pos.mpr hpx_ne
  rcases Metric.isOpen_iff.1 hUopen x hxU with ⟨ε, hεpos, hεball⟩
  let δ : ℝ := min (1 / 2) (ε / (2 * dist p x))
  have hδpos : 0 < δ := by
    have hdenpos : 0 < 2 * dist p x := mul_pos (by norm_num) hdist_pos
    exact lt_min (by norm_num) (div_pos hεpos hdenpos)
  have hδle_half : δ ≤ 1 / 2 := min_le_left _ _
  have hδlt_one : δ < 1 := by
    exact lt_of_le_of_lt hδle_half (by norm_num)
  have hδle_eps : δ ≤ ε / (2 * dist p x) := min_le_right _ _
  let t : ℝ := 1 - δ
  have htpos : 0 < t := by
    dsimp [t]
    linarith
  have htlt : t < 1 := by
    dsimp [t]
    linarith
  let y : EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap p x t
  have hy_ne_x : y ≠ x := by
    intro hyx
    have hdist_yx : dist y x = δ * dist p x := by
      calc
        dist y x = ‖1 - t‖ * dist p x := by
          simpa [y] using dist_lineMap_right p x t
        _ = δ * dist p x := by
          have hnonneg : 0 ≤ δ := hδpos.le
          simp [t, abs_of_nonneg hnonneg]
    have hδ_mul_pos : 0 < δ * dist p x := mul_pos hδpos hdist_pos
    have : (0 : ℝ) = δ * dist p x := by
      simpa [hyx] using hdist_yx
    linarith
  have hydist_lt : dist p y < dist p x := by
    calc
      dist p y = ‖t‖ * dist p x := by
        simpa [y] using dist_left_lineMap p x t
      _ = t * dist p x := by
        simp [Real.norm_eq_abs, abs_of_nonneg htpos.le]
      _ < 1 * dist p x := by
        exact mul_lt_mul_of_pos_right htlt hdist_pos
      _ = dist p x := by ring
  have hyCompl : y ∈ Kᶜ := by
    have : dist p y < Metric.infDist p K := by
      simpa [hnearest] using hydist_lt
    exact Metric.notMem_of_dist_lt_infDist this
  have hyU : y ∈ U := by
    apply hεball
    have hdist_yx : dist y x = δ * dist p x := by
      calc
        dist y x = ‖1 - t‖ * dist p x := by
          simpa [y] using dist_lineMap_right p x t
        _ = δ * dist p x := by
          have hnonneg : 0 ≤ δ := hδpos.le
          simp [t, abs_of_nonneg hnonneg]
    have hmul_le : δ * dist p x ≤ ε / 2 := by
      have hdenpos : 0 < 2 * dist p x := mul_pos (by norm_num) hdist_pos
      have := mul_le_mul_of_nonneg_right hδle_eps hdist_pos.le
      calc
        δ * dist p x ≤ (ε / (2 * dist p x)) * dist p x := this
        _ = ε / 2 := by
          field_simp [hdist_pos.ne']
    have hεhalf_lt : ε / 2 < ε := by linarith
    exact hdist_yx.trans_lt (lt_of_le_of_lt hmul_le hεhalf_lt)
  have hsegCompl : segment ℝ p y ⊆ Kᶜ := by
    intro z hz
    have hzclosed : z ∈ Metric.closedBall p (dist p y) :=
      segment_subset_closedBall_left p y hz
    have hzdist_le : dist p z ≤ dist p y :=
      by simpa [dist_comm] using (Metric.mem_closedBall.mp hzclosed)
    have hzdist_lt : dist p z < Metric.infDist p K := by
      exact lt_of_le_of_lt hzdist_le (by simpa [hnearest] using hydist_lt)
    exact Metric.notMem_of_dist_lt_infDist hzdist_lt
  have hsegConn : IsConnected (segment ℝ p y) := by
    refine ⟨?_, (convex_segment p y).isPreconnected⟩
    exact ⟨p, left_mem_segment ℝ p y⟩
  have hUnionNonempty : (C ∪ segment ℝ p y).Nonempty := by
    exact ⟨p, Or.inl hpC⟩
  have hUnionSubset : C ∪ segment ℝ p y ⊆ Kᶜ := by
    intro z hz
    rcases hz with hzC | hzSeg
    · exact hCcompl hzC
    · exact hsegCompl hzSeg
  have hUnionConn : IsConnected (C ∪ segment ℝ p y) := by
    have hmeet : (C ∩ segment ℝ p y).Nonempty :=
      ⟨p, hpC, left_mem_segment ℝ p y⟩
    exact IsConnected.union hmeet hCconn hsegConn
  have hCsubsetUnion : C ⊆ C ∪ segment ℝ p y := fun z hz => Or.inl hz
  have hUnionSubsetC : C ∪ segment ℝ p y ⊆ C :=
    hCmax (C ∪ segment ℝ p y) hUnionNonempty hUnionSubset hUnionConn hCsubsetUnion
  have hyC : y ∈ C := hUnionSubsetC (Or.inr (right_mem_segment ℝ p y))
  exact ⟨y, hyC, hyU, hyCompl, hy_ne_x⟩
