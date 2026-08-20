import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import ErdosProblems.Erdos733.ST.PolygonalArc
import ErdosProblems.Erdos733.ST.PolygonalPath

open Classical
noncomputable section

-- [TABLET NODE: ArcCrossingFirstSegmentPrefixPoint]
lemma ArcCrossingFirstSegmentPrefixPoint
    (δ : PolygonalArc) (α : PolygonalPath) (j : ℕ)
    (hj : j + 1 < δ.vertices.length) :
    Set.Finite (α.carrier ∩ δ.carrier) →
      (α.carrier ∩ segment ℝ δ.vertices[j] δ.vertices[j + 1]).Nonempty →
        δ.vertices[j] ∉ α.carrier →
          δ.vertices[j + 1] ∉ α.carrier →
            ∃ c : EuclideanSpace ℝ (Fin 2),
              c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] ∧
                c ≠ δ.vertices[j] ∧
                  c ≠ δ.vertices[j + 1] ∧
                    c ∉ α.carrier ∧
                      segment ℝ δ.vertices[j] c ⊆
                        segment ℝ δ.vertices[j] δ.vertices[j + 1] ∩ α.carrierᶜ := by
-- BODY
  intro hXfiniteδ hhit hu_not hv_not
  let u : EuclideanSpace ℝ (Fin 2) := δ.vertices[j]
  let v : EuclideanSpace ℝ (Fin 2) := δ.vertices[j + 1]
  let X : Set (EuclideanSpace ℝ (Fin 2)) := α.carrier ∩ segment ℝ u v
  have hseg_subsetδ : segment ℝ u v ⊆ δ.carrier := by
    intro p hp
    rw [δ.carrier_eq]
    exact ⟨j, hj, by simpa [u, v] using hp⟩
  have hXfinite : Set.Finite X := by
    refine hXfiniteδ.subset ?_
    intro p hp
    exact ⟨hp.1, hseg_subsetδ hp.2⟩
  have hXnonempty : X.Nonempty := by
    simpa [X, u, v] using hhit
  have hXfin_nonempty : hXfinite.toFinset.Nonempty :=
    (Set.Finite.toFinset_nonempty hXfinite).2 hXnonempty
  obtain ⟨x0, hx0fin, hx0_min⟩ :=
    Finset.exists_min_image hXfinite.toFinset (fun x => dist u x) hXfin_nonempty
  have hx0X : x0 ∈ X := (Set.Finite.mem_toFinset hXfinite).1 hx0fin
  have hx0α : x0 ∈ α.carrier := hx0X.1
  have hx0seg : x0 ∈ segment ℝ u v := hx0X.2
  have hx0_ne_u : x0 ≠ u := by
    intro hx
    exact hu_not (by simpa [u, hx] using hx0α)
  have hx0_ne_v : x0 ≠ v := by
    intro hx
    exact hv_not (by simpa [v, hx] using hx0α)
  let c : EuclideanSpace ℝ (Fin 2) := midpoint ℝ u x0
  have hc_mid : c = midpoint ℝ u x0 := rfl
  have hc_seg_ux : c ∈ segment ℝ u x0 := by
    simpa [c] using midpoint_mem_segment (𝕜 := ℝ) u x0
  have hc_seg_uv : c ∈ segment ℝ u v := by
    exact (convex_segment u v).segment_subset
      (left_mem_segment ℝ u v) hx0seg hc_seg_ux
  have hdist_x0_pos : 0 < dist u x0 := by
    exact dist_pos.2 (by simpa [ne_eq, eq_comm] using hx0_ne_u)
  have hdist_c_eq : dist u c = (1 / 2 : ℝ) * dist u x0 := by
    simpa [c, invOf_eq_inv, Real.norm_ofNat, one_div] using
      (dist_left_midpoint (𝕜 := ℝ) u x0)
  have hdist_c_lt_x0 : dist u c < dist u x0 := by
    rw [hdist_c_eq]
    nlinarith [hdist_x0_pos]
  have hdist_c_pos : 0 < dist u c := by
    rw [hdist_c_eq]
    nlinarith [hdist_x0_pos]
  have hc_ne_u : c ≠ u := by
    intro hcu
    rw [hcu, dist_self] at hdist_c_pos
    exact (lt_irrefl (0 : ℝ)) hdist_c_pos
  have hx0_dist_le_v : dist u x0 ≤ dist u v := by
    have hball : x0 ∈ Metric.closedBall u (dist u v) := by
      exact (convex_closedBall u (dist u v)).segment_subset
        (by simp [Metric.mem_closedBall])
        (by simp [Metric.mem_closedBall, dist_comm])
        hx0seg
    simpa [Metric.mem_closedBall, dist_comm] using hball
  have hc_ne_v : c ≠ v := by
    intro hcv
    have hdist_v : dist u v = dist u c := by simp [hcv]
    nlinarith [hx0_dist_le_v, hdist_c_lt_x0]
  have hc_notα : c ∉ α.carrier := by
    intro hcα
    have hcX : c ∈ X := ⟨hcα, hc_seg_uv⟩
    have hcfin : c ∈ hXfinite.toFinset :=
      (Set.Finite.mem_toFinset hXfinite).2 hcX
    have hmin := hx0_min c hcfin
    nlinarith [hmin, hdist_c_lt_x0]
  have hprefix_subset :
      segment ℝ u c ⊆ segment ℝ u v ∩ α.carrierᶜ := by
    intro w hw
    have hwseg_uv : w ∈ segment ℝ u v :=
      (convex_segment u v).segment_subset
        (left_mem_segment ℝ u v) hc_seg_uv hw
    refine ⟨hwseg_uv, ?_⟩
    intro hwα
    have hwX : w ∈ X := ⟨hwα, hwseg_uv⟩
    have hwfin : w ∈ hXfinite.toFinset :=
      (Set.Finite.mem_toFinset hXfinite).2 hwX
    have hmin := hx0_min w hwfin
    have hw_dist_le_c : dist u w ≤ dist u c := by
      have hball : w ∈ Metric.closedBall u (dist u c) := by
        exact (convex_closedBall u (dist u c)).segment_subset
          (by simp [Metric.mem_closedBall])
          (by simp [Metric.mem_closedBall, dist_comm])
          hw
      simpa [Metric.mem_closedBall, dist_comm] using hball
    nlinarith [hmin, hw_dist_le_c, hdist_c_lt_x0]
  refine ⟨c, by simpa [u, v] using hc_seg_uv, ?_, ?_, ?_, ?_⟩
  · simpa [u] using hc_ne_u
  · simpa [v] using hc_ne_v
  · exact hc_notα
  · simpa [u, v] using hprefix_subset
