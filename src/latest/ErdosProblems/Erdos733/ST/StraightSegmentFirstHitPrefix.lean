import ErdosProblems.Erdos733.ST.Preamble
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.IntermediateValue

open Classical
noncomputable section

-- [TABLET NODE: StraightSegmentFirstHitPrefix]
lemma StraightSegmentFirstHitPrefix
    (a b u v : EuclideanSpace ℝ (Fin 2))
    (U : Set (EuclideanSpace ℝ (Fin 2)))
    (hUopen : IsOpen U)
    (hsegment_subset_U : segment ℝ a b ⊆ U)
    (hu_not : u ∉ segment ℝ a b)
    (hsegment_hit :
      (segment ℝ u v ∩ segment ℝ a b).Nonempty) :
    ∃ y : EuclideanSpace ℝ (Fin 2),
      y ∈ segment ℝ u v ∧ y ∈ U ∧ y ∉ segment ℝ a b ∧
        IsConnected (segment ℝ u y) ∧
          u ∈ segment ℝ u y ∧ y ∈ segment ℝ u y ∧
            segment ℝ u y ⊆
              segment ℝ u v ∩ (segment ℝ a b)ᶜ := by
-- BODY
  let S : Set (EuclideanSpace ℝ (Fin 2)) := segment ℝ a b
  have hScompact : IsCompact S := by
    dsimp [S]
    rw [segment_eq_image' ℝ a b]
    exact
      (isCompact_Icc.image
        (by
          fun_prop :
            Continuous
              (fun θ : ℝ =>
                a + θ • (b - a))))
  have hSclosed : IsClosed S := hScompact.isClosed
  have hSconvex : Convex ℝ S := by
    dsimp [S]
    exact convex_segment a b
  have hSU : S ⊆ U := hsegment_subset_U
  have huS : u ∉ S := by
    simpa [S] using hu_not
  have hsegS : (segment ℝ u v ∩ S).Nonempty := by
    simpa [S] using hsegment_hit
  rcases hsegS with ⟨z, hzseg, hzS⟩
  have hSnonempty : S.Nonempty := ⟨z, hzS⟩
  rcases hScompact.exists_thickening_subset_open hUopen hSU with
    ⟨ε, hεpos, hεU⟩
  have hdistu_pos : 0 < Metric.infDist u S :=
    (hSclosed.notMem_iff_infDist_pos hSnonempty).mp huS
  let δ : ℝ := min ε (Metric.infDist u S) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_lt_ε : δ < ε := by
    dsimp [δ]
    have hmin_le : min ε (Metric.infDist u S) ≤ ε := min_le_left _ _
    nlinarith [hεpos, hdistu_pos, hmin_le]
  have hδ_lt_distu : δ < Metric.infDist u S := by
    dsimp [δ]
    have hmin_le : min ε (Metric.infDist u S) ≤ Metric.infDist u S :=
      min_le_right _ _
    nlinarith [hεpos, hdistu_pos, hmin_le]
  let f : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun t => AffineMap.lineMap u z t
  let d : ℝ → ℝ := fun t => Metric.infDist (f t) S
  have hd_cont : Continuous d := by
    exact (Metric.continuous_infDist_pt (s := S)).comp
      (AffineMap.lineMap_continuous (p := u) (q := z))
  have hd0 : d 0 = Metric.infDist u S := by
    simp [d, f]
  have hd1 : d 1 = 0 := by
    simp [d, f, Metric.infDist_zero_of_mem hzS]
  have hδ_mem : δ ∈ Set.Icc (d 1) (d 0) := by
    constructor
    · rw [hd1]
      exact hδpos.le
    · rw [hd0]
      exact hδ_lt_distu.le
  rcases
      (intermediate_value_Icc'
        (show (0 : ℝ) ≤ 1 by norm_num) hd_cont.continuousOn) hδ_mem with
    ⟨t, htIcc, hdt⟩
  let y : EuclideanSpace ℝ (Fin 2) := f t
  have hy_dist : Metric.infDist y S = δ := by
    simpa [y, d] using hdt
  have hyt_near : y ∈ Metric.thickening ε S := by
    rw [Metric.mem_thickening_iff_infDist_lt hSnonempty]
    simpa [hy_dist] using hδ_lt_ε
  have hyU : y ∈ U := hεU hyt_near
  have hyNotS : y ∉ S := by
    intro hyS
    have hzero : Metric.infDist y S = 0 := Metric.infDist_zero_of_mem hyS
    linarith
  have hz_uv : Wbtw ℝ u z v := by
    exact (mem_segment_iff_wbtw).mp hzseg
  have hy_uz : Wbtw ℝ u y z := by
    rw [wbtw_lineMap_iff]
    exact Or.inr htIcc
  have hy_uv : y ∈ segment ℝ u v := by
    exact (hz_uv.trans_left hy_uz).mem_segment
  refine
    ⟨y, hy_uv, hyU, by simpa [S] using hyNotS, ?_,
      left_mem_segment ℝ u y, right_mem_segment ℝ u y, ?_⟩
  · exact (convex_segment u y).isConnected ⟨u, left_mem_segment ℝ u y⟩
  · intro w hwuy
    constructor
    · exact
        (convex_segment u v).segment_subset
          (left_mem_segment ℝ u v) hy_uv hwuy
    · intro hwS_original
      have hwS : w ∈ S := by
        simpa [S] using hwS_original
      have hw_uy : Wbtw ℝ u w y := by
        exact (mem_segment_iff_wbtw).mp hwuy
      have hy_wz : Wbtw ℝ w y z := hy_uz.trans_left_right hw_uy
      exact hyNotS (hSconvex.mem_of_wbtw hy_wz hwS hzS)

