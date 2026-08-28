import Wikipedia.HopfProblem.DegreeCollapseNonminimumBasinsMeagre
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowTimeDiffeomorph

/-!
# Actual basins as countable unions of smooth coordinate-plane images

The native local basin block gives full open balls in the positive and
negative coordinate planes. Their integer-time translates cover exactly
the complete forward and backward basins, respectively. Every parameter
map is smooth on its actual open ball. The source dimensions are the
original complementary Morse dimensions, not a supplied codimension claim.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_forward_basin_smooth_images
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) :
    ∃ r : ℝ, 0 < r ∧
      (∀ n : ℕ, ContMDiffOn 𝓘(ℝ, (S.data p).chart.PositiveCoordinates) 𝓘(ℝ, E) ∞
        (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v))) (ball 0 r)) ∧
      {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} =
        ⋃ n : ℕ, (fun v => S.flow (-(n : ℝ)) ((S.data p).chart.splitChart.symm (0, v))) ''
          ball (0 : (S.data p).chart.PositiveCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ := exists_descending_morse_basin_block c hf
    (S.smooth.of_le (by simp)) S.flow S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.PositiveCoordinates) (hv : v ∈ ball 0 (r / 2)) :
      (0, v) ∈ c.splitChart.target :=
    hblock ⟨mem_closedBall_self hr.le,
      closedBall_subset_closedBall (by linarith : r / 2 ≤ r) (ball_subset_closedBall hv)⟩
  have hlocal : ContMDiffOn 𝓘(ℝ, c.PositiveCoordinates) 𝓘(ℝ, E) ∞
      (fun v => c.splitChart.symm (0, v)) (ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp
      (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn htarget
  have hpoint (v : c.PositiveCoordinates) (hv : v ∈ ball 0 (r / 2)) :
      Tendsto (fun t => S.flow t (c.splitChart.symm (0, v))) atTop (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (0, v) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (0, v)) = (0, v) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (0, v)) hs ?_ ?_).1).mpr
    · rw [he]
    · rw [he]
      simpa using hr
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact (SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
      (-(n : ℝ))).contMDiff.comp_contMDiffOn hlocal
  · ext x
    constructor
    · intro hx
      have hlim := hx.comp tendsto_natCast_atTop_atTop
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually (morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (flow_time_atTop_limit_iff S.flow (n : ℝ) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (n : ℝ) x)).1 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).1).mp hnew
      refine mem_iUnion.mpr ⟨n, (c.splitChart (S.flow (n : ℝ) x)).2,
        mem_ball_zero_iff.mpr hp', ?_⟩
      have he : (0, (c.splitChart (S.flow (n : ℝ) x)).2) =
          c.splitChart (S.flow (n : ℝ) x) := Prod.ext hz.symm rfl
      change S.flow (-(n : ℝ))
        (c.splitChart.symm (0, (c.splitChart (S.flow (n : ℝ) x)).2)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (n : ℝ) x)) = S.flow (n : ℝ) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := mem_iUnion.mp hx
      exact (flow_time_atTop_limit_iff S.flow (-(n : ℝ)) (c.splitChart.symm (0, v)) p.val).mpr
        (hpoint v hv)

theorem AdaptedSurgeryWindows.exists_backward_basin_smooth_images
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) :
    ∃ r : ℝ, 0 < r ∧
      (∀ n : ℕ, ContMDiffOn 𝓘(ℝ, (S.data p).chart.NegativeCoordinates) 𝓘(ℝ, E) ∞
        (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0))) (ball 0 r)) ∧
      {x : M | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)} =
        ⋃ n : ℕ, (fun v => S.flow (n : ℝ) ((S.data p).chart.splitChart.symm (v, 0))) ''
          ball (0 : (S.data p).chart.NegativeCoordinates) r := by
  let c := (S.data p).chart
  obtain ⟨r, hr, hblock, hbasin⟩ := exists_descending_morse_basin_block c hf
    (S.smooth.of_le (by simp)) S.flow S.integral S.zero S.descent (S.critical_model_germ p)
  have htarget (v : c.NegativeCoordinates) (hv : v ∈ ball 0 (r / 2)) :
      (v, 0) ∈ c.splitChart.target :=
    hblock ⟨closedBall_subset_closedBall (by linarith : r / 2 ≤ r) (ball_subset_closedBall hv),
      mem_closedBall_self hr.le⟩
  have hlocal : ContMDiffOn 𝓘(ℝ, c.NegativeCoordinates) 𝓘(ℝ, E) ∞
      (fun v => c.splitChart.symm (v, 0)) (ball 0 (r / 2)) :=
    c.splitChart.contMDiffOn_invFun.comp
      (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffOn htarget
  have hpoint (v : c.NegativeCoordinates) (hv : v ∈ ball 0 (r / 2)) :
      Tendsto (fun t => S.flow t (c.splitChart.symm (v, 0))) atBot (𝓝 p.val) := by
    have ht := htarget v hv
    have hs : c.splitChart.symm (v, 0) ∈ c.splitChart.source := c.splitChart.map_target' ht
    have he : c.splitChart (c.splitChart.symm (v, 0)) = (v, 0) := c.splitChart.right_inv' ht
    apply ((hbasin (c.splitChart.symm (v, 0)) hs ?_ ?_).2).mpr
    · rw [he]
    · rw [he]
      exact (mem_ball_zero_iff.mp hv).trans (half_lt_self hr)
    · rw [he]
      simpa using hr
  refine ⟨r / 2, half_pos hr, ?_, ?_⟩
  · intro n
    exact (SmoothODE.nativeFlowTimeDiffeomorph_of_field S.smooth S.flow S.integral
      (n : ℝ)).contMDiff.comp_contMDiffOn hlocal
  · ext x
    constructor
    · intro hx
      have hlim : Tendsto (fun n : ℕ => S.flow (-(n : ℝ)) x) atTop (𝓝 p.val) :=
        hx.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
      obtain ⟨n, hs, hn, hp'⟩ :=
        (hlim.eventually (morse_coordinate_neighborhood c (half_pos hr) (half_pos hr))).exists
      have hnew := (flow_time_atBot_limit_iff S.flow (-(n : ℝ)) x p.val).mpr hx
      have hz : (c.splitChart (S.flow (-(n : ℝ)) x)).2 = 0 :=
        ((hbasin _ hs (hn.trans (half_lt_self hr)) (hp'.trans (half_lt_self hr))).2).mp hnew
      refine mem_iUnion.mpr ⟨n, (c.splitChart (S.flow (-(n : ℝ)) x)).1,
        mem_ball_zero_iff.mpr hn, ?_⟩
      have he : ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0) =
          c.splitChart (S.flow (-(n : ℝ)) x) := Prod.ext rfl hz.symm
      change S.flow (n : ℝ)
        (c.splitChart.symm ((c.splitChart (S.flow (-(n : ℝ)) x)).1, 0)) = x
      rw [he]
      have hi : c.splitChart.symm (c.splitChart (S.flow (-(n : ℝ)) x)) = S.flow (-(n : ℝ)) x :=
        c.splitChart.left_inv' hs
      rw [hi, ← S.flow.map_add, add_neg_cancel, S.flow.map_zero_apply]
    · intro hx
      obtain ⟨n, v, hv, rfl⟩ := mem_iUnion.mp hx
      exact (flow_time_atBot_limit_iff S.flow (n : ℝ) (c.splitChart.symm (v, 0)) p.val).mpr
        (hpoint v hv)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
