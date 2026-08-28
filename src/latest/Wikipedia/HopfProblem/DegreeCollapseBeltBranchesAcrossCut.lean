import Wikipedia.HopfProblem.DegreeCollapseCrossingBasinPaths
import Wikipedia.HopfProblem.DegreeCollapseBeltArcReachingPath

/-!
# Both sides of the actual belt arc cross the original lower boundary

The native upper-to-lower passage and openness of the lower-level crossing
basin put each short nonzero side of the belt arc in that basin. A common
minimum endpoint is not required. The return path is constructed in the
actual upper surgery level and retains crossing of both original cuts.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_positive_belt_branch_crossing_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranch : ((S.data q).surgery.attachingSphere u).val ∈
      FlowCancellation.levelBasin S.flow f c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ s : ℝ, 0 < s → s < ε →
      (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius s u.val v.val) ∈
        FlowCancellation.levelBasin S.flow f c := by
  let d := S.data q
  have h0target : BeltPassage.lower d.radius 0 u.val v.val ∈ d.chart.splitChart.target := by
    rw [BeltPassage.lower_zero]
    apply d.block
    constructor
    · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos d.radius_pos,
        mem_sphere_zero_iff_norm.mp u.property, mul_one]
      linarith [d.radius_pos]
    · exact mem_closedBall_self (by linarith [d.radius_pos])
  have h0value : d.chart.splitChart.symm (BeltPassage.lower d.radius 0 u.val v.val) =
      (d.surgery.attachingSphere u).val := by
    rw [BeltPassage.lower_zero, d.attaching_eq, d.chart.attachingCoreMap_coe]
  have hcont : ContinuousAt (fun s : ℝ => d.chart.splitChart.symm
      (BeltPassage.lower d.radius s u.val v.val)) 0 :=
    (d.chart.splitChart.contMDiffOn_invFun.continuousOn.continuousAt
      (d.chart.splitChart.open_target.mem_nhds h0target)).comp
        (f := fun s : ℝ => BeltPassage.lower d.radius s u.val v.val)
        (BeltPassage.contDiff_lower d.radius u.val v.val).continuous.continuousAt
  have hB : IsOpen (FlowCancellation.levelBasin S.flow f c) :=
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (hc z hz))).1
  have hbasin : d.chart.splitChart.symm (BeltPassage.lower d.radius 0 u.val v.val) ∈
      FlowCancellation.levelBasin S.flow f c := h0value.symm ▸ hbranch
  have hnear := hcont.tendsto.eventually (hB.mem_nhds hbasin)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro s hs hsε
  have hs₁ : s ≤ 1 := (hsε.trans_le (min_le_right _ _)).le
  have hlow : d.chart.splitChart.symm (BeltPassage.lower d.radius s u.val v.val) ∈
      FlowCancellation.levelBasin S.flow f c := by
    apply hδsub
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs]
    exact hsε.trans_le (min_le_left _ _)
  have hflow := S.flow_belt_passage q hs hs₁ u v
  exact (FlowCancellation.levelBasin_flow_iff S.flow f c (BeltPassage.time s) _).mp
    (hflow.symm ▸ hlow)

theorem AdaptedSurgeryWindows.exists_two_sided_belt_branch_crossing_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) {c : ℝ}
    (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      ((S.data q).surgery.attachingSphere w).val ∈ FlowCancellation.levelBasin S.flow f c) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ s : ℝ, 0 < |s| → |s| < ε →
      (S.data q).chart.splitChart.symm (BeltPassage.upper (S.data q).radius s u.val v.val) ∈
        FlowCancellation.levelBasin S.flow f c := by
  let u' : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 :=
    ⟨-u.val, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp u.property)⟩
  obtain ⟨εp, hεp, hεp1, hplus⟩ :=
    S.exists_positive_belt_branch_crossing_level hf q hc u v (hbranches u)
  obtain ⟨εn, hεn, _, hminus⟩ :=
    S.exists_positive_belt_branch_crossing_level hf q hc u' v (hbranches u')
  refine ⟨min εp εn, lt_min hεp hεn, (min_le_left _ _).trans hεp1, ?_⟩
  intro s hs hsmall
  by_cases hpos : 0 < s
  · apply hplus s hpos
    rw [abs_of_pos hpos] at hsmall
    exact hsmall.trans_le (min_le_left _ _)
  · have hneg : s < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (abs_pos.mp hs)
    have heq : BeltPassage.upper (S.data q).radius s u.val v.val =
        BeltPassage.upper (S.data q).radius (-s) u'.val v.val := by
      simpa only [neg_neg] using BeltPassage.upper_neg (S.data q).radius (-s) u.val v.val
    rw [heq]
    apply hminus (-s) (neg_pos.mpr hneg)
    rw [abs_of_neg hneg] at hsmall
    exact hsmall.trans_le (min_le_right _ _)

theorem AdaptedSurgeryWindows.exists_belt_arc_closing_path_between_cuts
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) {c a : ℝ} (hcq : c < f q)
    (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    [PathConnectedSpace {y : M // f y = c}]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      ((S.data q).surgery.attachingSphere w).val ∈ FlowCancellation.levelBasin S.flow f c)
    (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hv : ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a)
    {d : ℕ} (hlow : ∀ z : criticalPoints E f, c < f z → f z ≤ a → nativeMorseIndex E f z ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ s : ℝ, |s| ≤ r → nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f a) ∧
      (∀ s : ℝ, 0 < |s| → |s| ≤ r →
        nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f c) ∧
      JoinedIn {z : M | f z = S.toSurgeryWindows.upper q ∧
        z ∈ FlowCancellation.levelBasin S.flow f c ∧ z ∈ FlowCancellation.levelBasin S.flow f a}
        (nativeBeltArc S q u v r) (nativeBeltArc S q u v (-r)) := by
  obtain ⟨ε, hε, hε1, hlower⟩ :=
    S.exists_two_sided_belt_branch_crossing_level hf q hc u v hbranches
  have hB : IsOpen (FlowCancellation.levelBasin S.flow f a) :=
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (ha z hz))).1
  have hα0 : nativeBeltArc S q u v 0 ∈ FlowCancellation.levelBasin S.flow f a := by
    rw [nativeBeltArc_zero]
    exact hv
  have hcont : ContinuousAt (nativeBeltArc S q u v) 0 :=
    ((nativeBeltArc_contMDiffOn S q u v).contMDiffAt
      (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))).continuousAt
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), nativeBeltArc S q u v s ∈
      FlowCancellation.levelBasin S.flow f a := hcont.preimage_mem_nhds (hB.mem_nhds hα0)
  obtain ⟨δ, hδ, hball⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  let r := min (ε / 2) (δ / 2)
  have hr : 0 < r := lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hr1 : r < 1 := hrε.trans_le hε1
  have hreach (s : ℝ) (hs : |s| ≤ r) :
      nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f a := by
    apply hball
    rw [mem_ball, Real.dist_eq, sub_zero]
    exact hs.trans_lt hrδ
  have hall (s : ℝ) (hs : 0 < |s|) (hsr : |s| ≤ r) :
      nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f c :=
    hlower s hs (hsr.trans_lt hrε)
  have hpr : |r| = r := abs_of_pos hr
  have hmr : |-r| = r := by rw [abs_neg, hpr]
  refine ⟨r, hr, hr1, hreach, hall, ?_⟩
  exact S.joinedIn_level_crossing_both_cuts hf
    (hcq.trans (S.toSurgeryWindows.value_lt_upper q)) hba hc (S.data q).upper_regular ha
    hlow hdim
    (nativeBeltArc_height S q u v (by rw [hpr]; exact hr1.le))
    (nativeBeltArc_height S q u v (by rw [hmr]; exact hr1.le))
    (hall r (hpr.symm ▸ hr) hpr.le) (hall (-r) (hmr.symm ▸ hr) hmr.le)
    (hreach r hpr.le) (hreach (-r) hmr.le)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
