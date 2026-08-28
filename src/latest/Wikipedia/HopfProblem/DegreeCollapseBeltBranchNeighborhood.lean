import Wikipedia.HopfProblem.DegreeCollapseNativeBeltPassage
import Wikipedia.HopfProblem.DegreeCollapseDenseMinimumBasins

/-!
# Both nearby sides of the actual belt lie in the minimum basin

The exact lower passage point converges to the original attaching core.
Openness of the minimum basin and actual native passage therefore put all
sufficiently small positive normal points in that basin. If both attaching
directions reach the same minimum, the conclusion holds on both sides of
the belt, with one common positive radius.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_positive_belt_branch_in_minimum_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranch : Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val)
      atTop (𝓝 p.val)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ s : ℝ, 0 < s → s < ε →
      Tendsto (fun t => S.flow t ((S.data q).chart.splitChart.symm
        (BeltPassage.upper (S.data q).radius s u.val v.val))) atTop (𝓝 p.val) := by
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
  have hc : ContinuousAt (fun s : ℝ => d.chart.splitChart.symm
      (BeltPassage.lower d.radius s u.val v.val)) 0 :=
    (d.chart.splitChart.contMDiffOn_invFun.continuousOn.continuousAt
      (d.chart.splitChart.open_target.mem_nhds h0target)).comp
        (f := fun s : ℝ => BeltPassage.lower d.radius s u.val v.val)
        (BeltPassage.contDiff_lower d.radius u.val v.val).continuous.continuousAt
  have hbasin : d.chart.splitChart.symm (BeltPassage.lower d.radius 0 u.val v.val) ∈
      {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} := by
    rw [h0value]
    exact hbranch
  have hnear := hc.tendsto.eventually ((S.isOpen_minimum_forward_basin hf p hp).mem_nhds hbasin)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min δ 1, lt_min hδ zero_lt_one, min_le_right _ _, ?_⟩
  intro s hs hsε
  have hs₁ : s ≤ 1 := (hsε.trans_le (min_le_right _ _)).le
  apply (S.belt_passage_forward_limit_iff q hs hs₁ u v p.val).mpr
  apply hδsub
  rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs]
  exact hsε.trans_le (min_le_left _ _)

open Classical in
theorem AdaptedSurgeryWindows.exists_two_sided_belt_branch_in_minimum_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ s : ℝ, 0 < |s| → |s| < ε →
      Tendsto (fun t => S.flow t ((S.data q).chart.splitChart.symm
        (BeltPassage.upper (S.data q).radius s u.val v.val))) atTop (𝓝 p.val) := by
  let u' : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 :=
    ⟨-u.val, mem_sphere_zero_iff_norm.mpr (by
      rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp u.property)⟩
  obtain ⟨εp, hεp, hεp1, hplus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u v (hbranches u)
  obtain ⟨εn, hεn, -, hminus⟩ :=
    S.exists_positive_belt_branch_in_minimum_basin hf p q hp u' v (hbranches u')
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

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
