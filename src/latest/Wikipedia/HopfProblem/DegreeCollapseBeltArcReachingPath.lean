import Wikipedia.HopfProblem.DegreeCollapseBeltPointUpperCrossing
import Wikipedia.HopfProblem.DegreeCollapseMinimumLevelPathsReaching

/-!
# Both pieces of the belt loop can be chosen to reach a higher level

Openness of the actual higher-level crossing basin controls a whole small
closed belt arc. The return path stays both in the minimum basin and in
that crossing basin. These are actual orbit conditions for the given flow.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_belt_arc_closing_path_reaching_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {a : ℝ} (hba : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hv : ((S.data q).surgery.beltSphere v).val ∈ FlowCancellation.levelBasin S.flow f a)
    {d : ℕ} (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (∀ s : ℝ, |s| ≤ r → nativeBeltArc S q u v s ∈ FlowCancellation.levelBasin S.flow f a) ∧
      (∀ s : ℝ, 0 < |s| → |s| ≤ r →
        Tendsto (fun t => S.flow t (nativeBeltArc S q u v s)) atTop (𝓝 p.val)) ∧
      JoinedIn {z : M | f z = S.toSurgeryWindows.upper q ∧
        Tendsto (fun t => S.flow t z) atTop (𝓝 p.val) ∧
        z ∈ FlowCancellation.levelBasin S.flow f a}
        (nativeBeltArc S q u v r) (nativeBeltArc S q u v (-r)) := by
  obtain ⟨ε, hε, hε1, hmin⟩ :=
    S.exists_two_sided_belt_branch_in_minimum_basin hf p q hp u v hbranches
  have hB : IsOpen (FlowCancellation.levelBasin S.flow f a) :=
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (ha z hz))).1
  have hα0 : nativeBeltArc S q u v 0 ∈ FlowCancellation.levelBasin S.flow f a := by
    rw [nativeBeltArc_zero]
    exact hv
  have hc : ContinuousAt (nativeBeltArc S q u v) 0 :=
    ((nativeBeltArc_contMDiffOn S q u v).contMDiffAt
      (Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) (show (0 : ℝ) < 1 by norm_num))).continuousAt
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), nativeBeltArc S q u v s ∈
      FlowCancellation.levelBasin S.flow f a := hc.preimage_mem_nhds (hB.mem_nhds hα0)
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
      Tendsto (fun t => S.flow t (nativeBeltArc S q u v s)) atTop (𝓝 p.val) :=
    hmin s hs (hsr.trans_lt hrε)
  have hpb : f p < S.toSurgeryWindows.upper q :=
    (S.forward_limit_below_regular_level hf (S.data q).lower_regular
      ((S.data q).surgery.attachingSphere u) (hbranches u)).trans
        ((S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q))
  have hpr : |r| = r := abs_of_pos hr
  have hmr : |-r| = r := by rw [abs_neg, hpr]
  refine ⟨r, hr, hr1, hreach, hall, ?_⟩
  exact S.joinedIn_level_minimum_basin_reaching_level hf p hp hpb hba ha
    (S.data q).upper_regular hlow hdim
    (nativeBeltArc_height S q u v (by rw [hpr]; exact hr1.le))
    (nativeBeltArc_height S q u v (by rw [hmr]; exact hr1.le))
    (hall r (hpr.symm ▸ hr) hpr.le) (hall (-r) (hmr.symm ▸ hr) hmr.le)
    (hreach r hpr.le) (hreach (-r) hmr.le)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
