import Wikipedia.HopfProblem.DegreeCollapseBeltMeridianDisk

/-!
# The whole native meridian disk fits inside any belt-point neighborhood

Choose an actual positive radius for the bounded radial disk. Uniform
boundedness of its unit-ball coordinate keeps its entire Euclidean image
inside the prescribed original open neighborhood of the belt point.
-/

noncomputable section

open Set Function Metric Manifold Filter
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open DiskShrinking

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

theorem exists_native_meridian_disk_in_open
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    {O : Set M} (hO : IsOpen O) (hv : ((S.data q).surgery.beltSphere v).val ∈ O) :
    ∃ s : unitInterval, ∃ hs : (s : ℝ) ≤ 1 / 2, 0 < (s : ℝ) ∧
      ∀ x, (nativeBeltMeridianDisk S q v s hs x).val ∈ O := by
  let N := (S.data q).chart.NegativeCoordinates
  let P := (S.data q).chart.PositiveCoordinates
  let a : N → N × P := fun y =>
    ((S.data q).radius • y,
      ((S.data q).radius * Real.sqrt (1 + ‖y‖ ^ 2)) • v.val)
  have ha : ContDiff ℝ ∞ a :=
    (contDiff_id.const_smul (S.data q).radius).prodMk
      ((contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt
        (fun _ => by positivity))).smul contDiff_const)
  let h : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hh : (h : ℝ) ≤ 1 / 2 := le_rfl
  have htarget : a 0 ∈ (S.data q).chart.splitChart.target := by
    simpa only [a, nativeBeltDiskCoordinates, boundedRadialDiskMap_zero] using
      nativeBeltDiskCoordinates_mem_target S q v h hh 0
  let F : N → M := fun y => (S.data q).chart.splitChart.symm (a y)
  have hF : ContinuousAt F 0 :=
    ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.continuousAt
      ((S.data q).chart.splitChart.open_target.mem_nhds htarget)).comp ha.continuous.continuousAt
  have hF0 : F 0 = ((S.data q).surgery.beltSphere v).val := by
    have he : F 0 = (nativeBeltMeridianDisk S q v h hh 0).val := by
      simp only [F, a, nativeBeltMeridianDisk, nativeBeltDiskCoordinates,
        boundedRadialDiskMap_zero]
    exact he.trans (congrArg Subtype.val (nativeBeltMeridianDisk_zero S q v h hh))
  have hnear : F ⁻¹' O ∈ 𝓝 (0 : N) :=
    hF.preimage_mem_nhds (hO.mem_nhds (hF0.symm ▸ hv))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let σ : ℝ := min (δ / 4) (1 / 4)
  have hσ : 0 < σ := lt_min (by positivity) (by norm_num)
  have hσhalf : σ ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  let s : unitInterval := ⟨σ, hσ.le, hσhalf.trans (by norm_num)⟩
  refine ⟨s, hσhalf, hσ, ?_⟩
  intro x
  change F (boundedRadialDiskMap σ x) ∈ O
  apply hball
  rw [mem_ball_zero_iff, boundedRadialDiskMap, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) hσ.le)]
  have hn : ‖(OpenPartialHomeomorph.univUnitBall : N → N) x‖ < 1 :=
    mem_ball_zero_iff.mp (OpenPartialHomeomorph.univUnitBall.map_source (mem_univ x))
  have hroot : Real.sqrt (2 : ℝ) ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  calc
    (Real.sqrt 2 * σ) * ‖(OpenPartialHomeomorph.univUnitBall : N → N) x‖
        ≤ Real.sqrt 2 * σ := mul_le_of_le_one_right (by positivity) hn.le
    _ ≤ 2 * σ := mul_le_mul_of_nonneg_right hroot hσ.le
    _ ≤ δ / 2 := by dsimp only [σ]; linarith [min_le_left (δ / 4) (1 / 4 : ℝ)]
    _ < δ := half_lt_self hδ

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
