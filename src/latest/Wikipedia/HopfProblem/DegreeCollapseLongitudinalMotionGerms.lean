import Wikipedia.HopfProblem.DegreeCollapseLongitudinalTubeMotion

/-!
# Exact axis and germ formulas for the constructed tube motion

The longitudinal profile is a translation near zero, and the transverse
cutoff is one there. Consequently the joint model germ is a translation
whose time velocity is strictly positive at the constructed crossing time.
The ambient family fixes everything outside the actual tube target.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞}

theorem LongitudinalTubeMotion.model_axis (A : LongitudinalTubeMotion Φ) (t : ℝ) :
    longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, (0, 0)) =
      (Real.smoothTransition t * A.destination, 0) := by
  simp only [longitudinalBlend, longitudinalBlendDisplacement, A.cutoff_zero,
    A.profile_zero, mul_one, sub_zero, zero_add]

theorem LongitudinalTubeMotion.model_germ (A : LongitudinalTubeMotion Φ) (t : ℝ) :
    longitudinalBlend A.profile A.cutoff Real.smoothTransition =ᶠ[𝓝 (t, (0, 0))]
      fun p : ℝ × (ℝ × V) =>
        (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : Tendsto (fun p : ℝ × (ℝ × V) => p.2.1)
      (𝓝 (t, (0, 0))) (𝓝 0) := continuous_fst.continuousAt.comp continuous_snd.continuousAt
  have hz : Tendsto (fun p : ℝ × (ℝ × V) => p.2.2)
      (𝓝 (t, (0, 0))) (𝓝 0) := continuous_snd.continuousAt.comp continuous_snd.continuousAt
  filter_upwards [hs.eventually A.profile_germ, hz.eventually A.cutoff_germ] with p hp hβ
  simp only [longitudinalBlend, longitudinalBlendDisplacement, hp, hβ, mul_one,
    add_sub_cancel_left]

theorem LongitudinalTubeMotion.native_axis (A : LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    A.family (t, Φ 0) = Φ (Real.smoothTransition t * A.destination, 0) := by
  rw [A.formula t 0 h0]
  exact congrArg Φ (A.model_axis t)

theorem LongitudinalTubeMotion.native_germ (A : LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) (t : ℝ) :
    (fun p : ℝ × (ℝ × V) => A.family (p.1, Φ p.2)) =ᶠ[𝓝 (t, 0)]
      fun p => Φ (p.2.1 + Real.smoothTransition p.1 * A.destination, p.2.2) := by
  have hs : ∀ᶠ p : ℝ × (ℝ × V) in 𝓝 (t, 0), p.2 ∈ Φ.source :=
    continuous_snd.continuousAt.eventually (Φ.open_source.mem_nhds h0)
  filter_upwards [A.model_germ t, hs] with p hp hs
  rw [A.formula p.1 p.2 hs, hp]

theorem LongitudinalTubeMotion.fixed_outside_target (A : LongitudinalTubeMotion Φ)
    (t : ℝ) (y : M) (hy : y ∉ Φ.target) : A.family (t, y) = y :=
  A.fixedOutside t y (fun h => hy (A.support_subset h))

theorem LongitudinalTubeMotion.maps_target (A : LongitudinalTubeMotion Φ)
    (t : ℝ) : MapsTo (fun y => A.family (t, y)) Φ.target Φ.target := by
  intro y hy
  change A.family (t, y) ∈ Φ.target
  have heq : A.family (t, y) =
      Φ (longitudinalBlend A.profile A.cutoff Real.smoothTransition (t, Φ.symm y)) :=
    (congrArg (fun z => A.family (t, z)) (Φ.right_inv hy)).symm.trans
      (A.formula t (Φ.symm y) (Φ.map_target hy))
  rw [heq]
  exact Φ.map_source (A.model_source t (Φ.symm y) (Φ.map_target hy))

theorem LongitudinalTubeMotion.crossing_axis (A : LongitudinalTubeMotion Φ)
    (h0 : (0 : ℝ × V) ∈ Φ.source) : A.family (A.time, Φ 0) = Φ (1, 0) := by
  rw [A.native_axis h0, A.time_value]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
