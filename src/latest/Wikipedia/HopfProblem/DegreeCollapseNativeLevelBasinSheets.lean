import Wikipedia.HopfProblem.DegreeCollapseNativeLevelVerticalModel
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelTransverseSheets
import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# Actual transverse basin flow tubes from the original regular level

The original complete flow constructs the genuine whole-level cylinder.
Native transverse level maps therefore give smooth transverse flow tubes
in the original manifold, with the corresponding endpoint basin germs.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  {A B HA HB X Y : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace HA] [TopologicalSpace HB]
  {I : ModelWithCorners ℝ A HA} {I' : ModelWithCorners ℝ B HB}
  [TopologicalSpace X] [ChartedSpace HA X] [TopologicalSpace Y] [ChartedSpace HB Y]

theorem native_transverse_basin_tubes_of_level_maps {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c : ℝ}
    (hreg : ∀ z, f z = c → z ∉ ManifoldMorse.criticalPoints E f)
    {V : (z : M) → TangentSpace 𝓘(ℝ, E) z}
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ z, IsMIntegralCurve (fun t => F t z) V)
    (hboundary : ∀ z, f z = c → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) {p q : M} :
    letI := RegularLevel.chartedSpace hf hreg
    ∀ (α : X → {z : M // f z = c}) (β : Y → {z : M // f z = c}) (x : X) (y : Y),
      MDifferentiableAt I 𝓘(ℝ, RegularLevel.Model E) α x →
      MDifferentiableAt I' 𝓘(ℝ, RegularLevel.Model E) β y →
      β y = α x →
      NativeTransversality.At I I' 𝓘(ℝ, RegularLevel.Model E) α β x y →
      (∀ᶠ u in 𝓝 x, Tendsto (fun t => F t (α u)) atBot (𝓝 q)) →
      (∀ᶠ u in 𝓝 y, Tendsto (fun t => F t (β u)) atTop (𝓝 p)) →
      let S : X × ℝ → M := fun w => F w.2 (α w.1)
      let T : Y × ℝ → M := fun w => F w.2 (β w.1)
      MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) S (x, 0) ∧
      MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) T (y, 0) ∧
      S (x, 0) = (α x : M) ∧ T (y, 0) = (α x : M) ∧
      (∀ᶠ u in 𝓝 (x, (0 : ℝ)), Tendsto (fun t => F t (S u)) atBot (𝓝 q)) ∧
      (∀ᶠ u in 𝓝 (y, (0 : ℝ)), Tendsto (fun t => F t (T u)) atTop (𝓝 p)) ∧
      NativeTransversality.At (I.prod 𝓘(ℝ, ℝ)) (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
        S T (x, 0) (y, 0) := by
  let _ := RegularLevel.chartedSpace hf hreg
  let _ := RegularLevel.isManifold hf hreg
  intro α β x y hα hβ hcross htrans hαbasin hβbasin
  obtain ⟨C, hsource, -, hformula, -⟩ :=
    exists_native_level_flow_cylinder_with_field hf hreg hV F hF hboundary (α x)
  have hxC : (α x, (0 : ℝ)) ∈ C.source := by rw [hsource]; exact mem_univ _
  have hyC : (β y, (0 : ℝ)) ∈ C.source := by rw [hsource]; exact mem_univ _
  have hS : MDifferentiableAt (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (fun w : X × ℝ => C (α w.1, w.2)) (x, 0) :=
    (C.mdifferentiableAt (by simp) hxC).comp (x, 0)
      ((hα.comp (x, 0) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have hT : MDifferentiableAt (I'.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
      (fun w : Y × ℝ => C (β w.1, w.2)) (y, 0) :=
    (C.mdifferentiableAt (by simp) hyC).comp (y, 0)
      ((hβ.comp (y, 0) mdifferentiableAt_fst).prodMk mdifferentiableAt_snd)
  have ht := TransverseGerms.native_transverse_sheets_of_level_maps C hα hβ
    (v := fun _ : X => (0 : ℝ)) (w := fun _ : Y => (0 : ℝ))
    mdifferentiableAt_const mdifferentiableAt_const hcross htrans
    (s := 0) (t := 0) rfl (by simpa only [add_zero] using hxC)
  refine ⟨?_, ?_, F.map_zero_apply _, ?_, ?_, ?_, ?_⟩
  · simpa only [hformula] using hS
  · simpa only [hformula] using hT
  · change F 0 (β y) = (α x : M)
    rw [F.map_zero_apply, hcross]
  · filter_upwards [continuous_fst.continuousAt hαbasin] with u hu
    exact (MorseCancellation.flow_time_atBot_limit_iff F u.2 (α u.1) q).mpr hu
  · filter_upwards [continuous_fst.continuousAt hβbasin] with u hu
    exact (MorseCancellation.flow_time_atTop_limit_iff F u.2 (β u.1) p).mpr hu
  · simpa only [add_zero, hformula] using ht

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
