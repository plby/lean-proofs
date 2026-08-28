import Wikipedia.HopfProblem.DegreeCollapseNativeBeltArc

/-!
# An entire native belt meridian passes to the original attaching class

Fix a positive-core direction and vary the negative unit direction. The
resulting upper-level sphere passes, at one common explicit time, to a
lower-level sphere. Shrinking its positive coordinate gives an actual
homotopy in the original lower level to the original attaching sphere.
This retains the whole parametrization needed for a middle handle slide.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

theorem nativeLowerMeridian_coordinates_mem_target
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    BeltPassage.lower (S.data q).radius s u.val v.val ∈ (S.data q).chart.splitChart.target := by
  have hh := BeltPassage.upper_mem_block (S.data q).radius_pos
    (show |(s : ℝ)| ≤ 1 by rw [abs_of_nonneg s.property.1]; exact s.property.2)
    (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  exact (S.data q).block ⟨hh.2, hh.1⟩

theorem nativeLowerMeridian_height
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    f ((S.data q).chart.splitChart.symm (BeltPassage.lower (S.data q).radius s u.val v.val)) =
      S.toSurgeryWindows.lower q := by
  rw [(S.data q).chart.splitChart_inverse_equation
    (nativeLowerMeridian_coordinates_mem_target S q u v s)]
  have hh := BeltPassage.upper_height (S.data q).radius (s : ℝ)
    (mem_sphere_zero_iff_norm.mp v.property) (mem_sphere_zero_iff_norm.mp u.property)
  change -‖(BeltPassage.lower (S.data q).radius s u.val v.val).2‖ ^ 2 +
    ‖(BeltPassage.lower (S.data q).radius s u.val v.val).1‖ ^ 2 = (S.data q).radius ^ 2 at hh
  dsimp only [SurgeryWindows.lower]
  linarith

def nativeLowerMeridianFamily (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    C(unitInterval × sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      (S.data q).LowerLevel) where
  toFun z := ⟨(S.data q).chart.splitChart.symm
    (BeltPassage.lower (S.data q).radius z.1 z.2.val v.val),
    nativeLowerMeridian_height S q z.2 v z.1⟩
  continuous_toFun := by
    have hsize : Continuous (fun z : unitInterval ×
        sphere (0 : (S.data q).chart.NegativeCoordinates) 1 => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hdir : Continuous (fun z : unitInterval ×
        sphere (0 : (S.data q).chart.NegativeCoordinates) 1 => z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    have hcoords : Continuous (fun z : unitInterval ×
        sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
        BeltPassage.lower (S.data q).radius (z.1 : ℝ) z.2.val v.val) := by
      unfold BeltPassage.lower
      exact ((continuous_const.mul
        (Real.continuous_sqrt.comp (continuous_const.add (hsize.pow 2)))).smul hdir).prodMk
          ((continuous_const.mul hsize).smul continuous_const)
    exact ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous
      hcoords (fun z => nativeLowerMeridian_coordinates_mem_target S q z.2 v z.1)).subtype_mk _

def nativeLowerMeridian (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).LowerLevel) :=
  (nativeLowerMeridianFamily S q v).comp
    ((ContinuousMap.const _ s).prodMk (ContinuousMap.id _))

def nativeUpperMeridian (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    C(sphere (0 : (S.data q).chart.NegativeCoordinates) 1, (S.data q).UpperLevel) where
  toFun u := ⟨nativeBeltArc S q u v s, nativeBeltArc_height S q u v
    (by rw [abs_of_nonneg s.property.1]; exact s.property.2)⟩
  continuous_toFun := by
    have hcoords : Continuous (fun u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
        BeltPassage.upper (S.data q).radius (s : ℝ) u.val v.val) := by
      unfold BeltPassage.upper
      have hneg : Continuous (fun u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          ((S.data q).radius * (s : ℝ)) • u.val) :=
        (continuous_subtype_val : Continuous (fun u :
          sphere (0 : (S.data q).chart.NegativeCoordinates) 1 => u.val)).const_smul
            ((S.data q).radius * (s : ℝ))
      have hpos : Continuous (fun _ : sphere (0 : (S.data q).chart.NegativeCoordinates) 1 =>
          ((S.data q).radius * Real.sqrt (1 + (s : ℝ) ^ 2)) • v.val) := continuous_const
      exact hneg.prodMk hpos
    exact ((S.data q).chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous
      hcoords (fun u => nativeBeltArc_coordinates_mem_target S q u v
        (by rw [abs_of_nonneg s.property.1]; exact s.property.2))).subtype_mk _

theorem nativeLowerMeridian_zero (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) :
    nativeLowerMeridian S q v 0 = (S.data q).surgery.attachingSphere := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  change (S.data q).chart.splitChart.symm
    (BeltPassage.lower (S.data q).radius 0 u.val v.val) = _
  rw [BeltPassage.lower_zero, (S.data q).attaching_eq, (S.data q).chart.attachingCoreMap_coe]

theorem nativeUpperMeridian_flow (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval)
    (hs : 0 < (s : ℝ)) (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    S.flow (BeltPassage.time s) ((nativeUpperMeridian S q v s) u).val =
      ((nativeLowerMeridian S q v s) u).val :=
  S.flow_belt_passage q hs s.property.2 u v

theorem nativeLowerMeridian_homotopic_attaching
    (S : AdaptedSurgeryWindows E f) (q : criticalPoints E f)
    (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1) (s : unitInterval) :
    (nativeLowerMeridian S q v s).Homotopic (S.data q).surgery.attachingSphere := by
  let shrink : C(unitInterval, unitInterval) :=
    ⟨fun t => unitInterval.symm t * s, unitInterval.continuous_symm.mul continuous_const⟩
  have h0 : shrink 0 = s := by simp [shrink]
  have h1 : shrink 1 = 0 := by simp [shrink]
  let H : (nativeLowerMeridian S q v s).Homotopy (S.data q).surgery.attachingSphere := {
    toFun := fun z => nativeLowerMeridianFamily S q v (shrink z.1, z.2)
    continuous_toFun := (nativeLowerMeridianFamily S q v).continuous.comp
      ((shrink.continuous.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := by
      intro u
      rw [h0]
      rfl
    map_one_left := by
      intro u
      rw [h1]
      exact congrArg (fun g : C(sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
        (S.data q).LowerLevel) => g u) (nativeLowerMeridian_zero S q v) }
  exact ⟨H⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
