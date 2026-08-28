import Wikipedia.SmoothSixDPoincare.MorseFaceAttachment

/-!
# The native handle-face subtype and its original sphere-times-disk coordinates

Both descriptions retain the same whole-handle point. The native lower
sublevel face map is the actual attaching-face map in these coordinates.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
def handleFaceCoordinates : d.handleFace ≃ₜ
    PuncturedHandle.UnitSphere d.chart.NegativeCoordinates ×
      MorseHandle.UnitDisk d.chart.PositiveCoordinates where
  toFun z := (⟨z.val.1.val, mem_sphere_zero_iff_norm.mpr z.property⟩, z.val.2)
  invFun z := ⟨d.handleFacePoint z.1 z.2, mem_sphere_zero_iff_norm.mp z.1.property⟩
  left_inv _z := Subtype.ext (Prod.ext (Subtype.ext rfl) rfl)
  right_inv _z := Prod.ext (Subtype.ext rfl) rfl
  continuous_toFun :=
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk
      continuous_snd).subtype_mk _

open Classical in
theorem handleFaceCoordinates_symm_val
    (z : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates ×
      MorseHandle.UnitDisk d.chart.PositiveCoordinates) :
    (d.handleFaceCoordinates.symm z).val = d.handleFacePoint z.1 z.2 := rfl

open Classical in
theorem handleFaceCoordinates_map (z : d.handleFace) :
    d.handleMap z.val = (d.attachingFace (d.handleFaceCoordinates z)).val := rfl

open Classical in
theorem handleFaceToSublevel_coordinates (z : d.handleFace) :
    d.handleFaceToSublevel z =
      ⟨(d.attachingFace (d.handleFaceCoordinates z)).val,
        (d.attachingFace (d.handleFaceCoordinates z)).property.le⟩ := rfl

open Classical in
theorem attachingFace_oldPiece
    (z : PuncturedHandle.UnitSphere d.chart.NegativeCoordinates ×
      MorseHandle.UnitDisk d.chart.PositiveCoordinates) :
    d.attachingFace z = d.surgery.oldPiece
      (z.1, ⟨z.2.val, mem_closedBall_zero_iff.mp z.2.property⟩) := by
  apply Subtype.ext
  rw [d.oldPiece_eq]
  rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
