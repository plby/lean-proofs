import Wikipedia.HopfProblem.DegreeCollapseTimeCollar

/-!
# The original zero fiber of a time collar is its specified boundary

Restrict the actual collar coordinates to time zero. Both inverse maps
are explicit restrictions of the original collar and retain ambient points.
-/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

def zeroHomeomorph : {x : M // t x = 0} ≃ₜ B := by
  let zeroTime : Ioo (-C.width) C.width :=
    ⟨0, neg_lt_zero.mpr C.width_pos, C.width_pos⟩
  let intoBand : C({x : M // t x = 0}, TimeBand t C.width) :=
    ⟨fun x => ⟨x.val, by rw [x.property]; exact zeroTime.property⟩,
      (continuous_subtype_val : Continuous (fun x : {y : M // t y = 0} => x.val)).subtype_mk
        (fun x => by rw [x.property]; exact zeroTime.property)⟩
  let fromB : C(B, {x : M // t x = 0}) :=
    ⟨fun b => ⟨(C.zeroPoint b).val, C.zeroPoint_time b⟩,
      (continuous_subtype_val.comp (C.coordinates.symm.continuous.comp
        (continuous_const.prodMk continuous_id))).subtype_mk _⟩
  refine {
    toFun := fun x => (C.coordinates (intoBand x)).2
    invFun := fromB
    continuous_toFun := continuous_snd.comp (C.coordinates.continuous.comp intoBand.continuous)
    continuous_invFun := fromB.continuous
    left_inv := ?_
    right_inv := ?_ }
  · intro x
    apply Subtype.ext
    have hpair : (zeroTime, (C.coordinates (intoBand x)).2) = C.coordinates (intoBand x) := by
      apply Prod.ext
      · exact Subtype.ext ((C.coordinate_time (intoBand x)).trans x.property).symm
      · rfl
    change (C.coordinates.symm (zeroTime, (C.coordinates (intoBand x)).2)).val = x.val
    rw [hpair, C.coordinates.symm_apply_apply]
    rfl
  · intro b
    change (C.coordinates (intoBand (fromB b))).2 = b
    have hband : intoBand (fromB b) = C.zeroPoint b := Subtype.ext rfl
    rw [hband]
    change (C.coordinates (C.coordinates.symm (zeroTime, b))).2 = b
    rw [C.coordinates.apply_symm_apply]

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
