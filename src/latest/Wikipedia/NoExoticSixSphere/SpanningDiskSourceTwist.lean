import Wikipedia.NoExoticSixSphere.SpanningDiskFrameFactorization

/-!
# A common source-framing change transports actual operator homotopies

The source twist need not extend over the disk and is not claimed to preserve
the numerical parity of a single sphere. It does transport a homotopy between
two original sphere-operator maps to a homotopy between their twisted blocks.
-/

noncomputable section

namespace NoExoticSixSphere.SpanningDiskFrameCoordinates

open GLOrthonormalization Stiefel

variable {N k : ℕ}

def twistedBlockMap (F : C(Sphere 3, Monomorphism.Space N (k + 3))) :
    C(Sphere 3, Monomorphism.Space (N + 6) ((k + 5) + 4)) where
  toFun s := Monomorphism.recoordinate (targetCoordinates N) (sourceTwist k s)
    (Monomorphism.blockMap 6 (F s))
  continuous_toFun := (continuous_const.clm_comp
    ((continuous_subtype_val.comp ((Monomorphism.blockMap 6).continuous.comp F.continuous)).clm_comp
      (continuous_sourceTwist k))).subtype_mk _

theorem twistedBlockMap_value (F : C(Sphere 3, Monomorphism.Space N (k + 3))) (s : Sphere 3) :
    (twistedBlockMap F s).val = (targetCoordinates N).toContinuousLinearMap.comp
      ((BlockSum.operator 6 (F s).val).comp (sourceTwist k s).toContinuousLinearMap) := rfl

theorem twistedBlockMap_homotopic {F G : C(Sphere 3, Monomorphism.Space N (k + 3))}
    (h : F.Homotopic G) : (twistedBlockMap F).Homotopic (twistedBlockMap G) := by
  obtain ⟨H⟩ := h
  refine ⟨{
    toFun := fun p ↦ Monomorphism.recoordinate (targetCoordinates N) (sourceTwist k p.2)
      (Monomorphism.blockMap 6 (H p))
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · exact (continuous_const.clm_comp
      ((continuous_subtype_val.comp
        ((Monomorphism.blockMap 6).continuous.comp H.continuous)).clm_comp
          ((continuous_sourceTwist k).comp continuous_snd))).subtype_mk _
  · intro s
    rw [H.apply_zero]
    rfl
  · intro s
    rw [H.apply_one]
    rfl

end NoExoticSixSphere.SpanningDiskFrameCoordinates
