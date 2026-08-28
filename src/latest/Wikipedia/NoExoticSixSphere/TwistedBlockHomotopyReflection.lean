import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockHomotopy
import Wikipedia.NoExoticSixSphere.SpanningDiskSourceTwist

/-!
# The common source twist reflects sphere homotopies

The inverse source twist is used pointwise on the sphere throughout the
given homotopy. No extension of that twist over a disk is assumed. After
undoing the genuine coordinate changes, block-stabilization reflection
recovers a homotopy of the original injective-operator maps.
-/

noncomputable section

namespace NoExoticSixSphere.SpanningDiskFrameCoordinates

open GLOrthonormalization Stiefel

theorem continuous_sourceTwist_symm (k : ℕ) :
    Continuous (fun s ↦ (sourceTwist k s).symm.toContinuousLinearMap) := by
  change Continuous (fun s ↦ (sourceSphere k s).toContinuousLinearMap.comp
    (sourceShuffle k).symm.toContinuousLinearMap)
  exact (continuous_sourceSphere k).clm_comp continuous_const

theorem twistedBlockMap_homotopic_iff {N k : ℕ} (hN : N = k + 6)
    (F G : C(Sphere 3, Monomorphism.Space N (k + 3))) :
    (twistedBlockMap F).Homotopic (twistedBlockMap G) ↔ F.Homotopic G := by
  constructor
  · rintro ⟨H⟩
    have K : ((Monomorphism.blockMap 6).comp F).Homotopic
        ((Monomorphism.blockMap 6).comp G) := by
      refine ⟨{
        toFun q := Monomorphism.recoordinate (targetCoordinates N).symm
          (sourceTwist k q.2).symm (H q)
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_
      }⟩
      · exact (continuous_const.clm_comp
          ((continuous_subtype_val.comp H.continuous).clm_comp
            ((continuous_sourceTwist_symm k).comp continuous_snd))).subtype_mk _
      · intro s
        rw [H.apply_zero]
        exact (Monomorphism.recoordinateHomeomorph
          (targetCoordinates N) (sourceTwist k s)).symm_apply_apply (Monomorphism.blockMap 6 (F s))
      · intro s
        rw [H.apply_one]
        exact (Monomorphism.recoordinateHomeomorph
          (targetCoordinates N) (sourceTwist k s)).symm_apply_apply (Monomorphism.blockMap 6 (G s))
    exact (Monomorphism.blockMap_homotopic_iff (by omega) (by omega) 6 F G).mp K
  · exact twistedBlockMap_homotopic

end NoExoticSixSphere.SpanningDiskFrameCoordinates
