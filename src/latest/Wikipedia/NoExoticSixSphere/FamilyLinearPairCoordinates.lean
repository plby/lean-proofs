import Wikipedia.NoExoticSixSphere.FamilyLinearCoordinates
import Wikipedia.NoExoticSixSphere.FamilySharedTimeCurve
import Wikipedia.NoExoticSixSphere.FamilyDoublePointSymmetry

/-!
# Fixed linear coordinates on the actual family double-point closure

Apply the rank-adapted source equivalence to both spatial points, retaining
their common time. The invertible target change preserves equality of
images. This gives a homeomorphism on the actual closures, compatible with
swapping and with globally smooth ambient coordinate maps.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilyLinearCoordinates

open CorankOneCoordinates

variable {T V W E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def sourcePairs (c : Coordinates V W E F) :
    (T × (V × V)) ≃L[ℝ] T × ((E × ℝ) × (E × ℝ)) :=
  (ContinuousLinearEquiv.refl ℝ T).prodCongr (c.1.prodCongr c.1)

theorem sourcePairs_doublePoints (c : Coordinates V W E F) (f : T → V → W) :
    MapsTo (sourcePairs c) (FamilyEmbedding.doublePoints f)
      (FamilyEmbedding.doublePoints (family c f)) := by
  intro r hr
  refine ⟨fun he ↦ hr.1 (c.1.injective he), ?_⟩
  change c.2 (f r.1 (c.1.symm (c.1 r.2.1))) = c.2 (f r.1 (c.1.symm (c.1 r.2.2)))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg c.2 hr.2

theorem sourcePairs_symm_doublePoints (c : Coordinates V W E F) (f : T → V → W) :
    MapsTo (sourcePairs c).symm (FamilyEmbedding.doublePoints (family c f))
      (FamilyEmbedding.doublePoints f) := by
  intro r hr
  exact ⟨fun he ↦ hr.1 (c.1.symm.injective he), c.2.injective hr.2⟩

def closedPairCoordinates (c : Coordinates V W E F) (f : T → V → W) :
    closure (FamilyEmbedding.doublePoints f) ≃ₜ
      closure (FamilyEmbedding.doublePoints (family c f)) where
  toFun r := ⟨sourcePairs c r.val,
    (sourcePairs_doublePoints c f).closure (sourcePairs c).continuous r.property⟩
  invFun r := ⟨(sourcePairs c).symm r.val,
    (sourcePairs_symm_doublePoints c f).closure (sourcePairs c).symm.continuous r.property⟩
  left_inv r := Subtype.ext ((sourcePairs c).symm_apply_apply r.val)
  right_inv r := Subtype.ext ((sourcePairs c).apply_symm_apply r.val)
  continuous_toFun := ((sourcePairs c).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((sourcePairs c).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem closedPairCoordinates_swap (c : Coordinates V W E F) (f : T → V → W)
    (r : closure (FamilyEmbedding.doublePoints f)) :
    closedPairCoordinates c f (FamilyEmbedding.swapClosure f r) =
      FamilySharedTimePairs.swapClosure (family c f) (closedPairCoordinates c f r) :=
  Subtype.ext rfl

theorem sourcePairs_diagonal (c : Coordinates V W E F) (p : T × V) :
    sourcePairs c (p.1, (p.2, p.2)) =
      FamilySharedTimePairs.fromTrack ((sourceEquiv c).symm p, (sourceEquiv c).symm p) := rfl

end NoExoticSixSphere.FamilyLinearCoordinates
