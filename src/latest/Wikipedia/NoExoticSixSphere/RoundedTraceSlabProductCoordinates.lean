import Wikipedia.NoExoticSixSphere.RoundedTraceTubeEndCoordinates
import Mathlib.Topology.UnitInterval

/-!
# The actual time slab as an interval times Euclidean space
-/

noncomputable section

open Set
open scoped Manifold ContDiff unitInterval

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {e : EuclideanEmbedding 6 M}

def slabProductMap (z : tubeSlab (e := e)) : I × Vector (e.ambientDimension + 6) :=
  (⟨timeGraphTimeFunctional (e := e) z.val, z.property⟩,
    (timeGraphCoordinates (e := e) z.val).2)

def slabProductInv (q : I × Vector (e.ambientDimension + 6)) : tubeSlab (e := e) :=
  ⟨(timeGraphCoordinates (e := e)).symm (q.1.val, q.2), by
    change (timeGraphCoordinates (e := e)
      ((timeGraphCoordinates (e := e)).symm (q.1.val, q.2))).1 ∈ Icc 0 1
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact q.1.property⟩

theorem continuous_slabProductMap : Continuous (slabProductMap (e := e)) :=
  (((timeGraphTimeFunctional (e := e)).continuous.comp continuous_subtype_val).subtype_mk _).prodMk
    (continuous_snd.comp ((timeGraphCoordinates (e := e)).continuous.comp continuous_subtype_val))

theorem continuous_slabProductInv : Continuous (slabProductInv (e := e)) :=
  ((timeGraphCoordinates (e := e)).symm.continuous.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

def slabProductCoordinates : tubeSlab (e := e) ≃ₜ (I × Vector (e.ambientDimension + 6)) where
  toFun := slabProductMap (e := e)
  invFun := slabProductInv (e := e)
  left_inv z := by
    apply Subtype.ext
    apply (timeGraphCoordinates (e := e)).injective
    change timeGraphCoordinates (e := e) ((timeGraphCoordinates (e := e)).symm
      (timeGraphTimeFunctional (e := e) z.val, (timeGraphCoordinates (e := e) z.val).2)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    rfl
  right_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      change (timeGraphCoordinates (e := e)
        ((timeGraphCoordinates (e := e)).symm (q.1.val, q.2))).1 = q.1.val
      rw [ContinuousLinearEquiv.apply_symm_apply]
    · change (timeGraphCoordinates (e := e)
        ((timeGraphCoordinates (e := e)).symm (q.1.val, q.2))).2 = q.2
      rw [ContinuousLinearEquiv.apply_symm_apply]
  continuous_toFun := continuous_slabProductMap
  continuous_invFun := continuous_slabProductInv

theorem slabProductCoordinates_time (z : tubeSlab (e := e)) :
    (slabProductCoordinates (e := e) z).1.val = timeGraphTimeFunctional (e := e) z.val := rfl

theorem slabProductCoordinates_space (z : tubeSlab (e := e)) :
    (slabProductCoordinates (e := e) z).2 = (timeGraphCoordinates (e := e) z.val).2 := rfl

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
