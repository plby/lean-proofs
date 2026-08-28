import Wikipedia.NoExoticSixSphere.FamilyFlatteningInverse

/-!
# Actual derivatives in the reordered spatial directions

The reordered coordinates are fixed continuous linear equivalences. The
chain rule identifies derivatives in the time-zero directions with the
original spatial derivative, including both its leading and remaining blocks.
-/

noncomputable section

open Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilyFlattening

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_reordered (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (q : E × (T × ℝ)) :
    HasFDerivAt (fun r : E × (T × ℝ) ↦ f r.2.1 (r.1, r.2.2))
      ((fderiv ℝ (uncurry f) (sourceOrder q)).comp
        (sourceOrder (T := T) (E := E)).toContinuousLinearMap) q :=
  ((hf.differentiable (by simp) (sourceOrder q)).hasFDerivAt).comp q
    (sourceOrder (T := T) (E := E)).hasFDerivAt

theorem fderiv_head_spatial (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (q : E × (T × ℝ)) (x : E) (z : ℝ) :
    fderiv ℝ (head f) q (x, (0, z)) = (spatial f q (x, z)).1 := by
  unfold head
  rw [(hasFDerivAt_reordered f hf q).fst.fderiv, spatial,
    DiskHomotopy.spatial_fderiv_eq f hf]
  rfl

theorem fderiv_tail_spatial (f : T → E × ℝ → E × F) (hf : ContDiff ℝ ∞ (uncurry f))
    (q : E × (T × ℝ)) (x : E) (z : ℝ) :
    fderiv ℝ (tail f) q (x, (0, z)) = (spatial f q (x, z)).2 := by
  unfold tail
  rw [(hasFDerivAt_reordered f hf q).snd.fderiv, spatial,
    DiskHomotopy.spatial_fderiv_eq f hf]
  rfl

end NoExoticSixSphere.FamilyFlattening
