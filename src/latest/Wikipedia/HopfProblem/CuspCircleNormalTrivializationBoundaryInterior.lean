import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCuspNeighborhood
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFour
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Interiors of the genuine closed normal-radius sublevels

The actual real-coordinate equivalence identifies the normal radius
with the standard Euclidean norm. Interior is then computed using the
usual closed-ball theorem and the open projections and open-subtype
inclusion. The resulting strict inequality concerns the unchanged
normal coordinates in the actual round product domain.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

/-- The literal Euclidean normal sublevel has precisely the strict sublevel as interior. -/
theorem interior_radiusSq_sublevel (r : ℝ) (hr : 0 < r) :
    interior {v : Fibre | radiusSq v ≤ r ^ 2} = {v : Fibre | radiusSq v < r ^ 2} := by
  have hs : {v : Fibre | radiusSq v ≤ r ^ 2} =
      RealFour.coordinateEquiv ⁻¹' closedBall (0 : RealFour.Space) r := by
    ext v
    exact RealFour.radiusSq_le_iff_mem_closedBall r hr.le v
  rw [hs, ← RealFour.coordinateEquiv.isOpenMap.preimage_interior_eq_interior_preimage
    RealFour.coordinateEquiv.continuous]
  rw [interior_closedBall (0 : RealFour.Space) (ne_of_gt hr)]
  ext v
  exact (RealFour.radiusSq_lt_iff_mem_ball r hr.le v).symm

/-- The same strict-sublevel formula in the original base-sphere product. -/
theorem interior_product_radiusSq_sublevel (r : ℝ) (hr : 0 < r) :
    interior {p : RiemannSphere × Fibre | radiusSq p.2 ≤ r ^ 2} =
      {p : RiemannSphere × Fibre | radiusSq p.2 < r ^ 2} := by
  change interior (Prod.snd ⁻¹' {v : Fibre | radiusSq v ≤ r ^ 2}) = _
  rw [← isOpenMap_snd.preimage_interior_eq_interior_preimage continuous_snd,
    interior_radiusSq_sublevel r hr]
  rfl

/-- Interior inside the actual open normal chart is still the literal strict radius sublevel. -/
theorem interior_round_radiusSq_sublevel (r : ℝ) (hr : 0 < r) :
    interior {p : roundNormalProduct | radiusSq p.val.2 ≤ r ^ 2} =
      {p : roundNormalProduct | radiusSq p.val.2 < r ^ 2} := by
  change interior ((Subtype.val : roundNormalProduct → RiemannSphere × Fibre) ⁻¹'
    {p : RiemannSphere × Fibre | radiusSq p.2 ≤ r ^ 2}) = _
  have hopen : IsOpenMap (Subtype.val : roundNormalProduct → RiemannSphere × Fibre) :=
    roundNormalProduct.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  rw [← hopen.preimage_interior_eq_interior_preimage continuous_subtype_val,
    interior_product_radiusSq_sublevel r hr]
  rfl

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
