import StackExchange.Puzzling139335.CornerMass.Basic
import StackExchange.Puzzling139335.WeightedMass.Isometry
import StackExchange.Puzzling139335.IntrinsicCorners
import StackExchange.Puzzling139335.SquareSymmetry.Basic

/-!
# Rigid-motion invariance of local weighted mass

The ball and the actual interior/frontier density are transported together.
Thus intrinsic corner mass can be compared between the chosen tile placements
without any hypothesis that the boundary has area zero.
-/

open Set MeasureTheory
open scoped ENNReal

namespace Puzzling139335

noncomputable section

/-- A rigid motion preserves weighted mass in corresponding metric balls. -/
theorem localMass_image_affineIsometry (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (P : Set Plane) (v : Plane) (r : ℝ) :
    localMass (e '' P) (e v) r = localMass P v r := by
  unfold localMass
  rw [← (affineIsometry_measurePreserving e).setLIntegral_comp_preimage_emb
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (weightedDensity (e '' P)) (Metric.ball (e v) r)]
  rw [e.isometry.preimage_ball]
  exact lintegral_congr (weightedDensity_image_homeomorph e.toHomeomorph P)

namespace SquareDissection

/-- The chosen placement preserves local weighted mass at every prototype point. -/
theorem placement_localMass (d : SquareDissection) (i : Fin 4)
    (v : Plane) (r : ℝ) :
    localMass (d.piece i) (d.placement i v) r = localMass (d.piece 0) v r := by
  simpa only [d.placement_image] using
    localMass_image_affineIsometry (d.placement i) (d.piece 0) v r

/-- A physical square-corner mass equals the mass at its intrinsic corner type. -/
theorem localMass_intrinsicCorner (d : SquareDissection) (i j : Fin 4) (r : ℝ) :
    localMass (d.piece 0) (d.intrinsicCorner i j) r =
      localMass (d.piece i) (corner j) r := by
  simpa only [d.placement_intrinsicCorner] using
    (d.placement_localMass i (d.intrinsicCorner i j) r).symm

end SquareDissection

/-- Equal-radius neighborhoods of any two square corners have the same area
inside the square. The radius need not be positive or smaller than a side. -/
theorem volume_square_inter_ball_corner_eq (j k : Fin 4) (r : ℝ) :
    volume (unitSquare ∩ Metric.ball (corner j) r) =
      volume (unitSquare ∩ Metric.ball (corner k) r) := by
  have h (a : Fin 4) :
      volume (unitSquare ∩ Metric.ball (corner a) r) =
        volume (unitSquare ∩ Metric.ball (0 : Plane) r) := by
    have hball : SquareSymmetry.cornerFlip a '' Metric.ball (0 : Plane) r =
        Metric.ball (corner a) r := by
      simpa only [AffineIsometryEquiv.coe_toIsometryEquiv,
        SquareSymmetry.cornerFlip_zero] using
        (SquareSymmetry.cornerFlip a).toIsometryEquiv.image_ball (0 : Plane) r
    have hset : SquareSymmetry.cornerFlip a ''
        (unitSquare ∩ Metric.ball (0 : Plane) r) =
          unitSquare ∩ Metric.ball (corner a) r := by
      rw [Set.image_inter (SquareSymmetry.cornerFlip a).injective,
        SquareSymmetry.cornerFlip_image_unitSquare, hball]
    rw [← hset]
    exact volume_image_affineIsometry (SquareSymmetry.cornerFlip a) _
  exact (h j).trans (h k).symm

end

end Puzzling139335
