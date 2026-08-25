import StackExchange.Puzzling139335.CentralRotation.Assembly
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation
import StackExchange.Puzzling139335.CentralRotation.Setup
import StackExchange.Puzzling139335.CentralRotation.HalfTurnCoefficient

/-!
# A direct congruence between the two sides of a central Jordan crosscut

The theorem has only the actual Jordan-crosscut, central-symmetry, and direct
isometry hypotheses.  Compatible boundary coordinates, increasing real lifts,
antipodal endpoints, finite first overlap, and the local half-turn are all
derived by the imported proved results.
-/

open Set Schoenflies

namespace Puzzling139335.JordanCrosscut

/-- A proper Jordan crosscut dividing a centrally symmetric Jordan region
into directly congruent sides contains the center whenever the congruence is
not a half-turn.  This includes the proper-rotation branch and requires no
boundary rectifiability, polygonality, or separately assumed orientation. -/
theorem center_mem_of_direct_non_halfTurn
    {C Γ M N : Set Plane} {p q c : Plane}
    (hcut : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle) (b : ℂ)
    (hg : ∀ x, PlaneIsometries.complexEquiv (g x) =
      (a : ℂ) * PlaneIsometries.complexEquiv x + b)
    (hnot : ∀ z, g ≠ AffineIsometryEquiv.pointReflection ℝ z)
    (hmap : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) : c ∈ Γ := by
  obtain ⟨d⟩ := hcut.exists_crosscutPaths houter
  have hh (x : Plane) : PlaneIsometries.complexEquiv
      (AffineIsometryEquiv.pointReflection ℝ c x) =
      ((-1 : Circle) : ℂ) * PlaneIsometries.complexEquiv x +
        2 * PlaneIsometries.complexEquiv c := by
    rw [CentralRotation.RotationAlgebra.complex_pointReflection]
    simp only [Circle.coe_neg, Circle.coe_one]
    ring
  obtain ⟨L⟩ := d.exists_boundaryLifts_of_direct hcut houter g
    (AffineIsometryEquiv.pointReflection ℝ c) hg hh hmap hsym
  exact CentralRotation.center_mem_of_boundaryLifts d.boundaryCoordinates g c L a b hg hnot
    (hcut.image_boundary_of_image_sides houter g hmap)
    (hcut.halfTurn_image_outer_of_congruent_sides houter ⟨g, hmap⟩ hsym)

/-- The coordinate-classification version of the direct branch: the sole
excluded multiplier is minus one, which is exactly the half-turn case. -/
theorem center_mem_of_direct_multiplier_ne_neg_one
    {C Γ M N : Set Plane} {p q c : Plane}
    (hcut : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle) (b : ℂ) (ha : a ≠ -1)
    (hg : ∀ x, PlaneIsometries.complexEquiv (g x) =
      (a : ℂ) * PlaneIsometries.complexEquiv x + b)
    (hmap : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) : c ∈ Γ :=
  hcut.center_mem_of_direct_non_halfTurn houter g a b hg
    (CentralRotation.RotationAlgebra.not_halfTurn_of_direct_coefficient_ne_neg_one g a b ha hg)
    hmap hsym

end Puzzling139335.JordanCrosscut
