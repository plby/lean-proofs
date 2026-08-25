import StackExchange.Puzzling139335.N4MiddleInvolutions.Basic
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Axes
import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Transport

/-!
# The intrinsic half-turn center lies below height one quarter

At height at least one quarter, a source in the lower half-square and
its half-turn image both lie above the source's unit base.  This makes
the actual base a supporting segment of their union.  An oblique image
of that segment contradicts the two coordinate-axis symmetries.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

open FaceBounds

/-- If the intrinsic center is high enough, the actual base supports the
entire source union, without a hull or regularity assumption. -/
theorem base_supports_union_of_quarter_le {P : Set Plane} {q : Plane}
    (hbox : P ⊆ horizontalBand 0 (1 / 2))
    (hbase : segment ℝ (Schoenflies.Plane.mk 0 0)
      (Schoenflies.Plane.mk 1 0) ⊆ P)
    (hq : (1 / 4 : ℝ) ≤ q 1) :
    SupportsSegment (P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P) 0 (-1)
      (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) := by
  have hy : ∀ p ∈ P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P, 0 ≤ p 1 := by
    intro p hp
    rcases hp with hp | ⟨z, hz, rfl⟩
    · exact (hbox hp).2.1
    · rw [pointReflection_coord]
      linarith [(hbox hz).2.2]
  refine ⟨Or.inl (hbase (left_mem_segment ℝ _ _)),
    Or.inl (hbase (right_mem_segment ℝ _ _)), ?_, ?_⟩
  · intro p hp
    simpa [supportValue, Schoenflies.Plane.mk] using neg_nonpos.mpr (hy p hp)
  · intro p hp
    simpa [supportValue, Schoenflies.Plane.mk] using neg_nonpos.mpr (hy p hp)

/-- An oblique placement of the actual base in an axis-symmetric source
union inside the square forces the intrinsic center below height `1/4`.
The statement uses no Jordan, convexity, center-membership, or area premise. -/
theorem upper_coordinate_lt_quarter {P : Set Plane}
    (hbox : P ⊆ horizontalBand 0 (1 / 2))
    (hbase : segment ℝ (Schoenflies.Plane.mk 0 0)
      (Schoenflies.Plane.mk 1 0) ⊆ P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hx : e (Schoenflies.Plane.mk 0 0) 0 ≠ e (Schoenflies.Plane.mk 1 0) 0)
    (hy : e (Schoenflies.Plane.mk 0 0) 1 ≠ e (Schoenflies.Plane.mk 1 0) 1)
    {q : Plane} {cx cy : ℝ}
    (hSquare : e '' (P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P) ⊆ unitSquare)
    (hV : MapsTo (verticalAbout cx)
      (e '' (P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P))
      (e '' (P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P)))
    (hH : MapsTo (horizontalAbout cy)
      (e '' (P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P))
      (e '' (P ∪ AffineIsometryEquiv.pointReflection ℝ q '' P))) :
    q 1 < (1 / 4 : ℝ) := by
  by_contra hnot
  have hsource := base_supports_union_of_quarter_le hbox hbase (not_lt.mp hnot)
  have hsupport := hsource.image_affineIsometry e
  have hunit := normalImage_unit e (show (0 : ℝ) ^ 2 + (-1 : ℝ) ^ 2 = 1 by norm_num)
  have hn := hsupport.normal_coordinates_ne_zero_of_oblique hunit hx hy
  apply no_unit_oblique_support_of_axis_symmetries hsupport hn.1 hn.2 hV hH hSquare
  rw [e.isometry.dist_eq]
  apply (sq_eq_sq₀ dist_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mp
  norm_num [plane_dist_sq, Schoenflies.Plane.mk]

end Puzzling139335.N4MiddleInvolutions.HalfTurn
