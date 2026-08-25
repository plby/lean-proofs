import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.Geometry
import StackExchange.Puzzling139335.N4OuterPair.AxisNonzero
import StackExchange.Puzzling139335.PlaneIsometries.Matrix

/-!
# Choosing a source with an actual left half-arm

When the center is shifted to the left, reflect only the prototype in the
vertical midline and adjust its placement. This keeps all actual middle
pieces unchanged and avoids any orientation or relabeling assumption.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

open PlaneIsometries

structure LeftSource (d : SquareDissection) where
  carrier : Set Plane
  placement : Plane ≃ᵃⁱ[ℝ] Plane
  jordan : IsJordanRegion carrier
  band : carrier ⊆ horizontalBand 0 (1 / 2)
  base : segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ carrier
  arm : segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 (1 / 2)) ⊆ carrier
  image : placement '' carrier = d.piece 2
  oblique :
    placement (Schoenflies.Plane.mk 0 0) 0 ≠ placement (Schoenflies.Plane.mk 1 0) 0 ∧
    placement (Schoenflies.Plane.mk 0 0) 1 ≠ placement (Schoenflies.Plane.mk 1 0) 1

theorem image_base_oblique {d : SquareDissection} (h : N4OuterPair.Configuration d)
    (hc : d.HasProtectedCenter) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 2) :
    e (Schoenflies.Plane.mk 0 0) 0 ≠ e (Schoenflies.Plane.mk 1 0) 0 ∧
    e (Schoenflies.Plane.mk 0 0) 1 ≠ e (Schoenflies.Plane.mk 1 0) 1 := by
  have hn := h.middle_base_nonaxis hc (Or.inl rfl) e he
  have hA : Schoenflies.Plane.mk 0 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> rfl
  have hB : Schoenflies.Plane.mk 1 0 = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) := by
    ext i
    fin_cases i <;> simp [Schoenflies.Plane.mk]
  constructor
  · intro hcoord
    apply hn.1
    rw [linearMatrix_apply_eq_sub, ← hA, ← hB]
    exact sub_eq_zero.mpr hcoord.symm
  · intro hcoord
    apply hn.2
    rw [linearMatrix_apply_eq_sub, ← hA, ← hB]
    exact sub_eq_zero.mpr hcoord.symm

private theorem vertical_point (x y : ℝ) :
    ReflectionSeparation.vertical (Schoenflies.Plane.mk x y) =
      Schoenflies.Plane.mk (1 - x) y := by
  ext i
  fin_cases i <;> simp

theorem outer_half_arm {d : SquareDissection} (h : N4OuterPair.Configuration d)
    (hc : d.HasProtectedCenter) {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    (segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 (1 / 2)) ⊆ d.piece 0) ∨
    (segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 (1 / 2)) ⊆ d.piece 0) := by
  rcases lt_or_gt_of_ne (center_x_ne_half h hc hpair) with hleft | hright
  · exact Or.inr (right_arm_of_left_center h hpair hleft)
  · exact Or.inl (left_arm_of_right_center h hpair hright)

/-- This source is constructed from an actual congruence and the side-arm
ownership forced by the half-turn center. -/
theorem exists_left_source {d : SquareDissection} (h : N4OuterPair.Configuration d)
    (hc : d.HasProtectedCenter) {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3) :
    Nonempty (LeftSource d) := by
  obtain ⟨e, he⟩ := d.congruent 0 2
  have hoblique := image_base_oblique h hc e he
  rcases outer_half_arm h hc hpair with hleft | hright
  · exact ⟨⟨d.piece 0, e, d.jordan 0, h.outer_halves.1,
      h.bottom_side hc, hleft, he, hoblique⟩⟩
  · let V := ReflectionSeparation.vertical
    have hVbase : V '' segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) =
        segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) := by
      have himage : V '' segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) =
          segment ℝ (V (Schoenflies.Plane.mk 0 0)) (V (Schoenflies.Plane.mk 1 0)) :=
        image_segment ℝ V.toAffineEquiv.toAffineMap _ _
      rw [himage]
      simp only [V, vertical_point, sub_zero, sub_self, segment_symm]
    have hVarm : V ''
        segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 (1 / 2)) =
        segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 0 (1 / 2)) := by
      have himage : V ''
          segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 (1 / 2)) =
          segment ℝ (V (Schoenflies.Plane.mk 1 0))
            (V (Schoenflies.Plane.mk 1 (1 / 2))) :=
        image_segment ℝ V.toAffineEquiv.toAffineMap _ _
      rw [himage]
      simp only [V, vertical_point, sub_self]
    refine ⟨{ carrier := V '' d.piece 0
              placement := V.trans e
              jordan := (d.jordan 0).image_homeomorph V.toHomeomorph
              band := ?_
              base := ?_
              arm := ?_
              image := ?_
              oblique := ?_ }⟩
    · rintro _ ⟨p, hp, rfl⟩
      have hpbox := h.outer_halves.1 hp
      change (V p 0 ∈ Icc (0 : ℝ) 1) ∧ (V p 1 ∈ Icc (0 : ℝ) (1 / 2))
      simp only [V, ReflectionSeparation.vertical_apply_zero,
        ReflectionSeparation.vertical_apply_one]
      exact ⟨⟨by linarith [hpbox.1.2], by linarith [hpbox.1.1]⟩, hpbox.2⟩
    · rw [← hVbase]
      exact image_mono (h.bottom_side hc)
    · rw [← hVarm]
      exact image_mono hright
    · calc
        (V.trans e) '' (V '' d.piece 0) = e '' d.piece 0 := by
          rw [image_image]
          congr 1
          funext p
          change e (V (V p)) = e p
          rw [ReflectionSeparation.vertical_involutive]
        _ = d.piece 2 := he
    · change e (V (Schoenflies.Plane.mk 0 0)) 0 ≠
          e (V (Schoenflies.Plane.mk 1 0)) 0 ∧
        e (V (Schoenflies.Plane.mk 0 0)) 1 ≠
          e (V (Schoenflies.Plane.mk 1 0)) 1
      simp only [V, vertical_point, sub_zero, sub_self]
      exact ⟨hoblique.1.symm, hoblique.2.symm⟩

end Puzzling139335.N4MiddleInvolutions.HalfTurn
