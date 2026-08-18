/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.Geometry
import ErdosProblems.Erdos1124.Similarity

/-!
# Affine glue for circle squaring

This file performs the last, elementary part of the argument.  The geometric
sets are first placed inside the half-open fundamental square by the common
affine map `x ↦ (1/2,1/2) + x/4`.  A torus equidecomposition of their
quotient images lifts to Euclidean space.  Translating by the negative center
and scaling by four then recovers the original disk and square.
-/

open Set

namespace Erdos1124.AffineGlue

noncomputable section

abbrev Plane := Geometry.Plane
abbrev Torus := TorusTransfer.Torus (Fin 2)

/-- The coordinate presentation of the unit-radius equal-area square used in
the final statement of Erdős Problem 1124. -/
def unitCoordinateSquare : Set Plane :=
  (@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹'
    Icc (fun _ ↦ -(Real.sqrt Real.pi) / 2) (fun _ ↦ Real.sqrt Real.pi / 2)

/-- The coordinate-interval and absolute-value presentations of the
equal-area square agree. -/
theorem unitCoordinateSquare_eq_equalAreaSquare :
    unitCoordinateSquare = Geometry.equalAreaSquare := by
  ext x
  change ((∀ i, -(Real.sqrt Real.pi) / 2 ≤ x i) ∧
      ∀ i, x i ≤ Real.sqrt Real.pi / 2) ↔
    |x 0| ≤ Geometry.squareHalfSide ∧ |x 1| ≤ Geometry.squareHalfSide
  simp only [Geometry.squareHalfSide, abs_le]
  rw [show -(Real.sqrt Real.pi / 2) = -(Real.sqrt Real.pi) / 2 by ring]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨⟨hl 0, hu 0⟩, ⟨hl 1, hu 1⟩⟩
  · rintro ⟨⟨hl0, hu0⟩, ⟨hl1, hu1⟩⟩
    constructor <;> intro i <;> fin_cases i
    · exact hl0
    · exact hl1
    · exact hu0
    · exact hu1

/-- The same identity with the harmless factor `1` left in the side length;
this is the literal expression obtained by unfolding `square 1` in the main
problem file. -/
theorem coordinateSquare_one_eq_equalAreaSquare :
    ((@WithLp.ofLp 2 (Fin 2 → ℝ)) ⁻¹'
      Icc (fun _ ↦ -(Real.sqrt Real.pi * 1) / 2)
        (fun _ ↦ Real.sqrt Real.pi * 1 / 2) : Set Plane) =
      Geometry.equalAreaSquare := by
  simpa [unitCoordinateSquare] using unitCoordinateSquare_eq_equalAreaSquare

/-- Undoing the common torus placement, first by translation and then by
scaling, sends the image of any planar set back to that set. -/
theorem unembed_image (E : Set Plane) :
    (fun y : Plane ↦ (4 : ℝ) • y) ''
        ((fun y : Plane ↦ -Geometry.torusCenter + y) '' (Geometry.torusEmbed '' E)) = E := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    simpa [Geometry.torusEmbed, smul_smul] using hw
  · intro hx
    refine ⟨(1 / 4 : ℝ) • x, ?_, ?_⟩
    · refine ⟨Geometry.torusEmbed x, ⟨x, hx, rfl⟩, ?_⟩
      simp [Geometry.torusEmbed]
    · simp [smul_smul]

/-- Exact end-stage reduction: a translation equidecomposition on the torus
between the quotient images of the two embedded shapes gives a Euclidean
translation equidecomposition of the original unit disk and coordinate
equal-area square. -/
theorem unit_equidecomp_of_torus
    (e : Equidecomp Torus (Multiplicative Torus))
    (hsource : e.source =
      TorusTransfer.quotientMap '' (Geometry.torusEmbed '' Geometry.unitDisk))
    (htarget : e.target =
      TorusTransfer.quotientMap '' (Geometry.torusEmbed '' Geometry.equalAreaSquare)) :
    ∃ e' : Equidecomp Plane (Multiplicative Plane),
      e'.source = Geometry.unitDisk ∧ e'.target = unitCoordinateSquare := by
  let lifted : Equidecomp Plane (Multiplicative Plane) :=
    TorusTransfer.liftEquidecomp
      Geometry.torusEmbed_unitDisk_subset_fundamentalCube
      Geometry.torusEmbed_equalAreaSquare_subset_fundamentalCube e hsource htarget
  let centered : Equidecomp Plane (Multiplicative Plane) :=
    translateEquidecomp lifted (-Geometry.torusCenter)
  let unembedded : Equidecomp Plane (Multiplicative Plane) :=
    scaleEquidecomp centered 4 (by norm_num)
  refine ⟨unembedded, ?_, ?_⟩
  · change (scaleEquidecomp centered 4 (by norm_num)).source = Geometry.unitDisk
    rw [scaleEquidecomp_source]
    change (fun y : Plane ↦ (4 : ℝ) • y) ''
      ((translateEquidecomp lifted (-Geometry.torusCenter)).source) = Geometry.unitDisk
    rw [translateEquidecomp_source]
    change (fun y : Plane ↦ (4 : ℝ) • y) ''
      ((fun y : Plane ↦ -Geometry.torusCenter + y) '' lifted.source) = Geometry.unitDisk
    rw [show lifted.source = Geometry.torusEmbed '' Geometry.unitDisk by rfl]
    exact unembed_image Geometry.unitDisk
  · change (scaleEquidecomp centered 4 (by norm_num)).target = unitCoordinateSquare
    rw [scaleEquidecomp_target]
    change (fun y : Plane ↦ (4 : ℝ) • y) ''
      ((translateEquidecomp lifted (-Geometry.torusCenter)).target) = unitCoordinateSquare
    rw [translateEquidecomp_target]
    change (fun y : Plane ↦ (4 : ℝ) • y) ''
      ((fun y : Plane ↦ -Geometry.torusCenter + y) '' lifted.target) = unitCoordinateSquare
    rw [show lifted.target = Geometry.torusEmbed '' Geometry.equalAreaSquare by rfl]
    rw [unembed_image Geometry.equalAreaSquare, unitCoordinateSquare_eq_equalAreaSquare]

/-- A version whose target uses the geometric absolute-value presentation
directly. -/
theorem unit_geometry_equidecomp_of_torus
    (e : Equidecomp Torus (Multiplicative Torus))
    (hsource : e.source =
      TorusTransfer.quotientMap '' (Geometry.torusEmbed '' Geometry.unitDisk))
    (htarget : e.target =
      TorusTransfer.quotientMap '' (Geometry.torusEmbed '' Geometry.equalAreaSquare)) :
    ∃ e' : Equidecomp Plane (Multiplicative Plane),
      e'.source = Geometry.unitDisk ∧ e'.target = Geometry.equalAreaSquare := by
  obtain ⟨e', hs, ht⟩ := unit_equidecomp_of_torus e hsource htarget
  exact ⟨e', hs, ht.trans unitCoordinateSquare_eq_equalAreaSquare⟩

end

end Erdos1124.AffineGlue
