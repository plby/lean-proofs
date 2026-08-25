import StackExchange.Puzzling139335.N4OuterPair.CornerLegs
import StackExchange.Puzzling139335.UnitPairs.RightCorner
import StackExchange.Puzzling139335.CornerSupport.Equality
import StackExchange.Puzzling139335.RectangularHull

/-!
# Symmetries preserve the bottom endpoint pair

The bottom outer piece has a full relative neighborhood at each of its two
square corners. Any isometric symmetry takes these corners to another unit
side pair of supporting right corners. Four distinct corners would force a
rectangular convex hull. If the pairs meet, uniqueness of a unit side partner
at the common full corner makes the pairs equal.

The argument applies to every affine-isometry symmetry, so it does not need
an involution or orientation-reversing hypothesis.
-/

open Set Metric

namespace Puzzling139335.N4Remainder

variable {d : SquareDissection}

theorem bottom_corner_full (h : N4OuterPair.Configuration d) {a : Fin 4}
    (ha : a = 0 ∨ a = 1) :
    UnitPairs.IsFullSquareCorner (d.piece 0) (corner a) := by
  obtain ⟨ε, hε, hnear⟩ :=
    d.unique_piece_relative_neighborhood 0 (h.bottom_corner_unique a ha)
  refine ⟨AffineIsometryEquiv.refl ℝ Plane, a, ε, hε, ?_, rfl, ?_⟩
  · simpa using d.piece_subset 0
  · simpa using hnear

theorem bottom_unit_side_pair (h : N4OuterPair.Configuration d) :
    UnitPairs.IsUnitSidePair (d.piece 0) (corner 0) (corner 1) := by
  refine ⟨h.bottom_left, h.bottom_right, ?_,
    AffineIsometryEquiv.refl ℝ Plane, 0, 1, ?_, rfl, rfl⟩
  · have hsq : dist (corner 0) (corner 1) ^ 2 = 1 := by
      norm_num [plane_dist_sq, corner, Fin.ext_iff]
    nlinarith [show 0 ≤ dist (corner 0) (corner 1) from dist_nonneg]
  · simpa using d.piece_subset 0

/-- An actual placement witnessing a unit side pair transports through
any Euclidean isometry. -/
theorem unit_side_pair_image {P : Set Plane} {a b : Plane}
    (h : UnitPairs.IsUnitSidePair P a b) (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    UnitPairs.IsUnitSidePair (e '' P) (e a) (e b) := by
  obtain ⟨ha, hb, hd, f, i, j, hf, hfa, hfb⟩ := h
  refine ⟨mem_image_of_mem e ha, mem_image_of_mem e hb,
    by simpa only [e.isometry.dist_eq] using hd,
    e.symm.trans f, i, j, ?_, ?_, ?_⟩
  · rintro _ ⟨q, ⟨p, hp, rfl⟩, rfl⟩
    change f (e.symm (e p)) ∈ unitSquare
    rw [e.symm_apply_apply]
    exact hf (mem_image_of_mem f hp)
  · change f (e.symm (e a)) = corner i
    rw [e.symm_apply_apply, hfa]
  · change f (e.symm (e b)) = corner j
    rw [e.symm_apply_apply, hfb]

/-- Four distinct supporting right corners of any actual piece contradict
the protected-center rectangular-hull obstruction. -/
theorem four_support_corners_impossible (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) {a b c f : Plane}
    (ha : SupportCorner (d.piece i) a) (hb : SupportCorner (d.piece i) b)
    (hcs : SupportCorner (d.piece i) c) (hf : SupportCorner (d.piece i) f)
    (hab : a ≠ b) (hac : a ≠ c) (haf : a ≠ f)
    (hbc : b ≠ c) (hbf : b ≠ f) (hcf : c ≠ f) : False := by
  classical
  apply d.no_rectangular_hull hc i
  apply CornerSupport.Equality.hasRectangularHull_of_card_four
    ({a, b, c, f} : Finset Plane)
  · exact Finset.card_eq_four.mpr ⟨a, b, c, f, hab, hac, haf, hbc, hbf, hcf, rfl⟩
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact ⟨ha⟩
    · exact ⟨hb⟩
    · exact ⟨hcs⟩
    · exact ⟨hf⟩

/-- Every intrinsic isometric symmetry of the bottom outer piece fixes or
exchanges its two bottom square corners. -/
theorem intrinsic_symmetry_bottom_pair_cases
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 0) :
    (e (corner 0) = corner 0 ∧ e (corner 1) = corner 1) ∨
      (e (corner 0) = corner 1 ∧ e (corner 1) = corner 0) := by
  classical
  have hab := bottom_unit_side_pair h
  have heab : UnitPairs.IsUnitSidePair (d.piece 0) (e (corner 0)) (e (corner 1)) := by
    simpa only [he] using unit_side_pair_image hab e
  have hfull0 := bottom_corner_full h (Or.inl rfl)
  have hfull1 := bottom_corner_full h (Or.inr rfl)
  by_cases h00 : e (corner 0) = corner 0
  · have h11 : corner 1 = e (corner 1) :=
      UnitPairs.unit_partners_eq_of_protected_center d hc 0 hfull0 hab
        (by simpa only [h00] using heab)
    exact Or.inl ⟨h00, h11.symm⟩
  by_cases h01 : e (corner 0) = corner 1
  · have h10 : corner 0 = e (corner 1) :=
      UnitPairs.unit_partners_eq_of_protected_center d hc 0 hfull1 hab.symm
        (by simpa only [h01] using heab)
    exact Or.inr ⟨h01, h10.symm⟩
  by_cases h10 : e (corner 1) = corner 0
  · have h01 : corner 1 = e (corner 0) :=
      UnitPairs.unit_partners_eq_of_protected_center d hc 0 hfull0 hab
        (by simpa only [h10] using heab.symm)
    exact Or.inr ⟨h01.symm, h10⟩
  by_cases h11 : e (corner 1) = corner 1
  · have h00 : corner 0 = e (corner 0) :=
      UnitPairs.unit_partners_eq_of_protected_center d hc 0 hfull1 hab.symm
        (by simpa only [h11] using heab.symm)
    exact Or.inl ⟨h00.symm, h11⟩
  have hs0 := (squareSupportCorner 0).mono (d.piece_subset 0) h.bottom_left
  have hs1 := (squareSupportCorner 1).mono (d.piece_subset 0) h.bottom_right
  have hes0 : SupportCorner (d.piece 0) (e (corner 0)) := by
    simpa only [he] using hs0.map e
  have hes1 : SupportCorner (d.piece 0) (e (corner 1)) := by
    simpa only [he] using hs1.map e
  exact (four_support_corners_impossible d hc 0 hs0 hs1 hes0 hes1
    hab.ne (Ne.symm h00) (Ne.symm h10) (Ne.symm h01) (Ne.symm h11) heab.ne).elim

/-- Set form of preservation of the bottom endpoint pair. -/
theorem intrinsic_symmetry_bottom_pair
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 0) :
    ({e (corner 0), e (corner 1)} : Set Plane) = {corner 0, corner 1} := by
  rcases intrinsic_symmetry_bottom_pair_cases h hc e he with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · simp only [h0, h1]
  · simp only [h0, h1, pair_comm]

/-- Image form used by the orientation-reversing pair classification. -/
theorem intrinsic_symmetry_bottom_pair_image
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 0) :
    e '' ({corner 0, corner 1} : Set Plane) = {corner 0, corner 1} := by
  rw [image_pair]
  exact intrinsic_symmetry_bottom_pair h hc e he

end Puzzling139335.N4Remainder
