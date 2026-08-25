import StackExchange.Puzzling139335.DoubleCorner.RotationCone

/-!
# Position of a supporting cone meeting a positive coordinate axis

A forty-five-degree supporting cone at the origin that meets a positive
coordinate axis away from the origin lies on one side of the diagonal.
Consequently any set contained in that cone omits an interior neighborhood
of the square center. These statements concern actual set containment.
-/

open Set

namespace Puzzling139335.DoubleCorner.MixedCorner

open AcuteCorner PlaneIsometries

/-- Contact with the positive horizontal axis gives a support below the diagonal. -/
theorem diagonal_support_of_positive_horizontal_contact {K : Set Plane} {a : Plane}
    (hK : Supports45 K 0) (ha : a ∈ K) (ha0 : 0 < a 0) (ha1 : a 1 = 0) :
    ∀ p ∈ K, p 1 ≤ p 0 := by
  intro p hp
  have hpair := hK.pair_bound ha hp
  simp only [sub_zero, det, dot, ha1, zero_mul, sub_zero, add_zero] at hpair
  exact (mul_le_mul_iff_right₀ ha0).mp ((le_abs_self _).trans hpair)

/-- Contact with the positive vertical axis gives a support above the diagonal. -/
theorem diagonal_support_of_positive_vertical_contact {K : Set Plane} {a : Plane}
    (hK : Supports45 K 0) (ha : a ∈ K) (ha0 : a 0 = 0) (ha1 : 0 < a 1) :
    ∀ p ∈ K, p 0 ≤ p 1 := by
  intro p hp
  have hpair := hK.pair_bound ha hp
  simp only [sub_zero, det, dot, ha0, zero_mul, zero_sub, zero_add, abs_neg] at hpair
  exact (mul_le_mul_iff_right₀ ha1).mp ((le_abs_self _).trans hpair)

/-- A nonzero point on either positive axis fixes a diagonal supporting half-plane. -/
theorem diagonal_support_of_positive_axis_contact {K : Set Plane} {a : Plane}
    (hK : Supports45 K 0) (ha : a ∈ K) (hane : a ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) (haxis : a 0 = 0 ∨ a 1 = 0) :
    (∀ p ∈ K, p 0 ≤ p 1) ∨ (∀ p ∈ K, p 1 ≤ p 0) := by
  rcases haxis with hzero | hzero
  · left
    have hpos : 0 < a 1 := by
      refine lt_of_le_of_ne ha1 ?_
      intro h
      exact hane (plane_ext hzero (by simpa using h.symm))
    exact diagonal_support_of_positive_vertical_contact hK ha hzero hpos
  · right
    have hpos : 0 < a 0 := by
      refine lt_of_le_of_ne ha0 ?_
      intro h
      exact hane (plane_ext (by simpa using h.symm) hzero)
    exact diagonal_support_of_positive_horizontal_contact hK ha hpos hzero

/-- Any subset of a supporting cone with positive-axis contact omits the center's interior. -/
theorem squareCenter_not_mem_interior_of_positive_axis_contact
    {P K : Set Plane} {a : Plane}
    (hK : Supports45 K 0) (hP : P ⊆ K) (ha : a ∈ K) (hane : a ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) (haxis : a 0 = 0 ∨ a 1 = 0) :
    squareCenter ∉ interior P := by
  apply squareCenter_not_mem_interior_of_diagonal_support
  rcases diagonal_support_of_positive_axis_contact hK ha hane ha0 ha1 haxis with h | h
  · exact Or.inl (fun p hp => h p (hP hp))
  · exact Or.inr (fun p hp => h p (hP hp))

/-- The isometric image of the explicit cone is supported at the origin
when the isometry fixes the origin. -/
theorem supports45_image_cone45 (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) :
    Supports45 (e '' cone45) 0 := by
  have hcone : Supports45 cone45 0 := by
    refine ⟨AffineIsometryEquiv.refl ℝ Plane, rfl, ?_⟩
    simp
  simpa only [he0] using hcone.image e

/-- Positive-axis contact puts an origin-fixed image of the explicit cone
in one diagonal half-plane, including reflected images. -/
theorem image_cone45_diagonal_support_of_positive_axis_contact
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) {a : Plane}
    (ha : a ∈ e '' cone45) (hane : a ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) (haxis : a 0 = 0 ∨ a 1 = 0) :
    (∀ p ∈ e '' cone45, p 0 ≤ p 1) ∨ (∀ p ∈ e '' cone45, p 1 ≤ p 0) :=
  diagonal_support_of_positive_axis_contact (supports45_image_cone45 e he0)
    ha hane ha0 ha1 haxis

/-- A piece in such an image cone cannot protect the square center. -/
theorem squareCenter_not_mem_interior_of_image_cone45_positive_axis_contact
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he0 : e 0 = 0) {P : Set Plane} {a : Plane}
    (hP : P ⊆ e '' cone45) (ha : a ∈ e '' cone45) (hane : a ≠ 0)
    (ha0 : 0 ≤ a 0) (ha1 : 0 ≤ a 1) (haxis : a 0 = 0 ∨ a 1 = 0) :
    squareCenter ∉ interior P :=
  squareCenter_not_mem_interior_of_positive_axis_contact
    (supports45_image_cone45 e he0) hP ha hane ha0 ha1 haxis

end Puzzling139335.DoubleCorner.MixedCorner
