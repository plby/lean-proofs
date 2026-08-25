import StackExchange.Puzzling139335.N4HalfLeg.Defs
import StackExchange.Puzzling139335.N4HalfLeg.Normals.Scalar

/-!
# Quantitative source normals forced by a half-height leg

A northwest normal has only one supporting point when the left half-height
vertex belongs to the source. Nontrivial right contacts therefore have a
strictly northeast source normal. The mandatory base endpoint and half-height
vertex then force its horizontal component to exceed `4 / 5`.
-/

open Set

namespace Puzzling139335.N4HalfLeg

open SourceFaceBridge PlaneIsometries

/-- A northwest normal uniquely supports a source containing the top-left
vertex of its containing lower half-square. -/
theorem eq_left_half_vertex_of_northwest_support {P : Set Plane}
    (hP : P ⊆ lowerHalfSquare) (hC : point 0 (1 / 2) ∈ P)
    {c s : ℝ} (hc : c < 0) (hs : 0 < s) {p : Plane}
    (hp : SupportsAt P c s p) : p = point 0 (1 / 2) := by
  have hbox := hP hp.1
  have hsum : s * (1 / 2 : ℝ) ≤ c * p 0 + s * p 1 := by
    simpa only [point_zero, point_one, mul_zero, zero_add] using hp.2 _ hC
  have hxterm : c * p 0 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc.le hbox.1.1
  have hyterm : s * p 1 ≤ s * (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_left hbox.2.2 hs.le
  have hpx : p 0 = 0 := by
    have hprod : c * p 0 = 0 := by linarith only [hsum, hxterm, hyterm]
    exact (mul_eq_zero.mp hprod).resolve_left hc.ne
  have hpy : p 1 = (1 / 2 : ℝ) := by
    have hprod : s * (p 1 - (1 / 2 : ℝ)) = 0 := by
      nlinarith only [hsum, hxterm, hyterm]
    have hz := (mul_eq_zero.mp hprod).resolve_left hs.ne'
    linarith only [hz]
  exact point_ext hpx hpy

/-- Actual right-side contact with positive span has a northeast source normal
if the source contains its left half-height vertex. -/
theorem right_normal_positive_of_left_halfleg {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (hC : Schoenflies.Plane.mk 0 (1 / 2) ∈ d.piece 0)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece i)
    (hNontriv : (d.piece i ∩ {p : Plane | p 0 = 1}).Nontrivial) :
    0 < linearMatrix e 0 0 ∧ 0 < linearMatrix e 0 1 := by
  have hs := h.right_contact_normal_up hc hi e he hNontriv
  refine ⟨?_, hs⟩
  have hn := h.middle_normal_nonaxis hc hi e he
  by_contra hnot
  have hneg : linearMatrix e 0 0 < 0 :=
    lt_of_le_of_ne (le_of_not_gt hnot) hn.1
  have hP : d.piece 0 ⊆ lowerHalfSquare := by
    intro p hp
    exact ⟨(d.piece_subset 0 hp).1, (d.piece_subset 0 hp).2.1,
      (h.outer_halves.1 hp).2.2⟩
  have hC' : point 0 (1 / 2) ∈ d.piece 0 := by
    simpa only [point, Schoenflies.Plane.mk] using hC
  obtain ⟨p, q, hpq, hp, hq⟩ := N4OuterPair.right_contacts_have_two_source_supports
    e he (d.piece_subset i) hNontriv
  exact hpq ((eq_left_half_vertex_of_northwest_support hP hC' hneg hs hp).trans
    (eq_left_half_vertex_of_northwest_support hP hC' hneg hs hq).symm)

/-- Orthogonality identifies the squared vertical span of the mandatory
half-leg points in either isometry parity. -/
theorem matrix_halfleg_span_sq (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (linearMatrix e 1 1 / 2 - linearMatrix e 1 0) ^ 2 =
      (linearMatrix e 0 1 + linearMatrix e 0 0 / 2) ^ 2 := by
  have hrow := linearMatrix_row_dot e 0 0
  have hcol0 := linearMatrix_column_dot e 0 0
  have hcol1 := linearMatrix_column_dot e 1 1
  have hcross := linearMatrix_column_dot e 0 1
  norm_num [pow_two, Fin.ext_iff] at hrow hcol0 hcol1 hcross
  nlinarith only [hrow, hcol0, hcol1, hcross]

private theorem affine_y_coordinates (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) :
    (e p) 1 = linearMatrix e 1 0 * p 0 + linearMatrix e 1 1 * p 1 + (e 0) 1 :=
  congrArg (fun q : Plane => q 1) (affine_apply_eq_matrix_coordinates e p)

/-- Strict actual heights of the base endpoint and half-leg vertex bound
the sum of the two source-normal components needed for the half-leg estimate. -/
theorem halfleg_projection_span_lt_one_of_strict_heights
    (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hB : 0 < (e (Schoenflies.Plane.mk 1 0)) 1 ∧
      (e (Schoenflies.Plane.mk 1 0)) 1 < 1)
    (hC : 0 < (e (Schoenflies.Plane.mk 0 (1 / 2))) 1 ∧
      (e (Schoenflies.Plane.mk 0 (1 / 2))) 1 < 1) :
    linearMatrix e 0 1 + linearMatrix e 0 0 / 2 < 1 := by
  have hdiff : (e (Schoenflies.Plane.mk 0 (1 / 2))) 1 -
      (e (Schoenflies.Plane.mk 1 0)) 1 =
      linearMatrix e 1 1 / 2 - linearMatrix e 1 0 := by
    have hBy := affine_y_coordinates e (Schoenflies.Plane.mk 1 0)
    have hCy := affine_y_coordinates e (Schoenflies.Plane.mk 0 (1 / 2))
    norm_num [Schoenflies.Plane.mk] at hBy hCy
    linarith only [hBy, hCy]
  have hsq := matrix_halfleg_span_sq e
  rw [← hdiff] at hsq
  have hprod : 0 <
      (1 - ((e (Schoenflies.Plane.mk 0 (1 / 2))) 1 -
        (e (Schoenflies.Plane.mk 1 0)) 1)) *
      (1 + ((e (Schoenflies.Plane.mk 0 (1 / 2))) 1 -
        (e (Schoenflies.Plane.mk 1 0)) 1)) :=
    mul_pos (by linarith only [hB.1, hC.2]) (by linarith only [hB.2, hC.1])
  nlinarith only [hsq, hprod,
    sq_nonneg (linearMatrix e 0 1 + linearMatrix e 0 0 / 2 - 1)]

/-- The quantitative acute-normal bound follows solely from the actual
outer-pair configuration, half-leg membership, and nontrivial right contact. -/
theorem right_normal_bounds_of_left_halfleg {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (hC : Schoenflies.Plane.mk 0 (1 / 2) ∈ d.piece 0)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece i)
    (hNontriv : (d.piece i ∩ {p : Plane | p 0 = 1}).Nontrivial) :
    (4 / 5 : ℝ) < linearMatrix e 0 0 ∧ 0 < linearMatrix e 0 1 ∧
      linearMatrix e 0 0 ^ 2 + linearMatrix e 0 1 ^ 2 = 1 := by
  obtain ⟨hcpos, hspos⟩ := right_normal_positive_of_left_halfleg h hc hC hi e he hNontriv
  have hunit : linearMatrix e 0 0 ^ 2 + linearMatrix e 0 1 ^ 2 = 1 := by
    simpa [pow_two] using linearMatrix_row_dot e 0 0
  have hBheight := h.middle_strict_height hc hi
    (he ▸ mem_image_of_mem e h.bottom_right_mk)
  have hCheight := h.middle_strict_height hc hi (he ▸ mem_image_of_mem e hC)
  have hspan := halfleg_projection_span_lt_one_of_strict_heights e hBheight hCheight
  exact ⟨cos_gt_four_fifths_of_halfleg_span hcpos hspos hunit hspan, hspos, hunit⟩

end Puzzling139335.N4HalfLeg
