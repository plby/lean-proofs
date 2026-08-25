import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import StackExchange.Puzzling139335.ReflectionSeparation
import StackExchange.Puzzling139335.RectangularHull.FullSide

/-!
# Bounds forced by the actual reflected singleton placements

The hypotheses below are map identities and corner memberships in an actual
square dissection. Reflection separation and containment in the square yield
the parameter and source-height bounds. A positive vertical source germ at the
bottom-right corner makes the angular bound strict.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

noncomputable section

/-- Raw geometric data for the normalized reflected-singleton configuration. -/
structure SourceData (d : SquareDissection) (θ u v : ℝ) : Prop where
  angle_nonneg : 0 ≤ θ
  angle_le_half_pi : θ ≤ Real.pi / 2
  right_image : rightMap θ u v '' d.piece 0 = d.piece 1
  left_image : leftMap θ u v '' d.piece 0 = d.piece 2
  bottom_left : corner 0 ∈ d.piece 0
  bottom_right : corner 1 ∈ d.piece 0
  top_right : corner 2 ∈ d.piece 1
  top_left : corner 3 ∈ d.piece 2

theorem vertical_rightMap (θ u v : ℝ) (p : Plane) :
    ReflectionSeparation.vertical (rightMap θ u v p) = leftMap θ u v p := by
  ext i
  fin_cases i <;> simp [rightMap, leftMap] <;> ring

/-- Inverting the orthogonal source coordinates recovers the height. -/
theorem source_height_identity (θ : ℝ) (p : Plane) :
    p 1 = Real.sin θ * eCoord θ p + Real.cos θ * fCoord θ p := by
  have hc := congrArg (fun t : ℝ => t * p 1) (Real.sin_sq_add_cos_sq θ)
  dsimp [eCoord, fCoord]
  nlinarith only [hc]

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

theorem singleton_reflection (h : SourceData d θ u v) :
    ReflectionSeparation.vertical '' d.piece 1 = d.piece 2 := by
  rw [← h.right_image, Set.image_image, ← h.left_image]
  congr 1
  funext p
  exact vertical_rightMap θ u v p

theorem right_in_right_half (h : SourceData d θ u v) :
    d.piece 1 ⊆ {p : Plane | (1 / 2 : ℝ) ≤ p 0} := by
  rcases ReflectionSeparation.vertical_side (d.jordan 1) h.singleton_reflection
      (d.disjoint_interiors (by decide : (1 : Fin 4) ≠ 2)) with hleft | hright
  · have hbad := hleft h.top_right
    norm_num [corner, Fin.ext_iff] at hbad
  · exact hright

theorem right_mem_square (h : SourceData d θ u v) {p : Plane}
    (hp : p ∈ d.piece 0) : rightMap θ u v p ∈ unitSquare := by
  apply d.piece_subset 1
  rw [← h.right_image]
  exact mem_image_of_mem _ hp

theorem projection_bounds (h : SourceData d θ u v) {p : Plane}
    (hp : p ∈ d.piece 0) : eCoord θ p ≤ u ∧ fCoord θ p ≤ v := by
  have hfit := h.right_mem_square hp
  have hx := hfit.1.2
  have hy := hfit.2.2
  simp only [rightMap_zero_coord, rightMap_one_coord] at hx hy
  constructor <;> linarith

theorem u_le_half (h : SourceData d θ u v) : u ≤ 1 / 2 := by
  have hA : rightMap θ u v (corner 0) ∈ d.piece 1 := by
    rw [← h.right_image]
    exact mem_image_of_mem _ h.bottom_left
  have hhalf := h.right_in_right_half hA
  change (1 / 2 : ℝ) ≤ rightMap θ u v (corner 0) 0 at hhalf
  simp [rightMap, eCoord, corner] at hhalf
  linarith

theorem cos_le_u (h : SourceData d θ u v) : Real.cos θ ≤ u := by
  have hx := (h.projection_bounds h.bottom_right).1
  simpa [eCoord, corner] using hx

theorem v_nonneg (h : SourceData d θ u v) : 0 ≤ v := by
  have hy := (h.projection_bounds h.bottom_left).2
  simpa [fCoord, corner] using hy

theorem v_le_one_sub_sin (h : SourceData d θ u v) : v ≤ 1 - Real.sin θ := by
  have hy := (h.right_mem_square h.bottom_right).2.1
  simp [rightMap, fCoord, corner] at hy
  linarith

theorem parameters (h : SourceData d θ u v) :
    Real.cos θ ≤ u ∧ u ≤ 1 / 2 ∧ 0 ≤ v ∧ v ≤ 1 - Real.sin θ :=
  ⟨h.cos_le_u, h.u_le_half, h.v_nonneg, h.v_le_one_sub_sin⟩

theorem sin_nonneg (h : SourceData d θ u v) : 0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_nonneg_of_le_pi h.angle_nonneg
    (by linarith [h.angle_le_half_pi, Real.pi_pos])

theorem cos_nonneg (h : SourceData d θ u v) : 0 ≤ Real.cos θ :=
  Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [h.angle_nonneg, Real.pi_pos], h.angle_le_half_pi⟩

theorem cos_le_half (h : SourceData d θ u v) : Real.cos θ ≤ 1 / 2 :=
  h.cos_le_u.trans h.u_le_half

theorem angle_pos (h : SourceData d θ u v) : 0 < θ := by
  have hn : θ ≠ 0 := by
    intro heq
    have hc := h.cos_le_half
    norm_num [heq] at hc
  exact lt_of_le_of_ne h.angle_nonneg (Ne.symm hn)

theorem sin_pos (h : SourceData d θ u v) : 0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi h.angle_pos
    (by linarith [h.angle_le_half_pi, Real.pi_pos])

theorem cos_lt_u_of_germ (h : SourceData d θ u v)
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ !₂[1, ε] ∈ d.piece 0) : Real.cos θ < u := by
  obtain ⟨ε, hε, hp⟩ := hgerm
  have hx := (h.projection_bounds hp).1
  change Real.cos θ * 1 + Real.sin θ * ε ≤ u at hx
  have hprod := mul_pos h.sin_pos hε
  nlinarith only [hx, hprod]

theorem cos_lt_half_of_germ (h : SourceData d θ u v)
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ !₂[1, ε] ∈ d.piece 0) :
    Real.cos θ < 1 / 2 :=
  (h.cos_lt_u_of_germ hgerm).trans_le h.u_le_half

theorem angle_gt_pi_div_three_of_germ (h : SourceData d θ u v)
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ !₂[1, ε] ∈ d.piece 0) : Real.pi / 3 < θ := by
  by_contra hnot
  have hθ : θ ≤ Real.pi / 3 := le_of_not_gt hnot
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi h.angle_nonneg
    (by linarith [Real.pi_pos] : Real.pi / 3 ≤ Real.pi) hθ
  rw [Real.cos_pi_div_three] at hcos
  exact (not_lt_of_ge hcos) (h.cos_lt_half_of_germ hgerm)

theorem strict_parameters (h : SourceData d θ u v)
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ !₂[1, ε] ∈ d.piece 0) :
    Real.cos θ < u ∧ Real.cos θ < 1 / 2 ∧ Real.pi / 3 < θ :=
  ⟨h.cos_lt_u_of_germ hgerm, h.cos_lt_half_of_germ hgerm,
    h.angle_gt_pi_div_three_of_germ hgerm⟩

theorem height_bound (h : SourceData d θ u v) {p : Plane}
    (hp : p ∈ d.piece 0) : p 1 ≤ u * Real.sin θ + v * Real.cos θ := by
  obtain ⟨he, hf⟩ := h.projection_bounds hp
  calc
    p 1 = Real.sin θ * eCoord θ p + Real.cos θ * fCoord θ p :=
      source_height_identity θ p
    _ ≤ Real.sin θ * u + Real.cos θ * v :=
      add_le_add (mul_le_mul_of_nonneg_left he h.sin_nonneg)
        (mul_le_mul_of_nonneg_left hf h.cos_nonneg)
    _ = u * Real.sin θ + v * Real.cos θ := by ring

theorem height_coefficient_le_half (h : SourceData d θ u v) :
    u * Real.sin θ + v * Real.cos θ ≤ 1 / 2 := by
  have hu := mul_le_mul_of_nonneg_right h.u_le_half h.sin_nonneg
  have hv := mul_le_mul_of_nonneg_right h.v_le_one_sub_sin h.cos_nonneg
  have hc := mul_le_mul_of_nonneg_right h.cos_le_half
    (sub_nonneg.mpr (Real.sin_le_one θ))
  nlinarith only [hu, hv, hc]

theorem height_le_half (h : SourceData d θ u v) {p : Plane}
    (hp : p ∈ d.piece 0) : p 1 ≤ 1 / 2 :=
  (h.height_bound hp).trans h.height_coefficient_le_half

theorem height_coefficient_lt_half (h : SourceData d θ u v)
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ !₂[1, ε] ∈ d.piece 0)
    (hθ : θ < Real.pi / 2) :
    u * Real.sin θ + v * Real.cos θ < 1 / 2 := by
  have hcpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [h.angle_nonneg, Real.pi_pos], hθ⟩
  have hslt : Real.sin θ < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq θ, Real.sin_le_one θ,
      sq_pos_of_pos hcpos]
  have hu := mul_le_mul_of_nonneg_right h.u_le_half h.sin_nonneg
  have hv := mul_le_mul_of_nonneg_right h.v_le_one_sub_sin h.cos_nonneg
  have hc := mul_lt_mul_of_pos_right (h.cos_lt_half_of_germ hgerm)
    (sub_pos.mpr hslt)
  nlinarith only [hu, hv, hc]

theorem height_lt_half (h : SourceData d θ u v)
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ !₂[1, ε] ∈ d.piece 0)
    (hθ : θ < Real.pi / 2) {p : Plane} (hp : p ∈ d.piece 0) : p 1 < 1 / 2 :=
  (h.height_bound hp).trans_lt (h.height_coefficient_lt_half hgerm hθ)

theorem source_in_lower_half (h : SourceData d θ u v) :
    d.piece 0 ⊆ horizontalBand 0 (1 / 2) := by
  intro p hp
  have hfit := d.piece_subset 0 hp
  exact ⟨hfit.1, hfit.2.1, h.height_le_half hp⟩

theorem center_not_source (h : SourceData d θ u v) :
    squareCenter ∉ interior (d.piece 0) :=
  RectangularHull.center_not_in_interior_lower_half h.source_in_lower_half

theorem center_not_singletons (h : SourceData d θ u v) :
    squareCenter ∉ interior (d.piece 1) ∧
      squareCenter ∉ interior (d.piece 2) :=
  d.center_not_mem_fixed_pair (by decide : (1 : Fin 4) ≠ 2)
    ReflectionSeparation.vertical h.singleton_reflection
    ReflectionSeparation.vertical_center

theorem center_piece_three (h : SourceData d θ u v) (hc : d.HasProtectedCenter) :
    squareCenter ∈ interior (d.piece 3) := by
  obtain ⟨i, hi⟩ := hc
  fin_cases i
  · exact (h.center_not_source hi).elim
  · exact (h.center_not_singletons.1 hi).elim
  · exact (h.center_not_singletons.2 hi).elim
  · exact hi

/-- The full bottom segment is forced, also when the angle equals `π / 2`. -/
theorem bottom_side (h : SourceData d θ u v) (hc : d.HasProtectedCenter) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ d.piece 0 := by
  apply RectangularHull.lower_outer_piece_contains_bottom_side d hc
    (le_refl (1 / 2 : ℝ))
  · simpa [corner, Schoenflies.Plane.mk] using h.bottom_left
  · simpa [corner, Schoenflies.Plane.mk] using h.bottom_right
  · intro p hp
    exact h.height_le_half hp

end SourceData

end

end Puzzling139335.N4TwoOneOne
