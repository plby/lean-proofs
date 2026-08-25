import StackExchange.Puzzling139335.N7Geometry.Bounds

/-!
# The final normalized seven-incidence configuration cannot cover the square

The third placement's square containment is used to derive the source
inequalities. No enclosing hull quadrilateral is an assumption. In fact,
the lower-half containment of the source follows from those inequalities,
so it need not be supplied separately.

The left midpoint is missed by the source, its horizontal reflection, the
third placement, and both possible singleton placements.
-/

open Set

namespace Puzzling139335.N7Geometry

noncomputable section

@[simp] theorem Q_Q (p : Plane) : Q (Q p) = p := by
  ext i
  fin_cases i <;> simp [Q]

@[simp] theorem Q_leftMidpoint : Q leftMidpoint = leftMidpoint := by
  ext i
  fin_cases i <;> norm_num [Q, leftMidpoint]

/-- The source cannot contain the left midpoint because its third image
would have negative second coordinate. -/
theorem leftMidpoint_not_mem_source {P : Set Plane}
    (hT : T '' P ⊆ unitSquare) : leftMidpoint ∉ P := by
  intro hm
  have hfit := hT (mem_image_of_mem T hm)
  have hy := left_slice_bound hfit (p := leftMidpoint) rfl
  have hu := u_lt_quarter
  change (1 / 2 : ℝ) ≤ 2 * u at hy
  linarith only [hy, hu]

/-- Horizontal reflection fixes the left midpoint, so its image misses
the same point whenever the source does. -/
theorem leftMidpoint_not_mem_Q_image {P : Set Plane}
    (hT : T '' P ⊆ unitSquare) : leftMidpoint ∉ Q '' P := by
  rintro ⟨p, hp, heq⟩
  have hpm : p = leftMidpoint := by
    simpa only [Q_Q, Q_leftMidpoint] using congrArg Q heq
  exact leftMidpoint_not_mem_source hT (hpm ▸ hp)

/-- The third image has first coordinate at least one half. -/
theorem leftMidpoint_not_mem_T_image {P : Set Plane}
    (hP : P ⊆ unitSquare) : leftMidpoint ∉ T '' P := by
  rintro ⟨p, hp, heq⟩
  have hx := T_x_ge_half (hP hp)
  have heq0 := congrArg (fun z : Plane => z 0) heq
  rw [leftMidpoint_zero] at heq0
  rw [heq0] at hx
  norm_num at hx

/-- The first singleton placement has first coordinate at least the
strictly positive constant u, as a consequence of the third image's fit. -/
theorem leftMidpoint_not_mem_Uplus_image {P : Set Plane}
    (hT : T '' P ⊆ unitSquare) : leftMidpoint ∉ Uplus '' P := by
  rintro ⟨p, hp, heq⟩
  have hx := Uplus_x_ge_u (hT (mem_image_of_mem T hp))
  have heq0 := congrArg (fun z : Plane => z 0) heq
  rw [leftMidpoint_zero] at heq0
  rw [heq0] at hx
  exact (not_le_of_gt u_pos) hx

/-- The other singleton placement also stays a positive distance from
the left side. -/
theorem leftMidpoint_not_mem_Uminus_image {P : Set Plane}
    (hP : P ⊆ unitSquare) : leftMidpoint ∉ Uminus '' P := by
  rintro ⟨p, hp, heq⟩
  have hx := Uminus_x_ge_u (hP hp)
  have heq0 := congrArg (fun z : Plane => z 0) heq
  rw [leftMidpoint_zero] at heq0
  rw [heq0] at hx
  exact (not_le_of_gt u_pos) hx

/-- Even allowing both alternative singleton images does not cover the
left midpoint. -/
theorem leftMidpoint_not_mem_all_images {P : Set Plane}
    (hP : P ⊆ unitSquare) (hT : T '' P ⊆ unitSquare) :
    leftMidpoint ∉ P ∪ Q '' P ∪ T '' P ∪ Uplus '' P ∪ Uminus '' P := by
  simp only [mem_union, not_or]
  exact ⟨⟨⟨⟨leftMidpoint_not_mem_source hT, leftMidpoint_not_mem_Q_image hT⟩,
    leftMidpoint_not_mem_T_image hP⟩, leftMidpoint_not_mem_Uplus_image hT⟩,
    leftMidpoint_not_mem_Uminus_image hP⟩

/-- The normalized images cannot cover the square, independently of
Jordan regularity or boundary measure. -/
theorem normalized_images_do_not_cover {P : Set Plane}
    (hP : P ⊆ unitSquare) (hT : T '' P ⊆ unitSquare) :
    ¬ unitSquare ⊆ P ∪ Q '' P ∪ T '' P ∪ Uplus '' P ∪ Uminus '' P := by
  intro hcover
  exact leftMidpoint_not_mem_all_images hP hT (hcover leftMidpoint_mem_unitSquare)

/-- Actual four-piece normalization is impossible for either singleton
placement. Only the dissection's covering and containment facts are used. -/
theorem no_normalized_dissection (d : SquareDissection)
    (hQ : d.piece 1 = Q '' d.piece 0)
    (hT : d.piece 2 = T '' d.piece 0)
    (hU : d.piece 3 = Uplus '' d.piece 0 ∨ d.piece 3 = Uminus '' d.piece 0) : False := by
  have hP : d.piece 0 ⊆ unitSquare := d.piece_subset 0
  have hTfit : T '' d.piece 0 ⊆ unitSquare := by
    rw [← hT]
    exact d.piece_subset 2
  obtain ⟨i, hi⟩ := d.exists_piece_mem leftMidpoint_mem_unitSquare
  fin_cases i
  · exact leftMidpoint_not_mem_source hTfit hi
  · change leftMidpoint ∈ d.piece 1 at hi
    rw [hQ] at hi
    exact leftMidpoint_not_mem_Q_image hTfit hi
  · change leftMidpoint ∈ d.piece 2 at hi
    rw [hT] at hi
    exact leftMidpoint_not_mem_T_image hP hi
  · change leftMidpoint ∈ d.piece 3 at hi
    rcases hU with hU | hU
    · rw [hU] at hi
      exact leftMidpoint_not_mem_Uplus_image hTfit hi
    · rw [hU] at hi
      exact leftMidpoint_not_mem_Uminus_image hP hi

end

end Puzzling139335.N7Geometry
