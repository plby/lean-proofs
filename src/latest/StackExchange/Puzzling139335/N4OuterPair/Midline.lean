import StackExchange.Puzzling139335.N4OuterPair.Defs

/-!
# Interior midline crossing and outer-side avoidance

Weighted half-band saturation forces each non-bottom piece above the
midline and each non-top piece below it.  In particular both middle pieces
cross the midline in their interiors.  The actual Jordan height barrier
then excludes their contacts with the bottom and top sides.
-/

open Set

namespace Puzzling139335.RectangularHull

/-- The top-side version of the bottom height barrier, transported through
the actual horizontal affine isometry of the square. -/
theorem top_contact_below_height_impossible {P Q : Set Plane} {h r : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hTL : Schoenflies.Plane.mk 0 1 ∈ P) (hTR : Schoenflies.Plane.mk 1 1 ∈ P)
    (hheight : ∀ p ∈ P, h ≤ p 1) (hbelow : ∃ p ∈ Q, p 1 < h)
    (hr0 : 0 < r) (hr1 : r < 1) (hrQ : Schoenflies.Plane.mk r 1 ∈ Q) : False := by
  have hflip (x : ℝ) :
      ReflectionSeparation.horizontal (Schoenflies.Plane.mk x 1) =
        Schoenflies.Plane.mk x 0 := by
    ext i
    fin_cases i <;> simp
  have hPH : IsJordanRegion (ReflectionSeparation.horizontal '' P) :=
    hP.image_homeomorph ReflectionSeparation.horizontal.toHomeomorph
  have hQH : IsJordanRegion (ReflectionSeparation.horizontal '' Q) :=
    hQ.image_homeomorph ReflectionSeparation.horizontal.toHomeomorph
  have hPHS : ReflectionSeparation.horizontal '' P ⊆ unitSquare := by
    rintro _ ⟨p, hp, rfl⟩
    exact ReflectionSeparation.horizontal_mem_unitSquare.mpr (hPS hp)
  have hQHS : ReflectionSeparation.horizontal '' Q ⊆ unitSquare := by
    rintro _ ⟨p, hp, rfl⟩
    exact ReflectionSeparation.horizontal_mem_unitSquare.mpr (hQS hp)
  have hdisH : Disjoint (interior (ReflectionSeparation.horizontal '' P))
      (interior (ReflectionSeparation.horizontal '' Q)) :=
    disjoint_interiors_image_homeomorph hdis ReflectionSeparation.horizontal.toHomeomorph
  have hBL : Schoenflies.Plane.mk 0 0 ∈ ReflectionSeparation.horizontal '' P :=
    ⟨Schoenflies.Plane.mk 0 1, hTL, hflip 0⟩
  have hBR : Schoenflies.Plane.mk 1 0 ∈ ReflectionSeparation.horizontal '' P :=
    ⟨Schoenflies.Plane.mk 1 1, hTR, hflip 1⟩
  have hheightH : ∀ p ∈ ReflectionSeparation.horizontal '' P, p 1 ≤ 1 - h := by
    rintro _ ⟨p, hp, rfl⟩
    rw [ReflectionSeparation.horizontal_apply_one]
    linarith [hheight p hp]
  have haboveH : ∃ p ∈ ReflectionSeparation.horizontal '' Q, 1 - h < p 1 := by
    obtain ⟨p, hp, hph⟩ := hbelow
    refine ⟨ReflectionSeparation.horizontal p, mem_image_of_mem _ hp, ?_⟩
    rw [ReflectionSeparation.horizontal_apply_one]
    linarith
  have hrQH : Schoenflies.Plane.mk r 0 ∈ ReflectionSeparation.horizontal '' Q :=
    ⟨Schoenflies.Plane.mk r 1, hrQ, hflip r⟩
  exact bottom_contact_above_height_impossible hPH hQH hPHS hQHS hdisH
    hBL hBR hheightH haboveH hr0 hr1 hrQH

end Puzzling139335.RectangularHull

namespace Puzzling139335.N4OuterPair

namespace Configuration

variable {d : SquareDissection}

/-- Every piece other than the lower outer piece has an interior point
strictly above the midline. -/
theorem exists_interior_above (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i ≠ 0) :
    ∃ p ∈ interior (d.piece i), (1 / 2 : ℝ) < p 1 := by
  obtain ⟨c, hcenter⟩ := hc
  have hc0 : c ≠ 0 := by
    intro heq
    exact h.center_not_outer.1 (by simpa only [heq] using hcenter)
  by_cases hic : i = c
  · subst i
    exact (d.center_piece_crosses_midline hcenter).2
  · exact d.exists_interior_above_of_lower_piece hcenter hc0 (Ne.symm hic) hi.symm
      h.outer_halves.1

/-- Every piece other than the upper outer piece has an interior point
strictly below the midline. -/
theorem exists_interior_below (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i ≠ 1) :
    ∃ p ∈ interior (d.piece i), p 1 < (1 / 2 : ℝ) := by
  obtain ⟨c, hcenter⟩ := hc
  have hc1 : c ≠ 1 := by
    intro heq
    exact h.center_not_outer.2 (by simpa only [heq] using hcenter)
  by_cases hic : i = c
  · subst i
    exact (d.center_piece_crosses_midline hcenter).1
  · exact d.exists_interior_below_of_upper_piece hcenter hc1 (Ne.symm hic) hi.symm
      h.outer_halves.2

/-- The above-midline statement for every non-bottom piece. -/
theorem other_above (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i ≠ 0) :
    ∃ p ∈ interior (d.piece i), (1 / 2 : ℝ) < p 1 :=
  h.exists_interior_above hc hi

/-- The below-midline statement for every non-top piece. -/
theorem other_below (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i ≠ 1) :
    ∃ p ∈ interior (d.piece i), p 1 < (1 / 2 : ℝ) :=
  h.exists_interior_below hc hi

/-- Both middle pieces have interior points on both sides of the midline. -/
theorem middle_crosses_midline (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) :
    (∃ p ∈ interior (d.piece i), p 1 < (1 / 2 : ℝ)) ∧
      (∃ p ∈ interior (d.piece i), (1 / 2 : ℝ) < p 1) := by
  refine ⟨h.exists_interior_below hc ?_, h.exists_interior_above hc ?_⟩
  · rcases hi with rfl | rfl <;> decide
  · rcases hi with rfl | rfl <;> decide

/-- Every actual point of either middle piece has strictly positive height. -/
theorem middle_y_pos (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) {p : Plane} (hp : p ∈ d.piece i) :
    0 < p 1 := by
  have hpS := d.piece_subset i hp
  by_contra hnot
  have hpy : p 1 = 0 := le_antisymm (le_of_not_gt hnot) hpS.2.1
  have hpeq : p = Schoenflies.Plane.mk (p 0) 0 := by
    ext k
    fin_cases k
    · rfl
    · exact hpy
  have hpx0 : p 0 ≠ 0 := by
    intro hx
    have hcorner : p = corner 0 := by
      rw [hpeq, hx]
      norm_num [corner, Schoenflies.Plane.mk, Fin.ext_iff]
    exact h.middle_cornerless i hi 0 (hcorner ▸ hp)
  have hpx1 : p 0 ≠ 1 := by
    intro hx
    have hcorner : p = corner 1 := by
      rw [hpeq, hx]
      norm_num [corner, Schoenflies.Plane.mk, Fin.ext_iff]
    exact h.middle_cornerless i hi 1 (hcorner ▸ hp)
  obtain ⟨q, hq, hqy⟩ := (h.middle_crosses_midline hc hi).2
  have h0i : (0 : Fin 4) ≠ i := by rcases hi with rfl | rfl <;> decide
  exact RectangularHull.bottom_contact_above_height_impossible (d.jordan 0) (d.jordan i)
    (d.piece_subset 0) (d.piece_subset i) (d.disjoint_interiors h0i)
    h.bottom_left_mk h.bottom_right_mk (fun _ hz => (h.outer_halves.1 hz).2.2)
    ⟨q, interior_subset hq, hqy⟩
    (lt_of_le_of_ne hpS.1.1 hpx0.symm) (lt_of_le_of_ne hpS.1.2 hpx1)
    (hpeq ▸ hp)

/-- Neither middle piece meets the line containing the bottom side. -/
theorem middle_avoids_bottom (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) :
    Disjoint (d.piece i) {p : Plane | p 1 = 0} := by
  apply disjoint_left.mpr
  intro p hp hzero
  exact (ne_of_gt (h.middle_y_pos hc hi hp)) hzero

/-- Every actual point of either middle piece lies strictly below the top side. -/
theorem middle_y_lt_one (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) {p : Plane} (hp : p ∈ d.piece i) :
    p 1 < 1 := by
  have hpS := d.piece_subset i hp
  by_contra hnot
  have hpy : p 1 = 1 := le_antisymm hpS.2.2 (le_of_not_gt hnot)
  have hpeq : p = Schoenflies.Plane.mk (p 0) 1 := by
    ext k
    fin_cases k
    · rfl
    · exact hpy
  have hpx0 : p 0 ≠ 0 := by
    intro hx
    have hcorner : p = corner 3 := by
      rw [hpeq, hx]
      norm_num [corner, Schoenflies.Plane.mk, Fin.ext_iff]
    exact h.middle_cornerless i hi 3 (hcorner ▸ hp)
  have hpx1 : p 0 ≠ 1 := by
    intro hx
    have hcorner : p = corner 2 := by
      rw [hpeq, hx]
      norm_num [corner, Schoenflies.Plane.mk, Fin.ext_iff]
    exact h.middle_cornerless i hi 2 (hcorner ▸ hp)
  obtain ⟨q, hq, hqy⟩ := (h.middle_crosses_midline hc hi).1
  have h1i : (1 : Fin 4) ≠ i := by rcases hi with rfl | rfl <;> decide
  exact RectangularHull.top_contact_below_height_impossible (d.jordan 1) (d.jordan i)
    (d.piece_subset 1) (d.piece_subset i) (d.disjoint_interiors h1i)
    (h.top_side hc (left_mem_segment ℝ _ _))
    (h.top_side hc (right_mem_segment ℝ _ _))
    (fun _ hz => (h.outer_halves.2 hz).2.1) ⟨q, interior_subset hq, hqy⟩
    (lt_of_le_of_ne hpS.1.1 hpx0.symm) (lt_of_le_of_ne hpS.1.2 hpx1)
    (hpeq ▸ hp)

/-- Neither middle piece meets the line containing the top side. -/
theorem middle_avoids_top (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) :
    Disjoint (d.piece i) {p : Plane | p 1 = 1} := by
  apply disjoint_left.mpr
  intro p hp hone
  exact (ne_of_lt (h.middle_y_lt_one hc hi hp)) hone

/-- The entire closed middle piece, not only its interior, lies between
the two open outer-side height bounds. -/
theorem middle_strict_height (h : Configuration d) (hc : d.HasProtectedCenter)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) {p : Plane} (hp : p ∈ d.piece i) :
    0 < p 1 ∧ p 1 < 1 :=
  ⟨h.middle_y_pos hc hi hp, h.middle_y_lt_one hc hi hp⟩

end Configuration

end Puzzling139335.N4OuterPair
