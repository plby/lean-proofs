import StackExchange.Puzzling139335.N4TwoOneOne.SourceBounds

/-!
# Open rectangles forced by the aligned outgoing placements

Only actual set images and coverage are used. Once the source is below `H`,
an outer third above `H` can be covered by only one singleton. Translating
that open rectangle then forces the middle third into the fourth piece.
-/

open Set

namespace Puzzling139335.N4TwoOneOne.AlignedOutgoing

noncomputable section

/-- Horizontal translation by the signed distance `a`. -/
def horizontalShift (a : ℝ) (p : Plane) : Plane := !₂[p 0 + a, p 1]

@[simp] theorem horizontalShift_zero (a : ℝ) (p : Plane) :
    horizontalShift a p 0 = p 0 + a := rfl

@[simp] theorem horizontalShift_one (a : ℝ) (p : Plane) :
    horizontalShift a p 1 = p 1 := rfl

/-- An open rectangle with upper edge on the top square side. -/
def openRectangle (a b H : ℝ) : Set Plane :=
  {p | p 0 ∈ Ioo a b ∧ p 1 ∈ Ioo H 1}

theorem isOpen_openRectangle (a b H : ℝ) : IsOpen (openRectangle a b H) :=
  (isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).inter
    (isOpen_Ioo.preimage (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1))

variable {d : SquareDissection} {θ u v H : ℝ}

theorem left_half (h : SourceData d θ u v) {p : Plane} (hp : p ∈ d.piece 2) :
    p 0 ≤ 1 / 2 := by
  rw [← h.singleton_reflection] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  have hx := h.right_in_right_half hq
  change (1 / 2 : ℝ) ≤ q 0 at hx
  simp only [ReflectionSeparation.vertical_apply_zero]
  linarith

/-- With the fourth piece translated left from the right singleton, the
right third above the source is interior to that singleton. -/
theorem right_rectangle_forced (h : SourceData d θ u v)
    (hD : horizontalShift (-(1 / 3 : ℝ)) '' d.piece 1 = d.piece 3)
    (hH : ∀ p ∈ d.piece 0, p 1 ≤ H) (hH0 : 0 ≤ H) :
    openRectangle (2 / 3) 1 H ⊆ interior (d.piece 1) := by
  apply interior_maximal ?_ (isOpen_openRectangle _ _ _)
  intro p hp
  obtain ⟨hx, hy⟩ := hp
  have hpS : p ∈ unitSquare :=
    ⟨⟨by linarith [hx.1], hx.2.le⟩, ⟨by linarith [hy.1], hy.2.le⟩⟩
  obtain ⟨i, hi⟩ := d.exists_piece_mem hpS
  fin_cases i
  · have hlow := hH p hi
    linarith [hy.1]
  · exact hi
  · have hleft := left_half h hi
    linarith [hx.1]
  · change p ∈ d.piece 3 at hi
    rw [← hD] at hi
    obtain ⟨q, hq, hqp⟩ := hi
    have hqx := (d.piece_subset 1 hq).1.2
    have hpx := congrArg (fun z : Plane => z 0) hqp
    simp only [horizontalShift_zero] at hpx
    linarith [hx.1]

/-- The translated forced right rectangle gives the whole open middle
third to the fourth piece. -/
theorem middle_rectangle_forced_from_right (h : SourceData d θ u v)
    (hD : horizontalShift (-(1 / 3 : ℝ)) '' d.piece 1 = d.piece 3)
    (hH : ∀ p ∈ d.piece 0, p 1 ≤ H) (hH0 : 0 ≤ H) :
    openRectangle (1 / 3) (2 / 3) H ⊆ interior (d.piece 3) := by
  apply interior_maximal ?_ (isOpen_openRectangle _ _ _)
  intro p hp
  let q : Plane := !₂[p 0 + 1 / 3, p 1]
  have hq : q ∈ openRectangle (2 / 3) 1 H := by
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · change (2 / 3 : ℝ) < p 0 + 1 / 3
      linarith [hp.1.1]
    · change p 0 + 1 / 3 < (1 : ℝ)
      linarith [hp.1.2]
  have hqP := interior_subset (right_rectangle_forced h hD hH hH0 hq)
  rw [← hD]
  refine ⟨q, hqP, ?_⟩
  ext i
  fin_cases i <;> simp [horizontalShift, q]

/-- The mirror placement forces the left third into the left singleton. -/
theorem left_rectangle_forced (h : SourceData d θ u v)
    (hD : horizontalShift (1 / 3 : ℝ) '' d.piece 2 = d.piece 3)
    (hH : ∀ p ∈ d.piece 0, p 1 ≤ H) (hH0 : 0 ≤ H) :
    openRectangle 0 (1 / 3) H ⊆ interior (d.piece 2) := by
  apply interior_maximal ?_ (isOpen_openRectangle _ _ _)
  intro p hp
  obtain ⟨hx, hy⟩ := hp
  have hpS : p ∈ unitSquare :=
    ⟨⟨hx.1.le, by linarith [hx.2]⟩, ⟨by linarith [hy.1], hy.2.le⟩⟩
  obtain ⟨i, hi⟩ := d.exists_piece_mem hpS
  fin_cases i
  · have hlow := hH p hi
    linarith [hy.1]
  · have hright := h.right_in_right_half hi
    change (1 / 2 : ℝ) ≤ p 0 at hright
    linarith [hx.2]
  · exact hi
  · change p ∈ d.piece 3 at hi
    rw [← hD] at hi
    obtain ⟨q, hq, hqp⟩ := hi
    have hqx := (d.piece_subset 2 hq).1.1
    have hpx := congrArg (fun z : Plane => z 0) hqp
    simp only [horizontalShift_zero] at hpx
    linarith [hx.2]

/-- Translating the forced left rectangle gives the same middle third. -/
theorem middle_rectangle_forced_from_left (h : SourceData d θ u v)
    (hD : horizontalShift (1 / 3 : ℝ) '' d.piece 2 = d.piece 3)
    (hH : ∀ p ∈ d.piece 0, p 1 ≤ H) (hH0 : 0 ≤ H) :
    openRectangle (1 / 3) (2 / 3) H ⊆ interior (d.piece 3) := by
  apply interior_maximal ?_ (isOpen_openRectangle _ _ _)
  intro p hp
  let q : Plane := !₂[p 0 - 1 / 3, p 1]
  have hq : q ∈ openRectangle 0 (1 / 3) H := by
    refine ⟨⟨?_, ?_⟩, hp.2⟩
    · change (0 : ℝ) < p 0 - 1 / 3
      linarith [hp.1.1]
    · change p 0 - 1 / 3 < (1 / 3 : ℝ)
      linarith [hp.1.2]
  have hqP := interior_subset (left_rectangle_forced h hD hH hH0 hq)
  rw [← hD]
  refine ⟨q, hqP, ?_⟩
  ext i
  fin_cases i <;> simp [horizontalShift, q]

end

end Puzzling139335.N4TwoOneOne.AlignedOutgoing
