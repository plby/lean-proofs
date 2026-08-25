import StackExchange.Puzzling139335.DoubleCorner
import StackExchange.Puzzling139335.BoundaryGerm

/-!
# An actual shared diagonal segment at a double corner

The two half-quadrant germs obtained from a corner-fixing congruence contain
a common short inward diagonal.  Transporting this segment out of the
normalized coordinates gives an actual segment in both closed pieces.
-/

open Set Metric

namespace Puzzling139335.DoubleCorner

open AcuteCorner PlaneIsometries

private theorem diagonal_unit_segment_subset_cones :
    segment ℝ (0 : Plane) !₂[1, 1] ⊆ cone45 ∩ upperCone45 := by
  intro x hx
  rw [segment_eq_image] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  constructor
  · simpa [cone45] using hu.1
  · simpa [upperCone45] using hu.1

/-- Opposite half-quadrant germs share a nontrivial straight diagonal
segment.  The endpoint parameter is at most one. -/
theorem diagonal_segment_of_halfCone_germs {P Q : Set Plane}
    (hP : SameBoundaryGerm P cone45 0)
    (hQ : SameBoundaryGerm Q upperCone45 0) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ segment ℝ (0 : Plane) !₂[t, t] ⊆ P ∩ Q := by
  obtain ⟨r, hr, hPeq⟩ := hP
  obtain ⟨s, hs, hQeq⟩ := hQ
  have hw : (!₂[(1 : ℝ), 1] : Plane) ≠ 0 := by
    intro h
    have h0 := congrArg (fun p : Plane => p 0) h
    norm_num at h0
  obtain ⟨a, ha0, haseg⟩ := exists_initial_segment_subset_ball hw (lt_min hr hs)
  have haFull : a ∈ segment ℝ (0 : Plane) !₂[1, 1] :=
    (haseg (right_mem_segment ℝ (0 : Plane) a)).1
  rw [segment_eq_image] at haFull
  obtain ⟨t, ht, hta⟩ := haFull
  have ha : a = (!₂[t, t] : Plane) := by
    rw [← hta]
    apply plane_ext <;> simp
  have htne : t ≠ 0 := by
    intro ht0
    apply ha0
    rw [ha, ht0]
    apply plane_ext <;> simp
  refine ⟨t, lt_of_le_of_ne ht.1 htne.symm, ht.2, ?_⟩
  rw [ha] at haseg
  intro x hx
  have hxboth := haseg hx
  have hxcones := diagonal_unit_segment_subset_cones hxboth.1
  refine ⟨?_, ?_⟩
  · exact ((Set.ext_iff.mp hPeq x).mpr
      ⟨ball_subset_ball (min_le_left r s) hxboth.2, hxcones.1⟩).2
  · exact ((Set.ext_iff.mp hQeq x).mpr
      ⟨ball_subset_ball (min_le_right r s) hxboth.2, hxcones.2⟩).2

end Puzzling139335.DoubleCorner

namespace Puzzling139335.SquareDissection

open SquareSymmetry DoubleCorner

/-- If exactly two pieces share a square corner and a congruence between
them fixes that corner, they contain an actual common inward-diagonal segment. -/
theorem double_corner_diagonal_segment (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner j) = corner j) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      segment ℝ (corner j) (cornerFlip j !₂[t, t]) ⊆ d.piece i ∩ d.piece k := by
  have hnormalized : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      segment ℝ (0 : Plane) !₂[t, t] ⊆
        (cornerFlip j '' d.piece i) ∩ (cornerFlip j '' d.piece k) := by
    rcases d.double_corner_normalized_halfCones hik hi hk hother e he hfix with h | h
    · exact diagonal_segment_of_halfCone_germs h.2.2.1 h.2.2.2
    · obtain ⟨t, ht0, ht1, hseg⟩ := diagonal_segment_of_halfCone_germs h.2.2.2 h.2.2.1
      exact ⟨t, ht0, ht1, by simpa only [inter_comm] using hseg⟩
  obtain ⟨t, ht0, ht1, hseg⟩ := hnormalized
  refine ⟨t, ht0, ht1, ?_⟩
  have himage : cornerFlip j '' segment ℝ (0 : Plane) !₂[t, t] =
      segment ℝ (corner j) (cornerFlip j !₂[t, t]) := by
    have hfseg : cornerFlip j '' segment ℝ (0 : Plane) !₂[t, t] =
        segment ℝ (cornerFlip j 0) (cornerFlip j !₂[t, t]) :=
      image_segment ℝ (cornerFlip j).toAffineMap (0 : Plane) (!₂[t, t] : Plane)
    simpa only [cornerFlip_zero] using hfseg
  rw [← himage]
  rintro x ⟨y, hy, rfl⟩
  have hyboth := hseg hy
  constructor
  · obtain ⟨p, hp, hpy⟩ := hyboth.1
    rw [← hpy, cornerFlip_involutive]
    exact hp
  · obtain ⟨p, hp, hpy⟩ := hyboth.2
    rw [← hpy, cornerFlip_involutive]
    exact hp

/-- Equality of the intrinsic corner points supplies the required
corner-fixing congruence for the common diagonal segment. -/
theorem same_intrinsic_double_corner_diagonal_segment (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (htype : d.intrinsicCorner i j = d.intrinsicCorner k j) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
      segment ℝ (corner j) (cornerFlip j !₂[t, t]) ⊆ d.piece i ∩ d.piece k :=
  d.double_corner_diagonal_segment hik hi hk hother (d.relativePlacement i k)
    (d.relativePlacement_image i k) (d.relativePlacement_corner htype)

end Puzzling139335.SquareDissection
