import StackExchange.Puzzling139335.DoubleCorner.DiagonalSegment
import StackExchange.Puzzling139335.N6.TwoDouble.DiagonalPartner
import StackExchange.Puzzling139335.N6.TwoDouble.AdjacentCounting
import StackExchange.Puzzling139335.ReflectionSeparation.Maps

/-!
# Actual diagonal support and a diagonal sample for the normalized source

A repeated intrinsic corner at the bottom-right or top-right square corner
gives the normalized source a global supporting diagonal and an actual
positive sample on it. The double-corner theorem supplies the half-cones
and an actual common segment. No convex-hull chord is treated as a piece
segment.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

noncomputable section

open SquareSymmetry ReflectionSeparation AcuteCorner DoubleCorner

private theorem corner_one_not_mem_upper : corner 1 ∉ upperCone45 := by
  norm_num [upperCone45, corner, Fin.ext_iff]

/-- An actual source point on the normalized positive horizontal axis
chooses the lower one of the two half-cones. -/
theorem normalized_lower_of_double_corner (d : SquareDissection)
    {i k j : Fin 4} (hik : i ≠ k)
    (hi : corner j ∈ d.piece i) (hk : corner j ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner j ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner j) = corner j)
    {r : Plane} (hr : r ∈ d.piece i) (hrnorm : cornerFlip j r = corner 1) :
    cornerFlip j '' d.piece i ⊆ cone45 := by
  rcases d.double_corner_normalized_halfCones hik hi hk hother e he hfix with h | h
  · exact h.1
  · have hmem := h.1 (mem_image_of_mem (cornerFlip j) hr)
    rw [hrnorm] at hmem
    exact (corner_one_not_mem_upper hmem).elim

private theorem cornerFlip_one_corner_zero : cornerFlip 1 (corner 0) = corner 1 := by
  ext i
  fin_cases i <;> norm_num [cornerFlipPoint, corner, Fin.ext_iff]

private theorem cornerFlip_two_corner_three : cornerFlip 2 (corner 3) = corner 1 := by
  ext i
  fin_cases i <;> norm_num [cornerFlipPoint, corner, Fin.ext_iff]

private theorem cornerFlip_one_diagonal (t : ℝ) :
    cornerFlip 1 (!₂[t, t] : Plane) = diagonalSample t := by
  ext i
  fin_cases i <;> norm_num [cornerFlipPoint, corner, diagonalSample, Fin.ext_iff]

private theorem horizontal_corner_zero : horizontal (corner 0) = corner 3 := by
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

private theorem horizontal_corner_one : horizontal (corner 1) = corner 2 := by
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

private theorem horizontal_corner_two : horizontal (corner 2) = corner 1 := by
  ext i
  fin_cases i <;> norm_num [corner, Fin.ext_iff]

private theorem horizontal_cornerFlip_two_diagonal (t : ℝ) :
    horizontal (cornerFlip 2 (!₂[t, t] : Plane)) = diagonalSample t := by
  ext i
  fin_cases i <;> norm_num [cornerFlipPoint, corner, diagonalSample, Fin.ext_iff]

/-- At the bottom-right corner, the source's bottom-left corner chooses
the diagonal support `x+y≤1`, and the actual shared segment supplies a
positive source sample. -/
theorem bottom_data_of_double_corner (d : SquareDissection)
    {i k : Fin 4} (hik : i ≠ k)
    (hr : corner 0 ∈ d.piece i)
    (hi : corner 1 ∈ d.piece i) (hk : corner 1 ∈ d.piece k)
    (hother : ∀ l, l ≠ i → l ≠ k → corner 1 ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hfix : e (corner 1) = corner 1) :
    (∀ p ∈ d.piece i, p 0 + p 1 ≤ 1) ∧
      ∃ t : ℝ, 0 < t ∧ diagonalSample t ∈ d.piece i := by
  have hlower := normalized_lower_of_double_corner d hik hi hk hother e he hfix
    hr cornerFlip_one_corner_zero
  constructor
  · intro p hp
    have hbound : p 1 ≤ 1 - p 0 := by
      simpa [cornerFlipPoint, corner, Fin.ext_iff] using
        (hlower (mem_image_of_mem (cornerFlip 1) hp)).2
    linarith only [hbound]
  · obtain ⟨t, ht, _, hseg⟩ := d.double_corner_diagonal_segment hik hi hk hother e he hfix
    refine ⟨t, ht, ?_⟩
    have hpoint := (hseg (right_mem_segment ℝ (corner 1) (cornerFlip 1 !₂[t, t]))).1
    simpa only [cornerFlip_one_diagonal] using hpoint

/-- Top-right version. The source is first reflected horizontally; the
corner-fixing congruence is `e ∘ horizontal`. Both the support and the actual
sample are then transported back to the original source. -/
theorem top_data_of_double_corner (d : SquareDissection)
    {i j k : Fin 4} (hjk : j ≠ k)
    (hr : corner 0 ∈ d.piece i) (ha : corner 1 ∈ d.piece i)
    (hQ : d.piece j = horizontal '' d.piece i)
    (hother : ∀ l, l ≠ j → l ≠ k → corner 2 ∉ d.piece l)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece i = d.piece k)
    (hcorner : e (corner 1) = corner 2) :
    (∀ p ∈ d.piece i, p 0 + p 1 ≤ 1) ∧
      ∃ t : ℝ, 0 < t ∧ diagonalSample t ∈ d.piece i := by
  let f : Plane ≃ᵃⁱ[ℝ] Plane := horizontal.trans e
  have hfimage : f '' d.piece j = d.piece k := by
    calc
      f '' d.piece j = (fun p => e p) '' d.piece i := by
        rw [hQ, image_image]
        congr 1
        funext p
        change e (horizontal (horizontal p)) = e p
        rw [horizontal_involutive]
      _ = d.piece k := he
  have hffix : f (corner 2) = corner 2 := by
    change e (horizontal (corner 2)) = corner 2
    rw [horizontal_corner_two, hcorner]
  have hj : corner 2 ∈ d.piece j := by
    rw [hQ]
    exact ⟨corner 1, ha, horizontal_corner_one⟩
  have hk : corner 2 ∈ d.piece k := by
    rw [← he]
    exact ⟨corner 1, ha, hcorner⟩
  have hrj : corner 3 ∈ d.piece j := by
    rw [hQ]
    exact ⟨corner 0, hr, horizontal_corner_zero⟩
  have hlower := normalized_lower_of_double_corner d hjk hj hk hother f hfimage hffix
    hrj cornerFlip_two_corner_three
  constructor
  · intro p hp
    have hpj : horizontal p ∈ d.piece j := by
      rw [hQ]
      exact mem_image_of_mem horizontal hp
    have hbound : p 1 ≤ 1 - p 0 := by
      simpa [cornerFlipPoint, corner, Fin.ext_iff] using
        (hlower (mem_image_of_mem (cornerFlip 2) hpj)).2
    linarith only [hbound]
  · obtain ⟨t, ht, _, hseg⟩ :=
      d.double_corner_diagonal_segment hjk hj hk hother f hfimage hffix
    refine ⟨t, ht, ?_⟩
    have hpoint := (hseg (right_mem_segment ℝ (corner 2) (cornerFlip 2 !₂[t, t]))).1
    rw [hQ] at hpoint
    obtain ⟨p, hp, hpq⟩ := hpoint
    have hpeq : p = diagonalSample t := by
      calc
        p = horizontal (horizontal p) := (horizontal_involutive p).symm
        _ = horizontal (cornerFlip 2 (!₂[t, t] : Plane)) := by rw [hpq]
        _ = diagonalSample t := horizontal_cornerFlip_two_diagonal t
    exact hpeq ▸ hp

/-- The normalized three-piece bridge used in the two-double-corner case.
The multiplicity-two assumptions establish that the named pair exhausts
the relevant corner; no additional owner-exclusion premise is needed. -/
theorem right_corner_data_of_count_two (d : SquareDissection)
    (hr : corner 0 ∈ d.piece 0) (ha : corner 1 ∈ d.piece 0)
    (hQ : d.piece 1 = horizontal '' d.piece 0)
    (hBR : d.cornerTileCount 1 = 2) (hTR : d.cornerTileCount 2 = 2)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    (hcorner : e (corner 1) = corner 1 ∨ e (corner 1) = corner 2) :
    (∀ p ∈ d.piece 0, p 0 + p 1 ≤ 1) ∧
      ∃ t : ℝ, 0 < t ∧ diagonalSample t ∈ d.piece 0 := by
  rcases hcorner with hbottom | htop
  · have hk : corner 1 ∈ d.piece 2 := by
      rw [← he]
      exact ⟨corner 1, ha, hbottom⟩
    apply bottom_data_of_double_corner d (by decide) hr ha hk ?_ e he hbottom
    intro l hl0 hl2
    exact other_not_mem_of_two_owners d (by decide) ha hk hBR hl0 hl2
  · have hj : corner 2 ∈ d.piece 1 := by
      rw [hQ]
      exact ⟨corner 1, ha, horizontal_corner_one⟩
    have hk : corner 2 ∈ d.piece 2 := by
      rw [← he]
      exact ⟨corner 1, ha, htop⟩
    apply top_data_of_double_corner d (by decide) hr ha hQ ?_ e he htop
    intro l hl1 hl2
    exact other_not_mem_of_two_owners d (by decide) hj hk hTR hl1 hl2

end

end Puzzling139335.N6.TwoDouble
