import StackExchange.Puzzling139335.N6.TwoDouble.NormalizedTypes
import StackExchange.Puzzling139335.N6.TwoDouble.AdjacentCounting
import StackExchange.Puzzling139335.DoubleCorner
import StackExchange.Puzzling139335.DoubleCorner.MixedCorner

/-!
# Corner data for the normalized mixed singleton placement

The lower and upper outer pieces are horizontal reflections. The other
two pieces own the lower and upper right corners, respectively. Six total
incidences make those two corners double. If the congruence from the lower
outer piece fixed the lower right corner, the double-corner support theorem
would exclude the center from both remaining pieces.

Only actual piece memberships, congruences, and the incidence count are
used; no boundary-ray or angle data are assumed.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.MixedCornerGeometry

open ReflectionSeparation AcuteCorner

/-- The two known right-corner pairs account for all incidences beyond the
four required to cover the square's corners. -/
theorem normalized_mixed_corner_counts (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3) :
    d.cornerTileCount 0 = 1 ∧ d.cornerTileCount 1 = 2 ∧
      d.cornerTileCount 2 = 2 ∧ d.cornerTileCount 3 = 1 :=
  normalized_corner_counts_of_distinct_owners d hN (by decide) (by decide) hBR
    (normalized_top_right d hBR hreflect) hH hG

/-- The horizontal mirror fixes the center, so a protected center must
belong to one of the two pieces outside that reflected pair. -/
theorem center_mem_mixed_pair (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hreflect : horizontal '' d.piece 0 = d.piece 1) :
    squareCenter ∈ interior (d.piece 2) ∨ squareCenter ∈ interior (d.piece 3) := by
  have hexcluded := d.center_not_mem_fixed_pair (by decide : (0 : Fin 4) ≠ 1)
    horizontal hreflect horizontal_center
  obtain ⟨i, hi⟩ := hc
  fin_cases i
  · exact (hexcluded.1 hi).elim
  · exact (hexcluded.2 hi).elim
  · exact Or.inl hi
  · exact Or.inr hi

/-- The source right corner cannot map to the lower right corner of the
third piece: its supporting cone would transport to the fourth piece and
exclude the center from every possible owner. -/
theorem mixed_placement_not_fix_right_corner (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' d.piece 2 = d.piece 3)
    (hgBR : g (corner 1) = corner 2)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    e (corner 1) ≠ corner 1 := by
  intro hfix
  have hcounts := normalized_mixed_corner_counts d hN hBR hreflect hH hG
  have hTR := normalized_top_right d hBR hreflect
  have hotherBR : ∀ l, l ≠ (0 : Fin 4) → l ≠ 2 → corner 1 ∉ d.piece l := by
    intro l hl0 hl2
    exact other_not_mem_of_two_owners d (by decide) hBR hH hcounts.2.1 hl0 hl2
  have hsupport := d.double_corner_support_and_center_exclusion
    (by decide : (0 : Fin 4) ≠ 2) hBR hH hotherBR e he hfix
  have hsupportG : Supports45 (d.piece 3) (corner 2) := by
    simpa only [hg, hgBR] using hsupport.2.1.image g
  have hotherTR : ∀ l, l ≠ (3 : Fin 4) → l ≠ 1 → corner 2 ∉ d.piece l := by
    intro l hl3 hl1
    exact other_not_mem_of_two_owners d (by decide) hG hTR hcounts.2.2.1 hl3 hl1
  have hnotG := d.center_excluded_at_double_corner_of_support
    (by decide : (3 : Fin 4) ≠ 1) hG hTR hotherTR hsupportG
  obtain hcenter | hcenter := center_mem_mixed_pair d hc hreflect
  · exact hsupport.2.2.2 hcenter
  · exact hnotG hcenter

/-- The actual source of the third piece's lower right corner is a point
of the outer source piece different from its lower right corner. -/
theorem source_corner_preimage_data (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hBR : corner 1 ∈ d.piece 0)
    (hreflect : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' d.piece 2 = d.piece 3)
    (hgBR : g (corner 1) = corner 2)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    e.symm (corner 1) ∈ d.piece 0 ∧ e.symm (corner 1) ≠ corner 1 ∧
      e (e.symm (corner 1)) = corner 1 := by
  have hmem : e.symm (corner 1) ∈ d.piece 0 := by
    rw [← he] at hH
    obtain ⟨p, hp, hpBR⟩ := hH
    have hpEq : e.symm (corner 1) = p := by
      apply e.injective
      simpa only [e.apply_symm_apply] using hpBR.symm
    exact hpEq ▸ hp
  refine ⟨hmem, ?_, e.apply_symm_apply _⟩
  intro heq
  apply mixed_placement_not_fix_right_corner d hc hN hBR hreflect hH hG g hg hgBR e he
  simpa only [e.apply_symm_apply] using (congrArg e heq).symm

end Puzzling139335.N6.TwoDouble.MixedCornerGeometry
