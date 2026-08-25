import StackExchange.Puzzling139335.N6.TwoDouble.HorizontalAcute.Geometry
import StackExchange.Puzzling139335.N6.TwoDouble.UnitRay

/-!
# The horizontal outer pair cannot have an acute-type singleton

Both actual outer sides are full unit segments. A singleton repeating the
outer right-corner type shares that corner with the corresponding outer
piece. The unit-ray theorem excludes the singleton at either the lower or
the upper double corner.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.HorizontalAcute

open ReflectionSeparation

/-- The lower singleton cannot repeat the lower outer piece's right-corner type. -/
theorem bottom_repeat_impossible (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (htype : d.intrinsicCorner 2 1 = d.intrinsicCorner 0 1) : False := by
  have hcount := (singleton_counts d hc hN hBL hBR hQ hH hG).1
  have hseg : segment ℝ (corner 1) (corner 0) ⊆ d.piece 0 := by
    simpa only [segment_symm] using full_bottom_side d hc hBL hBR hQ
  exact UnitRay.repeated_corner_singleton_unitRay_impossible d hc
    (by decide : (0 : Fin 4) ≠ 2) hBR hH
    (bottom_other_not_mem d hN hBR hQ hH hG)
    (d.relativePlacement 0 2) (d.relativePlacement_image 0 2)
    (d.relativePlacement_corner htype.symm) hcount hseg (Or.inr (by decide))

/-- The upper singleton cannot repeat the lower outer piece's right-corner type. -/
theorem top_repeat_impossible (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (htype : d.intrinsicCorner 3 2 = d.intrinsicCorner 0 1) : False := by
  have hcount := (singleton_counts d hc hN hBL hBR hQ hH hG).2
  obtain ⟨himage, hfix⟩ := top_fixing_placement d hQ
    (d.relativePlacement 0 3) (d.relativePlacement_image 0 3)
    (d.relativePlacement_corner htype.symm)
  exact UnitRay.repeated_corner_singleton_unitRay_impossible d hc
    (by decide : (1 : Fin 4) ≠ 3) (normalized_top_right d hBR hQ) hG
    (top_other_not_mem d hN hBR hQ hH hG)
    (horizontal.trans (d.relativePlacement 0 3)) himage hfix hcount
    (full_top_side d hc hBL hBR hQ) (Or.inl (by decide))

/-- The complete normalized horizontal branch in which either singleton
uses the repeated outer acute type. No local-angle or side-ownership
certificate is an assumption. -/
theorem normalized_impossible (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hQ : horizontal '' d.piece 0 = d.piece 1)
    (hH : corner 1 ∈ d.piece 2) (hG : corner 2 ∈ d.piece 3)
    (htype : d.intrinsicCorner 2 1 = d.intrinsicCorner 0 1 ∨
      d.intrinsicCorner 3 2 = d.intrinsicCorner 0 1) : False := by
  rcases htype with h | h
  · exact bottom_repeat_impossible d hc hN hBL hBR hQ hH hG h
  · exact top_repeat_impossible d hc hN hBL hBR hQ hH hG h

end Puzzling139335.N6.TwoDouble.HorizontalAcute
