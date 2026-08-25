import StackExchange.Puzzling139335.RectangularHull.Defs
import StackExchange.Puzzling139335.RectangularHull.Transport
import StackExchange.Puzzling139335.Basic

/-!
# Congruent rectangle frames for the actual dissection pieces
-/

open Set

namespace Puzzling139335

theorem HasRectangularHull.image {P : Set Plane} (hP : HasRectangularHull P)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) : HasRectangularHull (e '' P) := by
  obtain ⟨R, hR⟩ := hP
  exact ⟨R.map e, R.image_convexHull_eq_map_carrier e hR⟩

theorem HasRectangularHull.of_congruent {P Q : Set Plane}
    (hP : HasRectangularHull P) (hPQ : Congruent P Q) : HasRectangularHull Q := by
  obtain ⟨e, he⟩ := hPQ
  rw [← he]
  exact hP.image e

namespace RectangularHull

/-- All frames in this family describe actual convex hulls; their ordered
edge lengths agree because the frames are transported by congruences. -/
structure CommonFrames (d : SquareDissection) where
  frame : Fin 4 → Frame
  hull_eq : ∀ i, convexHull ℝ (d.piece i) = (frame i).carrier
  first_length_eq : ∀ i j, ‖(frame i).first‖ = ‖(frame j).first‖
  second_length_eq : ∀ i j, ‖(frame i).second‖ = ‖(frame j).second‖

theorem exists_commonFrames (d : SquareDissection) {i : Fin 4}
    (hi : HasRectangularHull (d.piece i)) : Nonempty (CommonFrames d) := by
  classical
  obtain ⟨R, hR⟩ := hi
  choose e he using d.congruent i
  refine ⟨⟨fun j => R.map (e j), ?_, ?_, ?_⟩⟩
  · intro j
    rw [← he j]
    exact R.image_convexHull_eq_map_carrier (e j) hR
  · intro j k
    simp only [Frame.map_first, LinearIsometryEquiv.norm_map]
  · intro j k
    simp only [Frame.map_second, LinearIsometryEquiv.norm_map]

end RectangularHull

end Puzzling139335
