import StackExchange.Puzzling139335.N5.FourthSide.Obstruction
import StackExchange.Puzzling139335.N5.FourthSide.RightCoverage

/-!
# The fourth-piece side choice and forced right-side ownership

Starting with an actual normalized five-incidence dissection and a protected
center, the fourth piece has at most one contact on one of the right/top sides.
A common diagonal reflection and relabeling puts that side on the right and
leaves the prototype unchanged. Coverage and Jordan separation then determine
the exact right-side intervals of the source and singleton pieces.
-/

open Set

namespace Puzzling139335.N5

/-- All data for the subsequent actual right-arm argument, derived without
assuming a frame, a support normal, or a boundary interval. -/
theorem Normalized.exists_fourth_right_geometry {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    ∃ d' : SquareDissection, ∃ b : ℝ,
      Normalized d' ∧ d'.piece 0 = d.piece 0 ∧
      (d'.HasProtectedCenter ↔ d.HasProtectedCenter) ∧
      (d'.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton ∧
      0 < b ∧ b < 1 ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d'.piece 0 ↔ 0 ≤ y ∧ y ≤ b) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d'.piece 2 ↔ b ≤ y ∧ y ≤ 1) ∧
      segment ℝ (Schoenflies.Plane.mk 1 b) (corner 2) ⊆ d'.piece 2 := by
  obtain ⟨d', hd', hsource, hcenter, hright⟩ := h.exists_fourth_right_normalization hc
  obtain ⟨b, hb0, hb1, hP, hR, hsegment⟩ :=
    FourthSide.exists_right_contact_partition hd' hright
  exact ⟨d', b, hd', hsource, hcenter, hright, hb0, hb1, hP, hR, hsegment⟩

end Puzzling139335.N5
