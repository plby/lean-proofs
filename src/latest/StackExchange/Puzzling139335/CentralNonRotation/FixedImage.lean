import StackExchange.Puzzling139335.JordanRegion

/-! # A fixed point cannot lie in the interior of one of two disjoint images -/

open Set

namespace Puzzling139335.CentralNonRotation

/-- An isometry fixing a point preserves membership of that point in an
image interior. This does not require regularity of the set. -/
theorem mem_interior_image_iff_of_fixed (P : Set Plane)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) {c : Plane} (hfix : g c = c) :
    c ∈ interior (g '' P) ↔ c ∈ interior P := by
  change c ∈ interior (g.toHomeomorph '' P) ↔ c ∈ interior P
  rw [← g.toHomeomorph.image_interior]
  constructor
  · rintro ⟨x, hx, hxc⟩
    have heq : x = c := g.injective (hxc.trans hfix.symm)
    exact heq ▸ hx
  · intro hc
    exact ⟨c, hc, hfix⟩

/-- A fixed point of the congruence cannot be interior to either of two
regions having disjoint interiors. -/
theorem not_mem_interiors_of_fixed (P : Set Plane)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) {c : Plane} (hfix : g c = c)
    (hdis : Disjoint (interior P) (interior (g '' P))) :
    c ∉ interior P ∧ c ∉ interior (g '' P) := by
  have hiff := mem_interior_image_iff_of_fixed P g hfix
  constructor
  · intro hc
    exact disjoint_left.mp hdis hc (hiff.mpr hc)
  · intro hc
    exact disjoint_left.mp hdis (hiff.mp hc) hc

end Puzzling139335.CentralNonRotation
