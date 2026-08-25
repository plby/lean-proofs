import StackExchange.Puzzling139335.N4OuterPair.CornerLegs
import StackExchange.Puzzling139335.N4OuterPair.SideGaps

/-!
# Positive actual side-contact heights

Local unique ownership gives positive contacts, and the crosscut and
compactness arguments identify the whole contact intervals.  The strict
upper bounds needed for two nondegenerate middle gaps are not assumed or
asserted by these lemmas.
-/

open Set

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

theorem positive_side_contact_interval (h : Configuration d) (hc : d.HasProtectedCenter)
    {x : ℝ} (hx : x = 0 ∨ x = 1) :
    ∃ b ∈ Ioc (0 : ℝ) (1 / 2),
      ∀ y : ℝ, Schoenflies.Plane.mk x y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b := by
  obtain ⟨b, hb, hcontact⟩ := h.side_contact_interval hc hx
  obtain ⟨a, ha, _, hpoint⟩ := h.exists_side_leg_point x hx
  have hab := ((hcontact a).mp hpoint).2
  exact ⟨b, ⟨ha.trans_le hab, hb.2⟩, hcontact⟩

/-- The two outer pieces have exactly the four reflected side intervals. -/
theorem exists_side_contact_heights (h : Configuration d) (hc : d.HasProtectedCenter) :
    ∃ a b : ℝ, a ∈ Ioc (0 : ℝ) (1 / 2) ∧ b ∈ Ioc (0 : ℝ) (1 / 2) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 0 y ∈ d.piece 1 ↔ y ∈ Icc (1 - a) (1 : ℝ)) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 1 ↔ y ∈ Icc (1 - b) (1 : ℝ)) := by
  obtain ⟨a, ha, hleft⟩ := h.positive_side_contact_interval hc (x := (0 : ℝ)) (Or.inl rfl)
  obtain ⟨b, hb, hright⟩ := h.positive_side_contact_interval hc (x := (1 : ℝ)) (Or.inr rfl)
  exact ⟨a, b, ha, hb, hleft, hright, h.upper_side_contact_iff hleft,
    h.upper_side_contact_iff hright⟩

end Puzzling139335.N4OuterPair.Configuration
