import StackExchange.Puzzling139335.N4HalfLeg.Defs

/-!
# Extrema of actual right-side contacts

A compact set with two distinct contacts on the line `x = 1` has actual
lowest and highest contacts, with every other contact between them.
No interval-containment or connectedness hypothesis is required.
-/

open Set

namespace Puzzling139335.N4HalfLeg

open PlaneIsometries

/-- The vertical extrema of a nontrivial compact right-side contact are
attained at two distinct actual points. -/
theorem exists_right_contact_extrema {Q : Set Plane} (hQ : IsCompact Q)
    (hcontact : (Q ∩ {p : Plane | p 0 = 1}).Nontrivial) :
    ∃ bottom top : ℝ, bottom < top ∧
      Schoenflies.Plane.mk 1 bottom ∈ Q ∧ Schoenflies.Plane.mk 1 top ∈ Q ∧
      ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ Q → y ∈ Icc bottom top := by
  let K : Set Plane := Q ∩ {p : Plane | p 0 = 1}
  have hKcompact : IsCompact K := hQ.inter_right
    (isClosed_eq (Schoenflies.Plane.continuous_coord 0) continuous_const)
  obtain ⟨a, ha, b, hb, hab⟩ := hcontact
  have hKnonempty : K.Nonempty := ⟨a, ha⟩
  obtain ⟨bottom, hbottom, hmin⟩ := hKcompact.exists_isMinOn hKnonempty
    (Schoenflies.Plane.continuous_coord 1).continuousOn
  obtain ⟨top, htop, hmax⟩ := hKcompact.exists_isMaxOn hKnonempty
    (Schoenflies.Plane.continuous_coord 1).continuousOn
  have habheight : a 1 ≠ b 1 := by
    intro h
    exact hab (plane_ext (ha.2.trans hb.2.symm) h)
  have hba := (isMinOn_iff.mp hmin) a ha
  have hbb := (isMinOn_iff.mp hmin) b hb
  have hat := (isMaxOn_iff.mp hmax) a ha
  have hbt := (isMaxOn_iff.mp hmax) b hb
  have hlt : bottom 1 < top 1 := by
    rcases lt_or_gt_of_ne habheight with h | h <;> linarith
  have hbottom_eq : bottom = Schoenflies.Plane.mk 1 (bottom 1) :=
    plane_ext hbottom.2 rfl
  have htop_eq : top = Schoenflies.Plane.mk 1 (top 1) := plane_ext htop.2 rfl
  refine ⟨bottom 1, top 1, hlt, hbottom_eq ▸ hbottom.1, htop_eq ▸ htop.1, ?_⟩
  intro y hy
  exact ⟨(isMinOn_iff.mp hmin) _ ⟨hy, rfl⟩, (isMaxOn_iff.mp hmax) _ ⟨hy, rfl⟩⟩

end Puzzling139335.N4HalfLeg
