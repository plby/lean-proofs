import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.GapGeometry
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.Uniqueness

/-! Actual middle exterior contacts stay in the gaps between the outer contacts. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

variable {d : SquareDissection}

theorem middle_side_point_mem_gap
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {x c y : ℝ} (hx : x = 0 ∨ x = 1) (hcHalf : c ≤ 1 / 2)
    (hcontact : ∀ z : ℝ,
      Schoenflies.Plane.mk x z ∈ d.piece 0 ↔ z ∈ Icc (0 : ℝ) c)
    {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (hy : Schoenflies.Plane.mk x y ∈ d.piece i) :
    Schoenflies.Plane.mk x y ∈ verticalGap x c := by
  have hi0 : i ≠ 0 := by rcases hi with rfl | rfl <;> decide
  have hi1 : i ≠ 1 := by rcases hi with rfl | rfl <;> decide
  have hy0 : 0 < y := h.middle_y_pos hc hi hy
  have hy1 : y < 1 := h.middle_y_lt_one hc hi hy
  have hlo : c ≤ y := by
    by_contra hnot
    exact other_not_mem_strict_lower_side h hc hx hcontact
      ⟨hy0, lt_of_not_ge hnot⟩ hi0 hy
  have hhi : y ≤ 1 - c := by
    by_contra hnot
    exact other_not_mem_strict_upper_side h hc hx hcontact
      ⟨lt_of_not_ge hnot, hy1⟩ hi1 hy
  exact (mem_verticalGap_iff hcHalf).mpr ⟨rfl, hlo, hhi⟩

/-- The only outer-square boundary available to either middle piece is the
union of the two closed vertical gaps. -/
theorem middle_frontier_contact_mem_gaps
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2)
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    {i : Fin 4} (hi : i = 2 ∨ i = 3) {z : Plane}
    (hz : z ∈ d.piece i) (hzS : z ∈ frontier unitSquare) :
    z ∈ verticalGap 0 a ∪ verticalGap 1 b := by
  rcases frontier_square_point_on_vertical_side hzS
    (h.middle_y_pos hc hi hz) (h.middle_y_lt_one hc hi hz) with hz0 | hz1
  · left
    have heq : z = Schoenflies.Plane.mk 0 (z 1) := by
      ext j
      fin_cases j
      · exact hz0
      · rfl
    rw [heq] at hz ⊢
    exact middle_side_point_mem_gap h hc (Or.inl rfl) ha hleft hi hz
  · right
    have heq : z = Schoenflies.Plane.mk 1 (z 1) := by
      ext j
      fin_cases j
      · exact hz1
      · rfl
    rw [heq] at hz ⊢
    exact middle_side_point_mem_gap h hc (Or.inr rfl) hb hright hi hz

/-- Every actual exterior occurrence naming a middle tile lies in the two
vertical gaps. -/
theorem middle_exterior_arc_subset_gaps
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2)
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    (F : ExactBoundaryArcFamily d) (k : Fin (F.n (Sum.inr ())))
    (hk : F.partner (Sum.inr ()) k = Sum.inl 2 ∨
      F.partner (Sum.inr ()) k = Sum.inl 3) :
    F.arc (Sum.inr ()) k ⊆ verticalGap 0 a ∪ verticalGap 1 b := by
  intro z hz
  have hzE := (F.subset_frontiers (Sum.inr ()) k hz).1
  change z ∈ frontier closedSquareExterior at hzE
  rw [frontier_closedSquareExterior] at hzE
  have hzP := (F.subset_frontiers (Sum.inr ()) k hz).2
  rcases hk with hk | hk
  · rw [hk] at hzP
    change z ∈ frontier (d.piece 2) at hzP
    exact middle_frontier_contact_mem_gaps h hc ha hb hleft hright (Or.inl rfl)
      ((d.jordan 2).isClosed.closure_eq ▸ hzP.1) hzE
  · rw [hk] at hzP
    change z ∈ frontier (d.piece 3) at hzP
    exact middle_frontier_contact_mem_gaps h hc ha hb hleft hright (Or.inr rfl)
      ((d.jordan 3).isClosed.closure_eq ▸ hzP.1) hzE

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
