import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.OpenArcs
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.Junctions

/-!
# The two actual exterior arcs of the outer pair

The terminal side contacts are junctions, and strict contact uniqueness
excludes junctions from the open outer arcs.  Maximality therefore identifies
each whole three-segment arc with one actual exterior occurrence.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

variable {d : SquareDissection}

/-- The lower three-segment contact arc occurs as one complete exterior
arc and is paired with the lower outer tile. -/
theorem exists_lower_exterior_arc
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : a ∈ Ioc (0 : ℝ) (1 / 2))
    (hb : b ∈ Ioc (0 : ℝ) (1 / 2))
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    (F : ExactBoundaryArcFamily d) :
    ∃ k : Fin (F.n (.inr ())),
      F.partner (.inr ()) k = .inl 0 ∧
        F.arc (.inr ()) k = lowerOuterArc a b := by
  exact exists_exterior_arc_of_unique_tile F
    (lowerOuterArc_isArcBetween ha.1 hb.1)
    (lowerOuterArc_subset_frontier_unitSquare ha.1.le hb.1.le
      (by linarith only [ha.2]) (by linarith only [hb.2]))
    (side_terminal_mem_junctions h (Or.inl rfl) ha hleft).1
    (side_terminal_mem_junctions h (Or.inr rfl) hb hright).1
    (lowerOuterArc_interior_disjoint_junctions h hc ha.1 hb.1 hleft hright)
    (bottom_left_mem_lowerOuterArc a b) (fun _ hi => other_not_mem_bottom h hc 0 hi)

/-- The reflected upper three-segment contact arc occurs as one complete
exterior arc and is paired with the upper outer tile. -/
theorem exists_upper_exterior_arc
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : a ∈ Ioc (0 : ℝ) (1 / 2))
    (hb : b ∈ Ioc (0 : ℝ) (1 / 2))
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    (F : ExactBoundaryArcFamily d) :
    ∃ k : Fin (F.n (.inr ())),
      F.partner (.inr ()) k = .inl 1 ∧
        F.arc (.inr ()) k = upperOuterArc a b := by
  have hx : Schoenflies.Plane.mk 0 1 ∈ upperOuterArc a b := by
    refine ⟨Schoenflies.Plane.mk 0 0, bottom_left_mem_lowerOuterArc a b, ?_⟩
    ext j
    fin_cases j <;> simp
  exact exists_exterior_arc_of_unique_tile F
    (upperOuterArc_isArcBetween ha.1 hb.1)
    (upperOuterArc_subset_frontier_unitSquare ha.1.le hb.1.le
      (by linarith only [ha.2]) (by linarith only [hb.2]))
    (side_terminal_mem_junctions h (Or.inl rfl) ha hleft).2
    (side_terminal_mem_junctions h (Or.inr rfl) hb hright).2
    (upperOuterArc_interior_disjoint_junctions h hc ha.1 hb.1 hleft hright)
    hx (fun _ hi => other_not_mem_top h hc 0 hi)

/-- Both whole outer contact arcs are present in every exact exterior
boundary family, with their actual tile partners. -/
theorem exists_outer_exterior_arcs
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    {a b : ℝ} (ha : a ∈ Ioc (0 : ℝ) (1 / 2))
    (hb : b ∈ Ioc (0 : ℝ) (1 / 2))
    (hleft : ∀ y : ℝ,
      Schoenflies.Plane.mk 0 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) a)
    (hright : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) b)
    (F : ExactBoundaryArcFamily d) :
    ∃ k₀ k₁ : Fin (F.n (.inr ())),
      (F.partner (.inr ()) k₀ = .inl 0 ∧
        F.arc (.inr ()) k₀ = lowerOuterArc a b) ∧
      (F.partner (.inr ()) k₁ = .inl 1 ∧
        F.arc (.inr ()) k₁ = ReflectionSeparation.horizontal '' lowerOuterArc a b) := by
  obtain ⟨k₀, hk₀⟩ := exists_lower_exterior_arc h hc ha hb hleft hright F
  obtain ⟨k₁, hk₁⟩ := exists_upper_exterior_arc h hc ha hb hleft hright F
  exact ⟨k₀, k₁, hk₀, hk₁⟩

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
