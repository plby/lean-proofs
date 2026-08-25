import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.Components
import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.SquareExterior
import StackExchange.Puzzling139335.SquareExterior

/-!
# No bounded complementary components implies connected complement

Fix one point outside a bounded carrier.  Its component contains the connected
exterior.  Any different component misses that exterior, so lies in the bounded
carrier and would be one of the forbidden bounded components.
-/

open Set Bornology

namespace Puzzling139335.HalfTurnRemainder

noncomputable section

/-- For a set contained in a bounded carrier with nonempty connected exterior,
absence of bounded complementary components makes the whole complement
connected.  Closedness of the retained set is not needed for this implication. -/
theorem isConnected_compl_of_no_bounded_components
    {X : Type*} [TopologicalSpace X] [Bornology X] {U Q : Set X}
    (hUQ : U ⊆ Q) (hQbounded : IsBounded Q) (hQne : Qᶜ.Nonempty)
    (hQconn : IsPreconnected Qᶜ) (hnone : boundedComplementComponents U = ∅) :
    IsConnected Uᶜ := by
  obtain ⟨y, hyQ⟩ := hQne
  have hyU : y ∈ Uᶜ := fun hy => hyQ (hUQ hy)
  have hext : Qᶜ ⊆ connectedComponentIn Uᶜ y :=
    hQconn.subset_connectedComponentIn hyQ (compl_subset_compl.mpr hUQ)
  have heq {x : X} (hx : x ∈ Uᶜ) :
      connectedComponentIn Uᶜ x = connectedComponentIn Uᶜ y := by
    by_contra hne
    have hdis := component_disjoint_of_ne hne
    have hsub : connectedComponentIn Uᶜ x ⊆ Q := by
      intro z hz
      by_contra hzQ
      exact Set.disjoint_left.mp hdis hz (hext hzQ)
    have hbounded := hQbounded.subset hsub
    have hhole : connectedComponentIn Uᶜ x ∈ boundedComplementComponents U :=
      ⟨x, hx, rfl, hbounded⟩
    rw [hnone] at hhole
    exact hhole
  have hwhole : connectedComponentIn Uᶜ y = Uᶜ := by
    apply (connectedComponentIn_subset Uᶜ y).antisymm
    intro x hx
    rw [← heq hx]
    exact mem_connectedComponentIn hx
  rw [← hwhole]
  exact isConnected_connectedComponentIn_iff.mpr hyU

/-- The square-specialized implication, using the actual bounded square and
its connected unbounded exterior. -/
theorem isConnected_compl_of_no_bounded_square_components
    {U : Set Plane} (hUQ : U ⊆ unitSquare)
    (hnone : boundedComplementComponents U = ∅) : IsConnected Uᶜ :=
  isConnected_compl_of_no_bounded_components hUQ isJordanRegion_unitSquare.isBounded
    isConnected_compl_unitSquare.nonempty isPreconnected_compl_unitSquare hnone

end

end Puzzling139335.HalfTurnRemainder
