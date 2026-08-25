import StackExchange.Puzzling139335.RectangularHull.Interlacing.Regions
import StackExchange.Puzzling139335.SquareExterior

/-!
# Ownership of an actual ambient boundary arc

If one Jordan region contains the endpoints of an ambient boundary arc, a
region with disjoint interior that reaches the complementary boundary cannot
touch the arc away from its endpoints.  Applying this to the pieces of a
dissection and using coverage forces the whole arc into the first piece.
-/

open Set Schoenflies

namespace Puzzling139335.N8

/-- A Jordan region reaching outside the chosen ambient boundary arc cannot
touch its open part when another region owns both endpoints. -/
theorem boundary_arc_sdiff_disjoint_of_external_contact
    {P Q S A : Set Plane} {p q s : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q) (hS : IsJordanRegion S)
    (hPS : P ⊆ S) (hQS : Q ⊆ S)
    (hdis : Disjoint (interior P) (interior Q))
    (hA : IsArcBetween A p q) (hAS : A ⊆ frontier S)
    (hp : p ∈ P) (hq : q ∈ P) (hs : s ∈ Q)
    (hsS : s ∈ frontier S) (hsA : s ∉ A) :
    Disjoint (A \ {p, q}) Q := by
  apply Set.disjoint_left.mpr
  intro r hrA hrQ
  exact RectangularHull.boundary_arc_contacts_impossible hP hQ hS hPS hQS hdis
    hA hAS hp hq hrQ hs hrA hsS hsA

end N8

namespace SquareDissection

/-- Coverage turns the alternating-contact obstruction into ownership of an
entire actual square-boundary arc, including its two endpoints. -/
theorem boundary_arc_subset_of_other_pieces_have_external_contact
    (d : SquareDissection) {i : Fin 4} {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hAS : A ⊆ frontier unitSquare)
    (hp : p ∈ d.piece i) (hq : q ∈ d.piece i)
    (hothers : ∀ j, j ≠ i →
      ∃ s, s ∈ d.piece j ∧ s ∈ frontier unitSquare ∧ s ∉ A) :
    A ⊆ d.piece i := by
  intro r hr
  by_cases hends : r ∈ ({p, q} : Set Plane)
  · rcases mem_insert_iff.mp hends with rfl | hq'
    · exact hp
    · obtain rfl := mem_singleton_iff.mp hq'
      exact hq
  obtain ⟨j, hrj⟩ := d.exists_piece_mem (isClosed_unitSquare.frontier_subset (hAS hr))
  by_cases hji : j = i
  · simpa only [hji] using hrj
  obtain ⟨s, hs, hsS, hsA⟩ := hothers j hji
  have hdis := N8.boundary_arc_sdiff_disjoint_of_external_contact
    (d.jordan i) (d.jordan j) isJordanRegion_unitSquare
    (d.piece_subset i) (d.piece_subset j)
    (d.disjoint_interiors (fun hij => hji hij.symm)) hA hAS hp hq hs hsS hsA
  exact False.elim (Set.disjoint_left.mp hdis ⟨hr, hends⟩ hrj)

end SquareDissection

end Puzzling139335
