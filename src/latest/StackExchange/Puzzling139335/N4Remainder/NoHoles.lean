import StackExchange.Puzzling139335.N4OuterPair.Defs
import StackExchange.Puzzling139335.CornerIncidence
import StackExchange.Puzzling139335.PlaneIsometries
import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.ConnectedComplement

/-!
# The reflected outer-pair remainder has no holes

An omitted outer piece has a connected interior and owns a square corner
which does not belong to the retained middle pieces.  Adjoining that corner
connects its interior to the square exterior.  Its complementary component
is therefore unbounded.  Every bounded complementary component would have
to meet one of these two omitted interiors, which is impossible.

Only the actual closed Jordan regions and corner ownership are used.  In
particular, no polygonality, finite boundary length, or Jordan-union premise
is required.
-/

open Set Bornology

namespace Puzzling139335.N4Remainder

/-- A connected omitted interior which reaches the carrier exterior at an
uncovered boundary point belongs to an unbounded complementary component. -/
theorem component_unbounded_of_exterior_contact
    {U B Q : Set Plane} {a b : Plane}
    (hUQ : U ⊆ Q) (hQconn : IsPreconnected Qᶜ)
    (hQunbounded : ¬ IsBounded Qᶜ)
    (hBconn : IsPreconnected (interior B))
    (hBregular : closure (interior B) = B)
    (hBU : Disjoint (interior B) U)
    (haB : a ∈ B) (haU : a ∉ U) (haext : a ∈ closure Qᶜ)
    (hb : b ∈ interior B) :
    ¬ IsBounded (connectedComponentIn Uᶜ b) := by
  have hI : IsPreconnected (interior B ∪ {a}) := by
    apply hBconn.subset_closure subset_union_left
    rintro x (hx | hx)
    · exact subset_closure hx
    · rcases hx with rfl
      rwa [hBregular]
  have hE : IsPreconnected (Qᶜ ∪ {a}) := by
    apply hQconn.subset_closure subset_union_left
    rintro x (hx | hx)
    · exact subset_closure hx
    · rcases hx with rfl
      exact haext
  have hconn : IsPreconnected ((interior B ∪ {a}) ∪ (Qᶜ ∪ {a})) :=
    hI.union' ⟨a, Or.inr rfl, Or.inr rfl⟩ hE
  have hsub : (interior B ∪ {a}) ∪ (Qᶜ ∪ {a}) ⊆ Uᶜ := by
    rintro x ((hx | hx) | (hx | hx))
    · exact Set.disjoint_left.mp hBU hx
    · rcases hx with rfl
      exact haU
    · exact fun hxU => hx (hUQ hxU)
    · rcases hx with rfl
      exact haU
  have hcomp := hconn.subset_connectedComponentIn
    (show b ∈ (interior B ∪ {a}) ∪ (Qᶜ ∪ {a}) from Or.inl (Or.inl hb)) hsub
  intro hbounded
  exact hQunbounded (hbounded.subset fun x hx => hcomp (Or.inr (Or.inl hx)))

end Puzzling139335.N4Remainder

namespace Puzzling139335.N4OuterPair.Configuration

open HalfTurnRemainder N4Remainder

variable {d : SquareDissection}

/-- Each omitted outer interior belongs to the unbounded component of the
middle union's complement. -/
theorem outer_component_unbounded (h : Configuration d) {i : Fin 4}
    (hi : i = 0 ∨ i = 1) {b : Plane} (hb : b ∈ interior (d.piece i)) :
    ¬ IsBounded (connectedComponentIn (d.piece 2 ∪ d.piece 3)ᶜ b) := by
  have hUQ : d.piece 2 ∪ d.piece 3 ⊆ unitSquare :=
    union_subset (d.piece_subset 2) (d.piece_subset 3)
  have hdis : Disjoint (interior (d.piece i)) (d.piece 2 ∪ d.piece 3) := by
    apply disjoint_union_right.mpr
    constructor
    · exact d.disjoint_interior_piece (by rcases hi with rfl | rfl <;> decide)
    · exact d.disjoint_interior_piece (by rcases hi with rfl | rfl <;> decide)
  have hexterior (k : Fin 4) : corner k ∈ closure unitSquareᶜ := by
    rw [closure_compl]
    exact corner_not_mem_interior_unitSquare k
  rcases hi with rfl | rfl
  · exact component_unbounded_of_exterior_contact hUQ
      isPreconnected_compl_unitSquare not_isBounded_compl_unitSquare
      (d.jordan 0).isConnected_interior.isPreconnected (d.jordan 0).closure_interior
      hdis h.bottom_left
      (by rintro (hx | hx)
          · exact h.middle_cornerless 2 (Or.inl rfl) 0 hx
          · exact h.middle_cornerless 3 (Or.inr rfl) 0 hx)
      (hexterior 0) hb
  · have htop : corner 3 ∈ d.piece 1 := by
      rw [← h.reflected]
      refine ⟨corner 0, h.bottom_left, ?_⟩
      have hzero : corner 0 = 0 := by
        apply PlaneIsometries.plane_ext <;>
          norm_num [corner, show (0 : Fin 4) ≠ 1 from by decide,
            show (0 : Fin 4) ≠ 2 from by decide,
            show (0 : Fin 4) ≠ 3 from by decide]
      change SquareSymmetry.cornerFlip 3 (corner 0) = corner 3
      rw [hzero, SquareSymmetry.cornerFlip_zero]
    exact component_unbounded_of_exterior_contact hUQ
      isPreconnected_compl_unitSquare not_isBounded_compl_unitSquare
      (d.jordan 1).isConnected_interior.isPreconnected (d.jordan 1).closure_interior
      hdis htop
      (by rintro (hx | hx)
          · exact h.middle_cornerless 2 (Or.inl rfl) 3 hx
          · exact h.middle_cornerless 3 (Or.inr rfl) 3 hx)
      (hexterior 3) hb

/-- The union of the actual two cornerless pieces has no bounded
complementary components. -/
theorem middle_union_no_holes (h : Configuration d) :
    boundedComplementComponents (d.piece 2 ∪ d.piece 3) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro H ⟨x, hx, rfl, hbounded⟩
  have hUQ : d.piece 2 ∪ d.piece 3 ⊆ unitSquare :=
    union_subset (d.piece_subset 2) (d.piece_subset 3)
  have hcover : unitSquare ⊆ (d.piece 2 ∪ d.piece 3) ∪ (d.piece 0 ∪ d.piece 1) := by
    intro y hy
    obtain ⟨i, hi⟩ := d.exists_piece_mem hy
    fin_cases i
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
  rcases bounded_component_meets_interiors
      ((d.jordan 2).isClosed.union (d.jordan 3).isClosed) hUQ
      isPreconnected_compl_unitSquare not_isBounded_compl_unitSquare hcover
      (d.jordan 0).isClosed hx hbounded with ⟨b, hbcomp, hb⟩ | ⟨b, hbcomp, hb⟩
  · apply h.outer_component_unbounded (Or.inl rfl) hb
    rwa [← connectedComponentIn_eq hbcomp]
  · apply h.outer_component_unbounded (Or.inr rfl) hb
    rwa [← connectedComponentIn_eq hbcomp]

/-- The complement of the actual middle union is connected. -/
theorem middle_union_isConnected_compl (h : Configuration d) :
    IsConnected (d.piece 2 ∪ d.piece 3)ᶜ :=
  isConnected_compl_of_no_bounded_square_components
    (union_subset (d.piece_subset 2) (d.piece_subset 3)) h.middle_union_no_holes

end Puzzling139335.N4OuterPair.Configuration
