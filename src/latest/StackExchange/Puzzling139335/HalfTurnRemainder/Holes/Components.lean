import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Bornology.Basic
import Mathlib.Tactic

/-!
# Actual bounded complementary components of a two-piece remainder

The statements use `connectedComponentIn` directly.  A connected unbounded
exterior forces every bounded complementary component inside the carrier.
If the missing part of that carrier is covered by two closed pieces, each
nonempty open component meets one of their interiors.  Connected interiors then
give at most two components.  When these two components are distinct, regular
closedness identifies them with the interiors themselves.
-/

open Set Bornology

namespace Puzzling139335.HalfTurnRemainder

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- Two distinct relative connected components are disjoint. -/
theorem component_disjoint_of_ne {F : Set X} {x y : X}
    (hne : connectedComponentIn F x ≠ connectedComponentIn F y) :
    Disjoint (connectedComponentIn F x) (connectedComponentIn F y) := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  exact hne ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm)

/-- A nonempty open set covered by two pieces, the first closed, meets the
interior of at least one of them. -/
theorem open_subset_union_meets_interiors {V B C : Set X}
    (hV : IsOpen V) (hVne : V.Nonempty) (hB : IsClosed B) (hcover : V ⊆ B ∪ C) :
    (V ∩ interior B).Nonempty ∨ (V ∩ interior C).Nonempty := by
  classical
  by_cases hVB : V ⊆ B
  · obtain ⟨v, hv⟩ := hVne
    exact Or.inl ⟨v, hv, interior_maximal hVB hV hv⟩
  · obtain ⟨v, hv, hvB⟩ := Set.not_subset.mp hVB
    have hsub : V ∩ Bᶜ ⊆ C := by
      rintro x ⟨hx, hxB⟩
      exact (hcover hx).resolve_left hxB
    exact Or.inr ⟨v, hv,
      interior_maximal hsub (hV.inter hB.isOpen_compl) ⟨hv, hvB⟩⟩

/-- A connected interior disjoint from the retained set lies in the component
of any one of its own points. -/
theorem interior_subset_component {U B : Set X} {b : X}
    (hB : IsPreconnected (interior B)) (hBU : Disjoint (interior B) U)
    (hb : b ∈ interior B) : interior B ⊆ connectedComponentIn Uᶜ b := by
  apply hB.subset_connectedComponentIn hb
  intro x hx
  exact Set.disjoint_left.mp hBU hx

section Bornology

variable [Bornology X]

/-- A bounded component cannot touch a connected unbounded exterior of a
carrier containing the retained set. -/
theorem bounded_component_subset {U Q : Set X} {x : X}
    (hUQ : U ⊆ Q) (hQconn : IsPreconnected Qᶜ)
    (hQunbounded : ¬ IsBounded Qᶜ)
    (hbounded : IsBounded (connectedComponentIn Uᶜ x)) :
    connectedComponentIn Uᶜ x ⊆ Q := by
  intro y hy
  by_contra hyQ
  have hext : Qᶜ ⊆ connectedComponentIn Uᶜ y :=
    hQconn.subset_connectedComponentIn hyQ (compl_subset_compl.mpr hUQ)
  rw [← connectedComponentIn_eq hy] at hext
  exact hQunbounded (hbounded.subset hext)

/-- The actual bounded component is covered by the two omitted pieces. -/
theorem bounded_component_subset_union {U Q B C : Set X} {x : X}
    (hUQ : U ⊆ Q) (hQconn : IsPreconnected Qᶜ)
    (hQunbounded : ¬ IsBounded Qᶜ) (hcover : Q ⊆ U ∪ (B ∪ C))
    (hbounded : IsBounded (connectedComponentIn Uᶜ x)) :
    connectedComponentIn Uᶜ x ⊆ B ∪ C := by
  intro y hy
  have hyQ := bounded_component_subset hUQ hQconn hQunbounded hbounded hy
  exact (hcover hyQ).resolve_left (connectedComponentIn_subset Uᶜ x hy)

section LocallyConnected

variable [LocallyConnectedSpace X]

/-- Every actual bounded complementary component meets one of the two omitted
interiors.  No smoothness or boundary-measure assumption is used. -/
theorem bounded_component_meets_interiors {U Q B C : Set X} {x : X}
    (hU : IsClosed U) (hUQ : U ⊆ Q) (hQconn : IsPreconnected Qᶜ)
    (hQunbounded : ¬ IsBounded Qᶜ) (hcover : Q ⊆ U ∪ (B ∪ C))
    (hB : IsClosed B) (hx : x ∈ Uᶜ)
    (hbounded : IsBounded (connectedComponentIn Uᶜ x)) :
    (connectedComponentIn Uᶜ x ∩ interior B).Nonempty ∨
      (connectedComponentIn Uᶜ x ∩ interior C).Nonempty :=
  open_subset_union_meets_interiors hU.isOpen_compl.connectedComponentIn
    ⟨x, mem_connectedComponentIn hx⟩ hB
    (bounded_component_subset_union hUQ hQconn hQunbounded hcover hbounded)

/-- Choosing one point in each connected omitted interior gives two explicit
components, and every bounded complementary component is one of those two. -/
theorem bounded_component_eq_one_of_two {U Q B C : Set X} {x b c : X}
    (hU : IsClosed U) (hUQ : U ⊆ Q) (hQconn : IsPreconnected Qᶜ)
    (hQunbounded : ¬ IsBounded Qᶜ) (hcover : Q ⊆ U ∪ (B ∪ C))
    (hBclosed : IsClosed B)
    (hBconn : IsPreconnected (interior B)) (hCconn : IsPreconnected (interior C))
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hb : b ∈ interior B) (hc : c ∈ interior C) (hx : x ∈ Uᶜ)
    (hbounded : IsBounded (connectedComponentIn Uᶜ x)) :
    connectedComponentIn Uᶜ x = connectedComponentIn Uᶜ b ∨
      connectedComponentIn Uᶜ x = connectedComponentIn Uᶜ c := by
  have hBs := interior_subset_component hBconn hBU hb
  have hCs := interior_subset_component hCconn hCU hc
  rcases bounded_component_meets_interiors hU hUQ hQconn hQunbounded hcover
      hBclosed hx hbounded with ⟨z, hz, hzB⟩ | ⟨z, hz, hzC⟩
  · exact Or.inl ((connectedComponentIn_eq hz).trans
      (connectedComponentIn_eq (hBs hzB)).symm)
  · exact Or.inr ((connectedComponentIn_eq hz).trans
      (connectedComponentIn_eq (hCs hzC)).symm)

/-- The set of actual nonempty bounded complementary components. -/
def boundedComplementComponents (U : Set X) : Set (Set X) :=
  {H | ∃ x ∈ Uᶜ, H = connectedComponentIn Uᶜ x ∧ IsBounded H}

/-- In particular, the set of holes is contained in an explicit two-element
set of actual connected components. -/
theorem boundedComplementComponents_subset_pair {U Q B C : Set X} {b c : X}
    (hU : IsClosed U) (hUQ : U ⊆ Q) (hQconn : IsPreconnected Qᶜ)
    (hQunbounded : ¬ IsBounded Qᶜ) (hcover : Q ⊆ U ∪ (B ∪ C))
    (hBclosed : IsClosed B)
    (hBconn : IsPreconnected (interior B)) (hCconn : IsPreconnected (interior C))
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hb : b ∈ interior B) (hc : c ∈ interior C) :
    boundedComplementComponents U ⊆
      {connectedComponentIn Uᶜ b, connectedComponentIn Uᶜ c} := by
  rintro H ⟨x, hx, rfl, hbounded⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
    bounded_component_eq_one_of_two hU hUQ hQconn hQunbounded hcover
      hBclosed hBconn hCconn hBU hCU hb hc hx hbounded

end LocallyConnected

end Bornology

section LocallyConnected

variable [LocallyConnectedSpace X]

/-- If two omitted interiors lie in distinct components, an open component
covered by the two closed pieces is exactly its own interior.  Regular
closedness excludes boundary points of the other piece. -/
theorem component_eq_interior_of_distinct {U B C : Set X} {b c : X}
    (hU : IsClosed U) (hcover : connectedComponentIn Uᶜ b ⊆ B ∪ C)
    (hBs : interior B ⊆ connectedComponentIn Uᶜ b)
    (hCs : interior C ⊆ connectedComponentIn Uᶜ c)
    (hCregular : closure (interior C) = C)
    (hne : connectedComponentIn Uᶜ b ≠ connectedComponentIn Uᶜ c) :
    connectedComponentIn Uᶜ b = interior B := by
  have hopen : IsOpen (connectedComponentIn Uᶜ b) :=
    hU.isOpen_compl.connectedComponentIn
  have hdisint : Disjoint (connectedComponentIn Uᶜ b) (interior C) :=
    (component_disjoint_of_ne hne).mono_right hCs
  have hdis : Disjoint (connectedComponentIn Uᶜ b) C := by
    rw [← hCregular]
    exact hdisint.closure_right hopen
  have hsub : connectedComponentIn Uᶜ b ⊆ B := by
    intro x hx
    exact (hcover hx).resolve_right (Set.disjoint_left.mp hdis hx)
  exact (interior_maximal hsub hopen).antisymm hBs

end LocallyConnected

section BornologyLocallyConnected

variable [Bornology X] [LocallyConnectedSpace X]

/-- Two distinct bounded components containing the two connected omitted
interiors are precisely those interiors. -/
theorem two_distinct_bounded_components_eq_interiors {U Q B C : Set X} {b c : X}
    (hU : IsClosed U) (hUQ : U ⊆ Q) (hQconn : IsPreconnected Qᶜ)
    (hQunbounded : ¬ IsBounded Qᶜ) (hcover : Q ⊆ U ∪ (B ∪ C))
    (hBconn : IsPreconnected (interior B)) (hCconn : IsPreconnected (interior C))
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hBregular : closure (interior B) = B) (hCregular : closure (interior C) = C)
    (hb : b ∈ interior B) (hc : c ∈ interior C)
    (hne : connectedComponentIn Uᶜ b ≠ connectedComponentIn Uᶜ c)
    (hbbounded : IsBounded (connectedComponentIn Uᶜ b))
    (hcbounded : IsBounded (connectedComponentIn Uᶜ c)) :
    connectedComponentIn Uᶜ b = interior B ∧ connectedComponentIn Uᶜ c = interior C := by
  have hBs := interior_subset_component hBconn hBU hb
  have hCs := interior_subset_component hCconn hCU hc
  have hcoverB := bounded_component_subset_union hUQ hQconn hQunbounded hcover hbbounded
  have hcoverC : connectedComponentIn Uᶜ c ⊆ C ∪ B := by
    simpa only [union_comm] using
      bounded_component_subset_union hUQ hQconn hQunbounded hcover hcbounded
  exact ⟨component_eq_interior_of_distinct hU hcoverB hBs hCs hCregular hne,
    component_eq_interior_of_distinct hU hcoverC hCs hBs hBregular hne.symm⟩

end BornologyLocallyConnected

end

end Puzzling139335.HalfTurnRemainder
