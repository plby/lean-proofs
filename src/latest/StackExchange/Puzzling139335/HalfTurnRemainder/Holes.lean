import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.Components
import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.SquareExterior
import StackExchange.Puzzling139335.HalfTurnRemainder.Holes.HalfTurnTransport
import StackExchange.Puzzling139335.JordanRegion
import Mathlib.Data.Set.Card

/-!
# The possible holes in a two-piece square remainder

The retained closed set `U` and two Jordan regions `B`, `C` cover the square.
Their omitted interiors are disjoint from `U`.  Every bounded component of the
complement of `U` is one of the two components containing those interiors.  If
two distinct bounded components exist, they are exactly `interior B` and
`interior C`.
-/

open Set Bornology

namespace Puzzling139335.HalfTurnRemainder

noncomputable section

/-- Every bounded component of the complement of a subset of the square stays
inside the square. -/
theorem bounded_component_subset_unitSquare {U : Set Plane} {x : Plane}
    (hUQ : U ⊆ unitSquare) (hbounded : IsBounded (connectedComponentIn Uᶜ x)) :
    connectedComponentIn Uᶜ x ⊆ unitSquare :=
  bounded_component_subset hUQ isPreconnected_compl_unitSquare
    not_isBounded_compl_unitSquare hbounded

/-- Every actual hole meets one of the omitted interiors. -/
theorem bounded_component_meets_interiors_in_square {U B C : Set Plane} {x : Plane}
    (hU : IsClosed U) (hUQ : U ⊆ unitSquare)
    (hcover : unitSquare ⊆ U ∪ (B ∪ C)) (hB : IsClosed B) (hx : x ∉ U)
    (hbounded : IsBounded (connectedComponentIn Uᶜ x)) :
    (connectedComponentIn Uᶜ x ∩ interior B).Nonempty ∨
      (connectedComponentIn Uᶜ x ∩ interior C).Nonempty :=
  bounded_component_meets_interiors hU hUQ isPreconnected_compl_unitSquare
    not_isBounded_compl_unitSquare hcover hB hx hbounded

/-- The holes lie in the explicit pair of components containing the interiors
of the omitted Jordan regions. -/
theorem boundedComplementComponents_subset_pair_in_square
    {U B C : Set Plane} {b c : Plane}
    (hU : IsClosed U) (hUQ : U ⊆ unitSquare)
    (hcover : unitSquare ⊆ U ∪ (B ∪ C)) (hB : IsJordanRegion B) (hC : IsJordanRegion C)
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hb : b ∈ interior B) (hc : c ∈ interior C) :
    boundedComplementComponents U ⊆
      {connectedComponentIn Uᶜ b, connectedComponentIn Uᶜ c} :=
  boundedComplementComponents_subset_pair hU hUQ isPreconnected_compl_unitSquare
    not_isBounded_compl_unitSquare hcover hB.isClosed
    hB.isConnected_interior.isPreconnected hC.isConnected_interior.isPreconnected
    hBU hCU hb hc

/-- There are at most two actual nonempty bounded complementary components. -/
theorem boundedComplementComponents_encard_le_two
    {U B C : Set Plane} (hU : IsClosed U) (hUQ : U ⊆ unitSquare)
    (hcover : unitSquare ⊆ U ∪ (B ∪ C)) (hB : IsJordanRegion B) (hC : IsJordanRegion C)
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U) :
    (boundedComplementComponents U).encard ≤ 2 := by
  obtain ⟨b, hb⟩ := hB.interior_nonempty
  obtain ⟨c, hc⟩ := hC.interior_nonempty
  have hsub := boundedComplementComponents_subset_pair_in_square
    hU hUQ hcover hB hC hBU hCU hb hc
  calc
    (boundedComplementComponents U).encard ≤
        ({connectedComponentIn Uᶜ b, connectedComponentIn Uᶜ c} : Set (Set Plane)).encard :=
      Set.encard_mono hsub
    _ ≤ ({connectedComponentIn Uᶜ c} : Set (Set Plane)).encard + 1 :=
      Set.encard_insert_le _ _
    _ = 2 := by norm_num

/-- If the two interior components are distinct and bounded, they are exactly
the two omitted interiors. -/
theorem two_bounded_components_eq_interiors_in_square
    {U B C : Set Plane} {b c : Plane}
    (hU : IsClosed U) (hUQ : U ⊆ unitSquare)
    (hcover : unitSquare ⊆ U ∪ (B ∪ C)) (hB : IsJordanRegion B) (hC : IsJordanRegion C)
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hb : b ∈ interior B) (hc : c ∈ interior C)
    (hne : connectedComponentIn Uᶜ b ≠ connectedComponentIn Uᶜ c)
    (hbbounded : IsBounded (connectedComponentIn Uᶜ b))
    (hcbounded : IsBounded (connectedComponentIn Uᶜ c)) :
    connectedComponentIn Uᶜ b = interior B ∧ connectedComponentIn Uᶜ c = interior C :=
  two_distinct_bounded_components_eq_interiors hU hUQ isPreconnected_compl_unitSquare
    not_isBounded_compl_unitSquare hcover
    hB.isConnected_interior.isPreconnected hC.isConnected_interior.isPreconnected
    hBU hCU hB.closure_interior hC.closure_interior hb hc hne hbbounded hcbounded

/-- Any two distinct actual holes force the complete hole set to consist of
the two omitted interiors; in particular no additional boundary points belong
to either hole. -/
theorem boundedComplementComponents_eq_interiors_of_two
    {U B C : Set Plane} {x y : Plane}
    (hU : IsClosed U) (hUQ : U ⊆ unitSquare)
    (hcover : unitSquare ⊆ U ∪ (B ∪ C)) (hB : IsJordanRegion B) (hC : IsJordanRegion C)
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hx : x ∉ U) (hy : y ∉ U)
    (hxbounded : IsBounded (connectedComponentIn Uᶜ x))
    (hybounded : IsBounded (connectedComponentIn Uᶜ y))
    (hxy : connectedComponentIn Uᶜ x ≠ connectedComponentIn Uᶜ y) :
    boundedComplementComponents U = {interior B, interior C} ∧ interior B ≠ interior C := by
  obtain ⟨b, hb⟩ := hB.interior_nonempty
  obtain ⟨c, hc⟩ := hC.interior_nonempty
  have hclass {z : Plane} (hz : z ∉ U)
      (hzb : IsBounded (connectedComponentIn Uᶜ z)) :
      connectedComponentIn Uᶜ z = connectedComponentIn Uᶜ b ∨
        connectedComponentIn Uᶜ z = connectedComponentIn Uᶜ c :=
    bounded_component_eq_one_of_two hU hUQ isPreconnected_compl_unitSquare
      not_isBounded_compl_unitSquare hcover hB.isClosed
      hB.isConnected_interior.isPreconnected hC.isConnected_interior.isPreconnected
      hBU hCU hb hc hz hzb
  have hxclass := hclass hx hxbounded
  have hyclass := hclass hy hybounded
  have hne : connectedComponentIn Uᶜ b ≠ connectedComponentIn Uᶜ c := by
    intro hbc
    have hxb : connectedComponentIn Uᶜ x = connectedComponentIn Uᶜ b :=
      hxclass.elim id (fun hxc => hxc.trans hbc.symm)
    have hyb : connectedComponentIn Uᶜ y = connectedComponentIn Uᶜ b :=
      hyclass.elim id (fun hyc => hyc.trans hbc.symm)
    exact hxy (hxb.trans hyb.symm)
  have hbbounded : IsBounded (connectedComponentIn Uᶜ b) := by
    rcases hxclass with hxb | hxc
    · exact hxb ▸ hxbounded
    · have hyb : connectedComponentIn Uᶜ y = connectedComponentIn Uᶜ b :=
        hyclass.resolve_right (fun hyc => hxy (hxc.trans hyc.symm))
      exact hyb ▸ hybounded
  have hcbounded : IsBounded (connectedComponentIn Uᶜ c) := by
    rcases hxclass with hxb | hxc
    · have hyc : connectedComponentIn Uᶜ y = connectedComponentIn Uᶜ c :=
        hyclass.resolve_left (fun hyb => hxy (hxb.trans hyb.symm))
      exact hyc ▸ hybounded
    · exact hxc ▸ hxbounded
  obtain ⟨hbcomp, hccomp⟩ := two_bounded_components_eq_interiors_in_square
    hU hUQ hcover hB hC hBU hCU hb hc hne hbbounded hcbounded
  have hsub : boundedComplementComponents U ⊆ {interior B, interior C} := by
    simpa only [hbcomp, hccomp] using
      boundedComplementComponents_subset_pair_in_square hU hUQ hcover hB hC hBU hCU hb hc
  have hBhole : interior B ∈ boundedComplementComponents U :=
    ⟨b, Set.disjoint_left.mp hBU hb, hbcomp.symm, hB.isBounded.subset interior_subset⟩
  have hChole : interior C ∈ boundedComplementComponents U :=
    ⟨c, Set.disjoint_left.mp hCU hc, hccomp.symm, hC.isBounded.subset interior_subset⟩
  refine ⟨hsub.antisymm (pair_subset hBhole hChole), ?_⟩
  simpa only [hbcomp, hccomp] using hne

/-- In a centrally symmetric connected remainder containing its center, one
actual hole forces two distinct holes, namely the two omitted interiors. -/
theorem boundedComplementComponents_eq_interiors_of_pointReflection
    {U B C : Set Plane} {o x : Plane}
    (hU : IsClosed U) (hUQ : U ⊆ unitSquare)
    (hcover : unitSquare ⊆ U ∪ (B ∪ C)) (hB : IsJordanRegion B) (hC : IsJordanRegion C)
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hUconn : IsConnected U) (hoU : o ∈ U)
    (hsym : AffineIsometryEquiv.pointReflection ℝ o '' U = U)
    (hx : x ∉ U) (hbounded : IsBounded (connectedComponentIn Uᶜ x)) :
    boundedComplementComponents U = {interior B, interior C} ∧ interior B ≠ interior C := by
  obtain ⟨y, hy, hybounded, hxy⟩ :=
    exists_distinct_bounded_component_of_pointReflection hU hUconn hoU hsym hx hbounded
  exact boundedComplementComponents_eq_interiors_of_two hU hUQ hcover hB hC hBU hCU
    hx hy hbounded hybounded hxy

/-- The exact alternative needed for the half-turn remainder: there are no
bounded complementary components, or there are precisely the two omitted
interiors.  No Jordan-boundary property of the remainder is assumed. -/
theorem boundedComplementComponents_empty_or_eq_interiors_of_pointReflection
    {U B C : Set Plane} {o : Plane}
    (hU : IsClosed U) (hUQ : U ⊆ unitSquare)
    (hcover : unitSquare ⊆ U ∪ (B ∪ C)) (hB : IsJordanRegion B) (hC : IsJordanRegion C)
    (hBU : Disjoint (interior B) U) (hCU : Disjoint (interior C) U)
    (hUconn : IsConnected U) (hoU : o ∈ U)
    (hsym : AffineIsometryEquiv.pointReflection ℝ o '' U = U) :
    boundedComplementComponents U = ∅ ∨
      boundedComplementComponents U = {interior B, interior C} := by
  classical
  by_cases hempty : boundedComplementComponents U = ∅
  · exact Or.inl hempty
  · obtain ⟨H, x, hx, hH, hbounded⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hcomponentBounded : IsBounded (connectedComponentIn Uᶜ x) := hH ▸ hbounded
    exact Or.inr (boundedComplementComponents_eq_interiors_of_pointReflection
      hU hUQ hcover hB hC hBU hCU hUconn hoU hsym hx hcomponentBounded).1

end

end Puzzling139335.HalfTurnRemainder
