/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwaySelectedCut
import ErdosProblems.Erdos599.HalfwayMacroContactOwnership
import ErdosProblems.Erdos599.GenericSimultaneousSwitchRank

/-!
# Retaining a contact-segmented transaction

The literal closure order in Section 9 can make an assigned alternating
route meet the closed set more than twice.  `ContactSegmentedAssignment`
therefore retains all consecutive contact blocks.  Once the closed blocks
have been realized in the forward direction, its transaction geometry gives
one honest relation: the realized closed edges together with the compressed
outside pieces.

This file performs the two generic conversions needed downstream.  First it
derives graph containment and the canonical well-founded orientation of that
literal relation; no rank is supplied as an assumption.  Second it observes
that a genuinely closed, single global club transaction can be repeated over
the actual successor-cardinal ladder stages.  This produces the exact
`SuccessorClubStageRun` consumed by the final scheduler while retaining the
transaction's `ClubStageUnionData` at every stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y closureFamily : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

namespace ContactSegmentation

variable {Q : AltPath Gamma.graph}

/-- Every recorded contact is a vertex of the original assigned route. -/
theorem contactSet_subset_vertexSet
    (T : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) :
    T.contactSet ⊆ Q.vertexSet := by
  intro x hx
  cases T with
  | finite T =>
      rcases hx with ⟨i, rfl⟩
      rw [T.vertexSet_exact]
      exact Or.inl ⟨i, rfl⟩
  | eventuallyOutside T =>
      rcases hx with ⟨i, rfl⟩
      rw [T.vertexSet_exact]
      exact Or.inl (Or.inl ⟨i, rfl⟩)
  | omega T =>
      rcases hx with ⟨i, rfl⟩
      rw [T.vertexSet_exact]
      exact Or.inl ⟨i, rfl⟩

/-- A recorded contact outside the closing set is an exposed endpoint of
the original route.  All other recorded points are certified internal
contacts. -/
theorem outside_contact_eq_initial_or_terminal
    (T : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) {x : V} (hx : x ∈ T.contactSet) (hxX : x ∉ X) :
    x = Q.initial ∨ Q.terminal? = some x := by
  cases T with
  | finite T =>
      rcases hx with ⟨i, rfl⟩
      by_cases hi0 : i.1 = 0
      · left
        have hi : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi0
        subst i
        exact T.initial_eq
      · have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi0
        by_cases hilast : i.1 = T.count
        · right
          have hi : i = ⟨T.count, Nat.lt_succ_self _⟩ := Fin.ext hilast
          subst i
          exact T.terminal_eq
        · have hilt : i.1 < T.count := by omega
          exact False.elim (hxX (T.internal_contact i hipos hilt))
  | eventuallyOutside T =>
      rcases hx with ⟨i, rfl⟩
      by_cases hi0 : i.1 = 0
      · left
        have hi : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi0
        subst i
        exact T.initial_eq
      · exact False.elim (hxX (T.internal_contact i (Nat.pos_of_ne_zero hi0)))
  | omega T =>
      rcases hx with ⟨i, rfl⟩
      cases i with
      | zero => exact Or.inl T.initial_eq
      | succ i => exact False.elim (hxX (T.later_contact i))

/-- Traversal index of a recorded contact.  Injectivity of `point` makes
`invFun` an actual inverse on every contact which occurs in the compressed
relation. -/
noncomputable def contactRank
    (T : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) : V → Nat :=
  match T with
  | .finite S => fun x ↦ (Function.invFun S.point x).1
  | .eventuallyOutside S => fun x ↦ (Function.invFun S.point x).1
  | .omega S => Function.invFun S.point

/-- Every compressed outside interval advances exactly one step in the
contact order. -/
theorem contactRank_lt_of_mem_compressedOutsideEdges
    (T : ContactSegmentation (Y := Y) Q X before innerRoof outerRoof
      closureFamily) {x y : V}
    (hxy : (x, y) ∈ T.compressedOutsideEdges) :
    T.contactRank x < T.contactRank y := by
  cases T with
  | finite S =>
      rcases hxy with ⟨i, P, _hi, hpair⟩
      have hx : x = S.point i.castSucc := congrArg Prod.fst hpair
      have hy : y = S.point i.succ := congrArg Prod.snd hpair
      subst x
      subst y
      change
        (Function.invFun S.point (S.point i.castSucc)).1 <
          (Function.invFun S.point (S.point i.succ)).1
      rw [Function.leftInverse_invFun S.point_injective,
        Function.leftInverse_invFun S.point_injective]
      exact Fin.castSucc_lt_succ
  | eventuallyOutside S =>
      rcases hxy with ⟨i, P, _hi, hpair⟩
      have hx : x = S.point i.castSucc := congrArg Prod.fst hpair
      have hy : y = S.point i.succ := congrArg Prod.snd hpair
      subst x
      subst y
      change
        (Function.invFun S.point (S.point i.castSucc)).1 <
          (Function.invFun S.point (S.point i.succ)).1
      rw [Function.leftInverse_invFun S.point_injective,
        Function.leftInverse_invFun S.point_injective]
      exact Fin.castSucc_lt_succ
  | omega S =>
      rcases hxy with ⟨i, P, _hi, hpair⟩
      have hx : x = S.point i := congrArg Prod.fst hpair
      have hy : y = S.point (i + 1) := congrArg Prod.snd hpair
      subst x
      subst y
      change
        Function.invFun S.point (S.point i) <
          Function.invFun S.point (S.point (i + 1))
      rw [Function.leftInverse_invFun S.point_injective,
        Function.leftInverse_invFun S.point_injective]
      omega

end ContactSegmentation

namespace ContactSegmentedAssignment

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}

/-- The unique selected route owning a recorded contact, when there is one.
The option-valued definition also works when the assignment domain is empty. -/
noncomputable def contactOwner
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) (x : V) : Option {z : V //
        z ∈ Gamma.initialSet Z \ Gamma.initialSet Y} := by
  classical
  exact if h : ∃ s, x ∈ (S.segmentation s).contactSet then
    some (Classical.choose h)
  else none

/-- A contact can have only one owner. -/
theorem contactOwner_eq_some_of_mem
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily)
    (s : {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y})
    {x : V} (hx : x ∈ (S.segmentation s).contactSet) :
    S.contactOwner x = some s := by
  classical
  unfold contactOwner
  split
  next h =>
    apply congrArg some
    by_contra hne
    have hst : s ≠ Classical.choose h := fun heq ↦ hne heq.symm
    exact Set.disjoint_left.1
      (S.contacts_pairwiseDisjoint s (Classical.choose h) hst) hx
      (Classical.choose_spec h)
  next h => exact False.elim (h ⟨s, hx⟩)

/-- The family rank is the local traversal index on the uniquely owned
contact set and zero away from all recorded contacts. -/
noncomputable def contactRank
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) (x : V) : Nat :=
  match S.contactOwner x with
  | none => 0
  | some s => (S.segmentation s).contactRank x

/-- The union of all compressed outside pieces strictly increases the
assembled family rank. -/
theorem contactRank_lt_of_mem_compressedOutsideEdges
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) {x y : V}
    (hxy : (x, y) ∈ S.compressedOutsideEdges) :
    S.contactRank x < S.contactRank y := by
  simp only [ContactSegmentedAssignment.compressedOutsideEdges,
    Set.mem_iUnion] at hxy
  obtain ⟨s, hxy⟩ := hxy
  have hx :=
    (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
      hxy |>.1
  have hy :=
    (S.segmentation s).endpoints_mem_contactSet_of_mem_compressedOutsideEdges
      hxy |>.2
  simp only [contactRank, S.contactOwner_eq_some_of_mem s hx,
    S.contactOwner_eq_some_of_mem s hy]
  exact (S.segmentation s).contactRank_lt_of_mem_compressedOutsideEdges hxy

/-- The compressed outside relation has no directed cycle. -/
theorem compressedOutsideEdges_acyclic
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) :
    ¬ ContainsDirectedCycle S.compressedOutsideEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsDirectedCycle_of_wellFoundedRank
    S.compressedOutsideEdges S.contactRank
    S.contactRank_lt_of_mem_compressedOutsideEdges

/-- The compressed outside relation has no reverse ray. -/
theorem compressedOutsideEdges_no_reverse_ray
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) :
    ¬ ContainsReverseDirectedRay S.compressedOutsideEdges :=
  Alternating.GenericSimultaneousSwitch.not_containsReverseDirectedRay_of_wellFoundedRank
    S.compressedOutsideEdges S.contactRank
    S.contactRank_lt_of_mem_compressedOutsideEdges

/-- The switching-only contact transaction.  Backward closed blocks are
deleted, exactly as in safe switching; any already oriented inside relation
can be added later by the global splice compiler. -/
noncomputable def compressedTransactionGeometry
    (S : ContactSegmentedAssignment A X before innerRoof outerRoof
      closureFamily) : S.TransactionGeometry where
  closedEdges := ∅
  closedEdges_in_graph := by simp
  biunique := by
    simpa using S.compressedOutsideEdges_biUnique
  acyclic := by
    simpa using S.compressedOutsideEdges_acyclic
  no_reverse_ray := by
    simpa using S.compressedOutsideEdges_no_reverse_ray

end ContactSegmentedAssignment

namespace MacroOwnedBracketSimultaneousAssignment

variable {Z : Set Gamma.DPath}

/-- Root equality is the same as equality of the corresponding uncovered
sources. -/
private theorem source_eq_of_root_eq
    {s t :
      {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y}}
    (h : initialPath Z ⟨s.1, s.property.1⟩ =
      initialPath Z ⟨t.1, t.property.1⟩) : s = t := by
  apply Subtype.ext
  calc
    s.1 = (initialPath Z ⟨s.1, s.property.1⟩).1.initial :=
      (initialPath_initial Z ⟨s.1, s.property.1⟩).symm
    _ = (initialPath Z ⟨t.1, t.property.1⟩).1.initial :=
      congrArg (fun p : Z ↦ p.1.initial) h
    _ = t.1 := initialPath_initial Z ⟨t.1, t.property.1⟩

/-- Local macro-orbit provenance constructs, rather than assumes, the
cross-source contact disjointness required by the contact transaction.

Contacts in `X` use `macroOrbit_roots_eq_of_cut_contact`.  A contact outside
`X` is an exposed route endpoint: initial/initial and terminal/terminal
collisions are ruled out by source and terminal injectivity, while a mixed
collision identifies the two forward macro orbits. -/
def toContactSegmentedAssignment
    (M : MacroOwnedBracketSimultaneousAssignment Z Y)
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hboundary : BoundaryAligned Z Y)
    (hcut : CutEndpointPure Z X)
    (segmentation : ∀ s,
      ContactSegmentation (Y := Y) (M.assigned s) X before innerRoof
        outerRoof closureFamily) :
    ContactSegmentedAssignment M.toSimultaneousAssignment X before
      innerRoof outerRoof closureFamily where
  segmentation := segmentation
  contacts_pairwiseDisjoint := by
    intro s t hst
    rw [Set.disjoint_left]
    intro x hxs hxt
    have hrootOutside : ∀ z :
        {z : V // z ∈ Gamma.initialSet Z \ Gamma.initialSet Y},
        (initialPath Z ⟨z.1, z.property.1⟩).1.initial ∉
          Gamma.vertexSet Y := by
      intro z
      rw [initialPath_initial]
      exact hboundary.initial_outside z.property
    have hxsQ := (segmentation s).contactSet_subset_vertexSet hxs
    have hxtQ := (segmentation t).contactSet_subset_vertexSet hxt
    by_cases hxX : x ∈ X
    · obtain ⟨q, hq, hxq⟩ := M.vertex_owner s x hxsQ
      obtain ⟨r, hr, hxr⟩ := M.vertex_owner t x hxtQ
      apply hst
      apply source_eq_of_root_eq
      exact macroOrbit_roots_eq_of_cut_contact hZ hY hboundary hcut
        (hrootOutside s) (hrootOutside t) hq hr hxq hxr hxX
    · have hsEnd := (segmentation s).outside_contact_eq_initial_or_terminal
        hxs hxX
      have htEnd := (segmentation t).outside_contact_eq_initial_or_terminal
        hxt hxX
      rcases hsEnd with hsInitial | hsTerminal <;>
          rcases htEnd with htInitial | htTerminal
      · apply hst
        apply Subtype.ext
        calc
          s.1 = (M.assigned s).initial := (M.starts_at s).symm
          _ = x := hsInitial.symm
          _ = (M.assigned t).initial := htInitial
          _ = t.1 := M.starts_at t
      · obtain ⟨⟨q, hq, hqterm⟩, _hxY⟩ :=
          M.finite_terminal_orbit t x htTerminal
        let p : Z := initialPath Z ⟨s.1, s.property.1⟩
        have hpx : x ∈ p.1.support := by
          have hpinitial : p.1.initial = x := by
            calc
              p.1.initial = s.1 := initialPath_initial Z ⟨s.1, s.property.1⟩
              _ = (M.assigned s).initial := (M.starts_at s).symm
              _ = x := hsInitial.symm
          exact hpinitial ▸ p.1.initial_mem_support
        apply hst
        apply source_eq_of_root_eq
        exact macroOrbit_roots_eq_of_common_forward hZ hY
          (hrootOutside s) (hrootOutside t)
          (mem_macroOrbit_root Z Y p) hq hpx
          (Gamma.terminal_mem_support hqterm)
      · obtain ⟨⟨q, hq, hqterm⟩, _hxY⟩ :=
          M.finite_terminal_orbit s x hsTerminal
        let p : Z := initialPath Z ⟨t.1, t.property.1⟩
        have hpx : x ∈ p.1.support := by
          have hpinitial : p.1.initial = x := by
            calc
              p.1.initial = t.1 := initialPath_initial Z ⟨t.1, t.property.1⟩
              _ = (M.assigned t).initial := (M.starts_at t).symm
              _ = x := htInitial.symm
          exact hpinitial ▸ p.1.initial_mem_support
        apply hst
        apply source_eq_of_root_eq
        exact (macroOrbit_roots_eq_of_common_forward hZ hY
          (hrootOutside t) (hrootOutside s)
          (mem_macroOrbit_root Z Y p) hq hpx
          (Gamma.terminal_mem_support hqterm)).symm
      · exact hst (M.finite_terminals_injective hsTerminal htTerminal)

end MacroOwnedBracketSimultaneousAssignment

namespace ContactSegmentedAssignment.TransactionGeometry

variable {Z : Set Gamma.DPath} {A : SimultaneousAssignment Z Y}
variable {S : ContactSegmentedAssignment A X before innerRoof outerRoof
  closureFamily}

/-- The literal relation retained by a contact-segmented transaction. -/
def edge (G : S.TransactionGeometry) : Set (V × V) :=
  G.closedEdges ∪ S.compressedOutsideEdges

/-- Both the realized closed blocks and the compressed outside pieces are
edges of the imaginary graph. -/
theorem edge_subset_imaginaryGraph (G : S.TransactionGeometry)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa) :
    G.edge ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  rintro e (he | he)
  · exact Or.inl (G.closedEdges_in_graph he)
  · exact S.compressedOutsideEdges_subset_imaginaryGraph hclosed he

/-- Absence of directed cycles and reverse rays constructs the predecessor
well-foundedness of the retained relation. -/
theorem predecessorWellFounded (G : S.TransactionGeometry) :
    WellFounded (fun x y : V ↦ (x, y) ∈ G.edge) :=
  ForwardOrientation.predecessor_wellFounded G.edge G.acyclic G.no_reverse_ray

/-- The canonical natural-number rank of the retained relation. -/
def rank (G : S.TransactionGeometry) : V → Nat :=
  ForwardOrientation.wellFoundedDepth G.edge G.predecessorWellFounded

/-- Every retained edge strictly increases the constructed rank. -/
theorem rank_lt_of_mem_edge (G : S.TransactionGeometry) {x y : V}
    (hxy : (x, y) ∈ G.edge) : G.rank x < G.rank y := by
  have hstep := ForwardOrientation.wellFoundedDepth_step G.edge G.biunique
    G.predecessorWellFounded hxy
  change ForwardOrientation.wellFoundedDepth G.edge G.predecessorWellFounded x <
    ForwardOrientation.wellFoundedDepth G.edge G.predecessorWellFounded y
  omega

/-- The contact relation has an honest forward orientation on any retained
carrier containing all of its endpoints. -/
theorem exists_forwardOrientation (G : S.TransactionGeometry)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (carrier : Set V)
    (hendpoints : ∀ e ∈ G.edge, e.1 ∈ carrier ∧ e.2 ∈ carrier) :
    ∃ O : ForwardOrientation (imaginaryGraph Gamma Y kappa), O.edge = G.edge :=
  ForwardOrientation.exists_forwardOrientation G.edge carrier
    (G.edge_subset_imaginaryGraph hclosed) hendpoints G.biunique G.acyclic
      G.no_reverse_ray

end ContactSegmentedAssignment.TransactionGeometry

end LinkageBlueprint
end Blueprint
end Erdos599
