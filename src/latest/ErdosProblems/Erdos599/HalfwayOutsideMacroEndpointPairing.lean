/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayOutsideMacroAssignment
import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceClassification
import ErdosProblems.Erdos599.FracturedWarpOfWarp
import ErdosProblems.Erdos599.SafeSwitching

/-!
# Endpoint pairing of the outside macro assignment

The outside macro construction contains an actual full-reference
simultaneous assignment whose routes avoid the constructed cut.  Its
`AssignmentClosureContext` therefore supplies the exact finite and infinite
Claim-2 witnesses required by `ClosedEndpointPairing`; no independent
endpoint-selection premise is needed.

At a club stage the local pairing can immediately be reclassified against
the limiting reference.  The output retains real forward edges at
limiting-reference exception endpoints instead of falsely asserting that
every local imaginary shortcut remains imaginary globally.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating
open Alternating.RelationDecomposition

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y W : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

namespace OutsideMacroFullAssignment

/-- Every vertex of an actual macro-owned route lies on the unique honest
outside-row member beginning at its source. -/
theorem assigned_vertexSet_subset_macroRoot
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) :
    (A.assignment.assigned s).vertexSet ⊆
      (initialPath (outsideReference W X) ⟨s.1, s.property.1⟩).1.support := by
  intro x hx
  let t := SimultaneousAssignment.toOutsideSource (X := X) s
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨t.1, t.property.1⟩
  have hx' : x ∈ (A.provenance.assigned t).vertexSet := by
    change x ∈ (A.full.assigned s).vertexSet at hx
    rw [A.full_assigned s] at hx
    exact hx
  obtain ⟨q, hqOwner, hxq⟩ := A.provenance.vertex_owner t x hx'
  change q ∈ macroOrbit (outsideReference W X)
      (outsideReference Y X) p ∨
    q ∈ macroReference (outsideReference W X)
      (outsideReference Y X) p at hqOwner
  have hZ : Gamma.IsWarp (outsideReference W X) :=
    outsideReference_isWarp hW
  have hpOutside : p.1 ∉ outsideReference Y X := by
    intro hp
    exact t.property.2 ⟨p.1, hp, initialPath_initial _ _⟩
  have hstepRoot : ¬ ∃ r : outsideReference W X,
      AssignmentMacroStep (outsideReference W X)
        (outsideReference Y X) p r := by
    rintro ⟨r, qY, v, hpterm, hqterm, _hqr⟩
    let qZ : outsideReference W X := ⟨qY.1, hsub qY.2⟩
    have hpq : p = qZ := by
      apply Subtype.ext
      exact DWeb.IsWarp.eq_of_mem_support hZ p.2 qZ.2
        (Gamma.terminal_mem_support hpterm)
        (Gamma.terminal_mem_support hqterm)
    exact hpOutside (hpq ▸ qY.2)
  have horbit : macroOrbit (outsideReference W X)
      (outsideReference Y X) p = {p.1} := by
    ext r
    constructor
    · rintro ⟨hrZ, hpr⟩
      rcases Relation.ReflTransGen.cases_head hpr with h | ⟨q, hpq, _⟩
      · simpa only [Set.mem_singleton_iff] using
          (congrArg Subtype.val h).symm
      · exact False.elim (hstepRoot ⟨q, hpq⟩)
    · intro hr
      have hrp : r = p.1 := Set.mem_singleton_iff.mp hr
      subst r
      exact mem_macroOrbit_root _ _ p
  have hreference : macroReference (outsideReference W X)
      (outsideReference Y X) p = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro r hr
    rcases hr.2 with ⟨q, hqOrbit, hqr⟩
    have hqp : q = p.1 := by simpa [horbit] using hqOrbit
    have hrZ : r ∈ outsideReference W X := hsub hr.1
    have hrp : r = p.1 := by
      apply DWeb.IsWarp.eq_of_mem_support hZ hrZ p.2
        r.initial_mem_support
      rw [← hqr]
      simpa [hqp] using q.initial_mem_support
    exact hpOutside (hrp ▸ hr.1)
  rcases hqOwner with hqOrbit | hqReference
  · have hqp : q = p.1 := by simpa [horbit] using hqOrbit
    simpa [p, t, hqp] using hxq
  · rw [hreference] at hqReference
    exact False.elim hqReference

/-- The finite endpoint selected by the assignment is the terminal of its
unique outside-row owner. -/
theorem assigned_terminal_macroRoot
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) {v : V}
    (hterminal : (A.assignment.assigned s).terminal? = some v) :
    Gamma.terminal?
      (initialPath (outsideReference W X) ⟨s.1, s.property.1⟩).1 =
        some v := by
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
  obtain ⟨q, hqZ, hqterminal⟩ :=
    (A.assignment.finite_terminal_mem s hterminal).1
  have hvQ : v ∈ (A.assignment.assigned s).vertexSet :=
    (A.assignment.assigned s).mem_vertexSet_of_terminal_eq hterminal
  have hvp : v ∈ p.1.support :=
    A.assigned_vertexSet_subset_macroRoot hW hsub s hvQ
  have hvq : v ∈ q.support := Gamma.terminal_mem_support hqterminal
  have hpq : p.1 = q :=
    DWeb.IsWarp.eq_of_mem_support hW p.2.1 hqZ.1 hvp hvq
  exact (congrArg Gamma.terminal? hpq).trans hqterminal

/-- Every retained forward edge of an actual outside-macro route lies on
the honest later row.  This is the concrete real-edge provenance needed in
the covered branches of limiting-reference reclassification. -/
theorem assigned_forwardEdges_subset_familyEdges
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) :
    (A.assignment.assigned s).directionEdges .forward ⊆ familyEdges W := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, hforward, hel⟩ := he
  have hfragment : IsFragmentOf l.path (outsideReference W X) :=
    (A.full.bracket_safe s).isBracketAlternating.2 l hl hforward
  rcases hfragment with ⟨p, hp, hlp⟩
  simp only [familyEdges, Set.mem_iUnion]
  exact ⟨p, hp.1, hlp.2 hel⟩

/-- Nontriviality of the exposed finite endpoint pair. -/
def AssignedEndpointsNontrivial
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X)) : Prop :=
  ∀ s v, (A.assignment.assigned s).terminal? = some v → s.1 ≠ v

/-- The actual old/new frontier separation supplies endpoint
nontriviality. -/
theorem assignedEndpointsNontrivial_of_endpointLocations
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    {target : Set V}
    (hsource : Gamma.initialSet W \ Gamma.initialSet Y ⊆
      Gamma.strictRoof target)
    (hterminal : Gamma.terminalFrontier W ⊆ target)
    (hessential : Gamma.essential target = target) :
    AssignedEndpointsNontrivial A := by
  intro s v hterm heq
  have hsStrict : s.1 ∈ Gamma.strictRoof target :=
    hsource ⟨initialSet_outsideReference_subset s.property.1,
      s.property.2⟩
  have hvTarget : v ∈ target :=
    hterminal (terminalFrontier_outsideReference_subset
      (A.assignment.finite_terminal_mem s hterm).1)
  have hvEssential : v ∈ Gamma.essential target :=
    hessential.symm ▸ hvTarget
  exact Set.disjoint_left.1 (Gamma.disjoint_strictRoof_essential target)
    hsStrict (heq ▸ hvEssential)

/-- The actual endpoint pairing exposed by the outside macro assignment.
Its endpoint map is literally the terminal option of the selected route. -/
noncomputable def toClosedEndpointPairing
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet Y ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof) :
    ClosedEndpointPairing
      (Gamma := Gamma) (Y := Y)
      (FracturedWarp.ofWarp (outsideReference W X)
        (outsideReference_isWarp hW))
      X before innerRoof outerRoof := by
  let H := A.closureContext hW hsource hterminal
  exact {
    endpoint := fun s ↦ (A.assignment.assigned s).terminal?
    finite_mem_terminal := by
      intro s v hsv
      exact (A.assignment.finite_terminal_mem s hsv).1
    finite_injective := by
      intro s t v hsv htv
      exact A.assignment.finite_terminals_injective hsv htv
    finite_witness := by
      intro s v hsv
      exact ⟨{
        path := A.assignment.assigned s
        starts_at := A.assignment.starts_at s
        ends_at := hsv
        safe := A.assignment.safe s
        eligible := H.eligible_finite s v hsv
        interior_disjoint := H.interior_disjoint_finite s v hsv
        outside := H.outside s }⟩
    infinite_witness := by
      intro s hs
      have hinfinite : (A.assignment.assigned s).IsInfinite :=
        (AltPath.isInfinite_iff_terminal?_eq_none _).2 hs
      exact ⟨{
        path := A.assignment.assigned s
        starts_at := A.assignment.starts_at s
        infinite := hinfinite
        safe := A.assignment.safe s
        eligible := H.eligible_infinite s hinfinite
        interior_disjoint := H.interior_disjoint_infinite s hinfinite
        outside := H.outside s }⟩ }

@[simp] theorem toClosedEndpointPairing_endpoint
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet Y ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \ Gamma.vertexSet Y ⊆
      before ∩ outerRoof)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) :
    (A.toClosedEndpointPairing hW hsource hterminal).endpoint s =
      (A.assignment.assigned s).terminal? := rfl

end OutsideMacroFullAssignment

/-! ## A common honest-row rank -/

/-- The well-founded predecessor rank of the honest later row. -/
noncomputable def outsideMacroRowRank (W : Set Gamma.DPath)
    (hW : Gamma.IsWarp W) : V → Nat :=
  ForwardOrientation.wellFoundedDepth (familyEdges W)
    (ForwardOrientation.predecessor_wellFounded (familyEdges W)
      (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
        hW)
      (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
        hW))

theorem outsideMacroRowRank_lt_of_mem_familyEdges
    (hW : Gamma.IsWarp W) {x y : V}
    (hxy : (x, y) ∈ familyEdges W) :
    outsideMacroRowRank W hW x < outsideMacroRowRank W hW y := by
  have hstep := ForwardOrientation.wellFoundedDepth_step (familyEdges W)
    (Alternating.IsWarp.familyEdges_biUnique hW)
    (ForwardOrientation.predecessor_wellFounded (familyEdges W)
      (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsDirectedCycle
        hW)
      (PathFilterComponents.DWeb.IsWarp.familyEdges_not_containsReverseDirectedRay
        hW)) hxy
  change ForwardOrientation.wellFoundedDepth (familyEdges W) _ x <
    ForwardOrientation.wellFoundedDepth (familyEdges W) _ y
  omega

private theorem walk_outsideMacroRowRank_le_finish
    {a b : V} (P : Walk Gamma.graph a b)
    (hW : Gamma.IsWarp W)
    (hP : P.edgeSet ⊆ familyEdges W) :
    outsideMacroRowRank W hW a ≤ outsideMacroRowRank W hW b := by
  induction P with
  | nil => exact le_rfl
  | @cons a c b h P ih =>
      have hac : outsideMacroRowRank W hW a <
          outsideMacroRowRank W hW c :=
        outsideMacroRowRank_lt_of_mem_familyEdges hW
          (hP (by simp [Walk.edgeSet_cons]))
      have htail : P.edgeSet ⊆ familyEdges W := by
        intro e he
        exact hP (by simp [Walk.edgeSet_cons, he])
      exact hac.le.trans (ih htail)

private theorem walk_outsideMacroRowRank_lt_finish
    {a b : V} (P : Walk Gamma.graph a b)
    (hW : Gamma.IsWarp W)
    (hP : P.edgeSet ⊆ familyEdges W) (hne : a ≠ b) :
    outsideMacroRowRank W hW a < outsideMacroRowRank W hW b := by
  cases P with
  | nil => exact False.elim (hne rfl)
  | @cons a c b h P =>
      have hac : outsideMacroRowRank W hW a <
          outsideMacroRowRank W hW c :=
        outsideMacroRowRank_lt_of_mem_familyEdges hW
          (hP (by simp [Walk.edgeSet_cons]))
      have htail : P.edgeSet ⊆ familyEdges W := by
        intro e he
        exact hP (by simp [Walk.edgeSet_cons, he])
      exact hac.trans_le (walk_outsideMacroRowRank_le_finish P hW htail)

private theorem no_directed_cycle_of_strict_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsDirectedCycle E := by
  rintro ⟨D, hD⟩
  let last : Nat := D.length - 1
  have hlast : last < D.length := Nat.sub_lt D.positive (by omega)
  have hnextLast : D.next ⟨last, hlast⟩ =
      (⟨0, D.positive⟩ : Fin D.length) := by
    apply Fin.ext
    have hs : last + 1 = D.length := Nat.sub_add_cancel D.positive
    simp [DirectedCycle.next, hs]
  have hmono : ∀ n, (hn : n < D.length) →
      rank (D.vertex ⟨0, D.positive⟩) ≤ rank (D.vertex ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.le_refl _
    | succ n ih =>
        intro hn
        have hn' : n < D.length := Nat.lt_trans (Nat.lt_succ_self n) hn
        have hnext : D.next (⟨n, hn'⟩ : Fin D.length) =
            ⟨n + 1, hn⟩ := by
          apply Fin.ext
          exact Nat.mod_eq_of_lt hn
        exact (ih hn').trans (Nat.le_of_lt (by
          rw [← hnext]
          exact hrank (hD ⟨⟨n, hn'⟩, rfl⟩)))
  have hback : rank (D.vertex ⟨last, hlast⟩) <
      rank (D.vertex ⟨0, D.positive⟩) := by
    rw [← hnextLast]
    exact hrank (hD ⟨⟨last, hlast⟩, rfl⟩)
  exact (Nat.not_lt_of_ge (hmono last hlast)) hback

private theorem no_reverse_ray_of_strict_rank
    (E : Set (V × V)) (rank : V → Nat)
    (hrank : ∀ {x y}, (x, y) ∈ E → rank x < rank y) :
    ¬ ContainsReverseDirectedRay E := by
  rintro ⟨R, hR⟩
  have hdesc (n : Nat) : rank (R.vertex (n + 1)) < rank (R.vertex n) :=
    hrank (hR n)
  have hbound : ∀ n, rank (R.vertex n) + n ≤ rank (R.vertex 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hdesc n
        omega
  have h := hbound (rank (R.vertex 0) + 1)
  omega

/-- The endpoints of every nontrivial finite assigned route advance in the
same honest-row rank. -/
theorem OutsideMacroFullAssignment.endpoint_rank
    (A : OutsideMacroFullAssignment (Y := Y) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference Y X ⊆ outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet Y}) {v : V}
    (hterm : (A.assignment.assigned s).terminal? = some v) :
    outsideMacroRowRank W hW s.1 < outsideMacroRowRank W hW v := by
  let p : outsideReference W X :=
    initialPath (outsideReference W X) ⟨s.1, s.property.1⟩
  obtain ⟨q, hpq⟩ := hWfinite p.2.1
  have hqterminal : q.finish = v := by
    have hpterminal := A.assigned_terminal_macroRoot hW hsub s hterm
    rw [hpq] at hpterminal
    exact Option.some.inj hpterminal
  have hpinitial : p.1.initial = s.1 := initialPath_initial _ _
  have hne : q.start ≠ q.finish := by
    intro h
    apply hnontrivial s v hterm
    calc
      s.1 = p.1.initial := hpinitial.symm
      _ = q.start := congrArg Path.initial hpq
      _ = q.finish := h
      _ = v := hqterminal
  have hrank := walk_outsideMacroRowRank_lt_finish q.walk hW (by
    intro e he
    simp only [familyEdges, Set.mem_iUnion]
    exact ⟨Sum.inl q, hpq ▸ p.2.1, he⟩) hne
  calc
    outsideMacroRowRank W hW s.1 =
        outsideMacroRowRank W hW p.1.initial :=
      congrArg (outsideMacroRowRank W hW) hpinitial.symm
    _ = outsideMacroRowRank W hW q.start := by
      exact congrArg (outsideMacroRowRank W hW)
        (congrArg Path.initial hpq)
    _ < outsideMacroRowRank W hW v := by
      simpa only [hqterminal] using hrank

namespace ClubStageGeometry

variable {Yglobal : Set Gamma.DPath}
variable (C : ClubStageGeometry Gamma Yglobal kappa (Order.succ kappa))

/-- The exact limiting-reference classification of one finite endpoint of
the actual macro assignment.  Unlike the generic pairing summary, its path
is definitionally the selected assigned route. -/
noncomputable def outsideMacroFiniteClassification
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference}) (v : V)
    (hsv : (A.assignment.assigned s).terminal? = some v) :
    LimitingFiniteContactClassification C X
      (A.assignment.assigned s) s.1 v := by
  let H := A.closureContext hW hsource hterminal
  have hlocal : IsImaginaryEdge Gamma C.selectedReference kappa s.1 v :=
    isImaginaryEdge_of_closed hclosed (H.eligible_finite s v hsv)
      (A.assignment.safe s) (A.assignment.starts_at s) hsv
      (H.interior_disjoint_finite s v hsv) (H.outside s)
  exact (C.globalizeLocalImaginary hSafeRoof
    (Q := A.assignment.assigned s) hlocal).some

/-- Infinite counterpart, again retaining the literal assigned route. -/
noncomputable def outsideMacroInfiniteClassification
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference})
    (hinfinite : (A.assignment.assigned s).IsInfinite) :
    LimitingInfiniteContactClassification C X persistent
      (A.assignment.assigned s) s.1 := by
  let H := A.closureContext hW hsource hterminal
  have hlocal : IsPopular Gamma C.selectedReference persistent kappa s.1 :=
    isPopular_of_closed_infinite hclosed
      (H.eligible_infinite s hinfinite) (A.assignment.safe s)
      (A.assignment.starts_at s) hinfinite
      (H.interior_disjoint_infinite s hinfinite) (H.outside s)
  exact (C.globalizeLocalPopular hSafeRoof
    (Q := A.assignment.assigned s) hlocal).some

/-- Every edge retained by any finite global classification advances in the
honest later-row rank.  Imaginary branches use the source/terminal rank;
covered branches use their literal forward-row provenance. -/
theorem outsideMacroFiniteRetained_rank
    {W : Set Gamma.DPath} {X : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference}) (v : V)
    (hsv : (A.assignment.assigned s).terminal? = some v)
    (K : LimitingFiniteContactClassification C X
      (A.assignment.assigned s) s.1 v)
    {x y : V} (hxy : (x, y) ∈ K.retainedEdges) :
    outsideMacroRowRank W hW x < outsideMacroRowRank W hW y := by
  cases K with
  | imaginary _ =>
      simp only [LimitingFiniteContactClassification.retainedEdges,
        Set.mem_singleton_iff, Prod.mk.injEq] at hxy
      rcases hxy with ⟨rfl, rfl⟩
      exact A.endpoint_rank hW hWfinite hsub hnontrivial s hsv
  | initialCovered _ =>
      exact outsideMacroRowRank_lt_of_mem_familyEdges hW
        (A.assigned_forwardEdges_subset_familyEdges s hxy)
  | terminalCovered _ =>
      exact outsideMacroRowRank_lt_of_mem_familyEdges hW
        (A.assigned_forwardEdges_subset_familyEdges s hxy)

/-- Every edge retained by any infinite global classification advances in
the same honest later-row rank. -/
theorem outsideMacroInfiniteRetained_rank
    {W : Set Gamma.DPath} {X persistent : Set V}
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference})
    (K : LimitingInfiniteContactClassification C X persistent
      (A.assignment.assigned s) s.1)
    {x y : V} (hxy : (x, y) ∈ K.retainedEdges) :
    outsideMacroRowRank W hW x < outsideMacroRowRank W hW y := by
  cases K with
  | popular _ =>
      simp [LimitingInfiniteContactClassification.retainedEdges] at hxy
  | initialCovered _ =>
      exact outsideMacroRowRank_lt_of_mem_familyEdges hW
        (A.assigned_forwardEdges_subset_familyEdges s hxy)

/-! ## The exact classified outside relation -/

/-- The complete edge contribution of the actual outside-macro assignment,
classified source by source against the limiting reference.  This definition
keeps the literal assigned route in its type; it does not pass through a
`Nonempty` witness selector. -/
noncomputable def outsideMacroRetainedEdges
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) : Set (V × V) :=
  {e | (∃ s v, ∃ hsv : (A.assignment.assigned s).terminal? = some v,
      e ∈ (C.outsideMacroFiniteClassification hSafeRoof A hW hsource
        hterminal hclosed s v hsv).retainedEdges) ∨
    (∃ s, ∃ hinfinite : (A.assignment.assigned s).IsInfinite,
      e ∈ (C.outsideMacroInfiniteClassification (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed s hinfinite).retainedEdges)}

/-- Every edge in the complete concrete outside contribution advances in
the common honest-row rank. -/
theorem outsideMacroRetainedEdges_rank
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    {x y : V}
    (hxy : (x, y) ∈ C.outsideMacroRetainedEdges (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed) :
    outsideMacroRowRank W hW x < outsideMacroRowRank W hW y := by
  rcases hxy with hxy | hxy
  · obtain ⟨s, v, hsv, hxy⟩ := hxy
    exact C.outsideMacroFiniteRetained_rank A hW hWfinite hsub
      hnontrivial s v hsv _ hxy
  · obtain ⟨s, hinfinite, hxy⟩ := hxy
    exact C.outsideMacroInfiniteRetained_rank A hW s _ hxy

/-- The concrete limiting-reference outside contribution is acyclic. -/
theorem outsideMacroRetainedEdges_acyclic
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    ¬ ContainsDirectedCycle
      (C.outsideMacroRetainedEdges (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) := by
  apply no_directed_cycle_of_strict_rank _ (outsideMacroRowRank W hW)
  exact C.outsideMacroRetainedEdges_rank hSafeRoof A hW hWfinite hsub
    hnontrivial hsource hterminal hclosed

/-- The same common rank excludes a reverse ray in the concrete outside
contribution. -/
theorem outsideMacroRetainedEdges_no_reverse_ray
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hsub : outsideReference C.selectedReference X ⊆
      outsideReference W X)
    (hnontrivial : A.AssignedEndpointsNontrivial)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    ¬ ContainsReverseDirectedRay
      (C.outsideMacroRetainedEdges (persistent := persistent)
        hSafeRoof A hW hsource hterminal hclosed) := by
  apply no_reverse_ray_of_strict_rank _ (outsideMacroRowRank W hW)
  exact C.outsideMacroRetainedEdges_rank hSafeRoof A hW hWfinite hsub
    hnontrivial hsource hterminal hclosed

/-- Reclassify the endpoint pairing constructed by the actual outside macro
assignment against the genuine limiting reference. -/
noncomputable def globalizeOutsideMacroEndpointPairing
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    LimitingClosedEndpointPairing C
      (FracturedWarp.ofWarp (outsideReference W X)
        (outsideReference_isWarp hW))
      X before innerRoof outerRoof persistent :=
  C.globalizeClosedEndpointPairing hSafeRoof
    (A.toClosedEndpointPairing hW hsource hterminal) hclosed

@[simp] theorem globalizeOutsideMacroEndpointPairing_endpoint
    {W : Set Gamma.DPath} {X : Set V}
    {before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : OutsideMacroFullAssignment
      (Y := C.selectedReference) (W := W) (X := X))
    (hW : Gamma.IsWarp W)
    (hsource : Gamma.initialSet W \ Gamma.initialSet C.selectedReference ⊆
      before ∩ innerRoof)
    (hterminal : Gamma.terminalFrontier W \
        Gamma.vertexSet C.selectedReference ⊆ before ∩ outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa)
    (s : {z : V // z ∈ Gamma.initialSet (outsideReference W X) \
      Gamma.initialSet C.selectedReference}) :
    (C.globalizeOutsideMacroEndpointPairing (persistent := persistent)
      hSafeRoof A hW hsource hterminal hclosed).endpoint s =
        (A.assignment.assigned s).terminal? := rfl

end ClubStageGeometry

#print axioms OutsideMacroFullAssignment.toClosedEndpointPairing
#print axioms OutsideMacroFullAssignment.assigned_forwardEdges_subset_familyEdges
#print axioms OutsideMacroFullAssignment.endpoint_rank
#print axioms ClubStageGeometry.outsideMacroFiniteClassification
#print axioms ClubStageGeometry.outsideMacroFiniteRetained_rank
#print axioms ClubStageGeometry.outsideMacroInfiniteRetained_rank
#print axioms ClubStageGeometry.outsideMacroRetainedEdges_acyclic
#print axioms ClubStageGeometry.outsideMacroRetainedEdges_no_reverse_ray
#print axioms ClubStageGeometry.globalizeOutsideMacroEndpointPairing

end LinkageBlueprint
end Blueprint
end Erdos599
