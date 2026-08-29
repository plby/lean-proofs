/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayContactTransaction

/-!
# Claim 2 with covered exposed endpoints

An occurrence interval of a safe alternating path can fail to be safe only
at an exposed endpoint: after cutting, a formerly internal forward link may
end (or begin) on the reference warp.  Such an interval cannot be inserted
into a hammock, but the covered endpoint has a unique reference owner; when
the reference is closed at `X`, that whole owner lies in `X`.

This file records the corresponding positive classification.  The
`internallySafe` predicate is exactly Definition 4.8 with the two exposed
endpoint clauses removed.  `classifyFinite` says that every internally safe
finite segment is either a genuine Claim-2 imaginary edge or has a closed
reference owner at one of the two newly exposed endpoints.  The final
singleton-link theorem constructs internal safeness directly from an
occurrence of the link in an ambient safe alternating path; in particular it
applies to the first and last pieces in the endpoint-cleanliness audit.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {X before innerRoof outerRoof : Set V}
variable {kappa : Cardinal.{u}}

/-- Safeness away from the two exposed endpoint clauses. -/
def InternallySafe (Y : Set Gamma.DPath) (Q : AltPath Gamma.graph) : Prop :=
  Gamma.IsWarp Y ∧ BackwardLinksOn Y Q ∧
    (∀ p ∈ Y,
      IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p) ∧
    ¬ ContainsDirectedRay (Q.edgeSet \ familyEdges Y) ∧
    ¬ ContainsDirectedCycle (Q.edgeSet \ familyEdges Y)

namespace InternallySafe

/-- A safe alternating path is internally safe. -/
theorem of_isSafe {Q : AltPath Gamma.graph} (hQ : IsSafe Y Q) :
    InternallySafe Y Q :=
  ⟨hQ.1.1, hQ.1.2.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2⟩

/-- The only possible failures of safeness for an internally safe path are
the two exposed endpoint clauses. -/
theorem isSafe_or_endpointCovered {Q : AltPath Gamma.graph}
    (hQ : InternallySafe Y Q) :
    IsSafe Y Q ∨
      (Q.firstDirection? = some .forward ∧
        Q.initial ∈ Gamma.vertexSet Y) ∨
      ∃ v, Q.terminal? = some v ∧
        Q.lastDirection? = some .forward ∧ v ∈ Gamma.vertexSet Y := by
  by_cases hfirst :
      Q.firstDirection? = some .forward → Q.initial ∉ Gamma.vertexSet Y
  · by_cases hlast : ∀ v, Q.terminal? = some v →
        Q.lastDirection? = some .forward → v ∉ Gamma.vertexSet Y
    · exact Or.inl ⟨⟨hQ.1, hQ.2.1, hfirst, hlast⟩,
        hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2⟩
    · right
      right
      push Not at hlast
      exact hlast
  · right
    left
    push Not at hfirst
    exact hfirst

/-- Internal safeness plus uncovered exposed endpoints reconstructs ordinary
safeness.  The direction hypotheses in `IsAlternating` are then irrelevant. -/
theorem isSafe_of_exposedEndpoints {Q : AltPath Gamma.graph}
    (hQ : InternallySafe Y Q)
    (hinitial : Q.initial ∉ Gamma.vertexSet Y)
    (hterminal : ∀ v, Q.terminal? = some v →
      v ∉ Gamma.vertexSet Y) : IsSafe Y Q := by
  exact ⟨⟨hQ.1, hQ.2.1, fun _ ↦ hinitial,
      fun v hv _ ↦ hterminal v hv⟩,
    hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2⟩

end InternallySafe

/-- A reference member owning a covered contact and, by closure, lying
wholly in the closing set. -/
structure ClosedReferenceOwner (Y : Set Gamma.DPath) (X : Set V) (x : V)
    where
  path : Gamma.DPath
  mem : path ∈ Y
  contains : x ∈ path.support
  contained : path.support ⊆ X

namespace ClosedReferenceOwner

/-- Closure constructs the closed owner of every covered vertex in `X`. -/
theorem exists_of_mem
    (hclosed : ClosedUnderPaths Gamma Y X) {x : V}
    (hxY : x ∈ Gamma.vertexSet Y) (hxX : x ∈ X) :
    Nonempty (ClosedReferenceOwner Y X x) := by
  obtain ⟨p, hpY, hxp⟩ := hxY
  exact ⟨{
    path := p
    mem := hpY
    contains := hxp
    contained := hclosed p hpY ⟨x, hxp, hxX⟩ }⟩

/-- Warp disjointness makes the closed owner unique at path level. -/
theorem path_eq (hY : Gamma.IsWarp Y) {x : V}
    (P R : ClosedReferenceOwner Y X x) : P.path = R.path :=
  DWeb.IsWarp.eq_of_mem_support hY P.mem R.mem P.contains R.contains

end ClosedReferenceOwner

/-- The exact three-way output for a finite endpoint-covered segment. -/
inductive FiniteSegmentClassification
    (Q : AltPath Gamma.graph) (u v : V) : Type u
  | imaginary : IsImaginaryEdge Gamma Y kappa u v →
      FiniteSegmentClassification Q u v
  | initialCovered : ClosedReferenceOwner Y X u →
      FiniteSegmentClassification Q u v
  | terminalCovered : ClosedReferenceOwner Y X v →
      FiniteSegmentClassification Q u v

/-- An occurrence interval with a covered `X` endpoint is classifiable
without any safeness, eligibility, or hammock hypothesis on that interval.
This is the branch needed for the first/last-fragment obstruction: the
reference owner, rather than a nonexistent `IsSafe` proof, is retained. -/
theorem classifyFinite_of_endpointCovered
    {u v : V} {Q : AltPath Gamma.graph}
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (hcovered :
      (u ∈ Gamma.vertexSet Y ∧ u ∈ X) ∨
      (v ∈ Gamma.vertexSet Y ∧ v ∈ X)) :
    Nonempty (FiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) Q u v) := by
  rcases hcovered with hu | hv
  · exact ⟨.initialCovered
      (ClosedReferenceOwner.exists_of_mem hreferenceClosed hu.1 hu.2).some⟩
  · exact ⟨.terminalCovered
      (ClosedReferenceOwner.exists_of_mem hreferenceClosed hv.1 hv.2).some⟩

/-- Generalized finite Claim 2.  Unlike `isImaginaryEdge_of_closed`, this
does not assume that the cut segment is safe.  Internal safeness suffices to
classify the only two failures, and closure turns either covered exposed
endpoint into a unique closed reference owner. -/
theorem classifyFinite
    {u v : V} {Q : AltPath Gamma.graph}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible : u ∉ Gamma.vertexSet Y → v ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof u (.vertex v))
    (hQinternal : u ∉ Gamma.vertexSet Y → v ∉ Gamma.vertexSet Y →
      InternallySafe Y Q)
    (hQinitial : Q.initial = u) (hQterminal : Q.terminal? = some v)
    (hQX : Disjoint (hammockInterior u (.vertex v) Q) X)
    (hQoutside : ¬ Q.vertexSet ⊆ X)
    (huX : u ∈ Gamma.vertexSet Y → u ∈ X)
    (hvX : v ∈ Gamma.vertexSet Y → v ∈ X) :
    Nonempty (FiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) Q u v) := by
  by_cases huY : u ∈ Gamma.vertexSet Y
  · exact ⟨.initialCovered
      (ClosedReferenceOwner.exists_of_mem hreferenceClosed huY
        (huX huY)).some⟩
  by_cases hvY : v ∈ Gamma.vertexSet Y
  · exact ⟨.terminalCovered
      (ClosedReferenceOwner.exists_of_mem hreferenceClosed hvY
        (hvX hvY)).some⟩
  have hQinitialOff : Q.initial ∉ Gamma.vertexSet Y := by
    rw [hQinitial]
    exact huY
  have hQterminalOff : ∀ w, Q.terminal? = some w →
      w ∉ Gamma.vertexSet Y := by
    intro w hw
    have hwv : w = v := Option.some.inj (hw.symm.trans hQterminal)
    simpa [hwv] using hvY
  have hsafe := (hQinternal huY hvY).isSafe_of_exposedEndpoints
    hQinitialOff hQterminalOff
  exact ⟨.imaginary (isImaginaryEdge_of_closed hclosed
    (heligible huY hvY) hsafe hQinitial hQterminal hQX hQoutside)⟩

/-- The exact two-way output for an infinite endpoint-covered segment. -/
inductive InfiniteSegmentClassification
    (persistent : Set V) (Q : AltPath Gamma.graph) (u : V) : Type u
  | popular : IsPopular Gamma Y persistent kappa u →
      InfiniteSegmentClassification persistent Q u
  | initialCovered : ClosedReferenceOwner Y X u →
      InfiniteSegmentClassification persistent Q u

/-- The covered initial endpoint of an infinite occurrence interval is
likewise classifiable without asserting that the cut tail is safe. -/
theorem classifyInfinite_of_endpointCovered
    {persistent : Set V} {u : V} {Q : AltPath Gamma.graph}
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (huY : u ∈ Gamma.vertexSet Y) (huX : u ∈ X) :
    Nonempty (InfiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) persistent Q u) := by
  exact ⟨.initialCovered
    (ClosedReferenceOwner.exists_of_mem hreferenceClosed huY huX).some⟩

/-- Generalized infinite Claim 2.  An internally safe infinite interval has
no terminal endpoint defect; it is either a genuine popularity witness or
its newly exposed initial endpoint is owned by a closed reference member. -/
theorem classifyInfinite
    {persistent : Set V} {u : V} {Q : AltPath Gamma.graph}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible : u ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof u .infinity)
    (hQinternal : u ∉ Gamma.vertexSet Y → InternallySafe Y Q)
    (hQinitial : Q.initial = u) (hQinfinite : Q.IsInfinite)
    (hQX : Disjoint (hammockInterior u .infinity Q) X)
    (hQoutside : ¬ Q.vertexSet ⊆ X)
    (huX : u ∈ Gamma.vertexSet Y → u ∈ X) :
    Nonempty (InfiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) persistent Q u) := by
  by_cases huY : u ∈ Gamma.vertexSet Y
  · exact ⟨.initialCovered
      (ClosedReferenceOwner.exists_of_mem hreferenceClosed huY
        (huX huY)).some⟩
  have hQinitialOff : Q.initial ∉ Gamma.vertexSet Y := by
    rw [hQinitial]
    exact huY
  have hnone := Q.isInfinite_iff_terminal?_eq_none.mp hQinfinite
  have hQterminalOff : ∀ v, Q.terminal? = some v →
      v ∉ Gamma.vertexSet Y := by
    intro v hv
    rw [hnone] at hv
    contradiction
  have hsafe := (hQinternal huY).isSafe_of_exposedEndpoints
    hQinitialOff hQterminalOff
  exact ⟨.popular (isPopular_of_closed_infinite
    (persistent := persistent) hclosed (heligible huY) hsafe hQinitial
    hQinfinite hQX hQoutside)⟩

namespace FiniteSegmentClassification

/-- Relation retained from a general classified finite occurrence interval.
A genuine outside interval is compressed to its Claim-2 imaginary edge.  If
an exposed endpoint is covered, safe switching retains every forward link of
the interval and deletes every backward reference link. -/
def retainedEdges {u v : V} {Q : AltPath Gamma.graph}
    (C : FiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) Q u v) : Set (V × V) :=
  match C with
  | .imaginary _ => {(u, v)}
  | .initialCovered _ => Q.directionEdges .forward
  | .terminalCovered _ => Q.directionEdges .forward

@[simp] theorem retainedEdges_imaginary
    {u v : V} {Q : AltPath Gamma.graph}
    (h : IsImaginaryEdge Gamma Y kappa u v) :
    (FiniteSegmentClassification.imaginary (X := X) (Q := Q) h).retainedEdges =
      {(u, v)} := rfl

@[simp] theorem retainedEdges_initialCovered
    {u v : V} {Q : AltPath Gamma.graph}
    (P : ClosedReferenceOwner Y X u) :
    (FiniteSegmentClassification.initialCovered (kappa := kappa) (v := v)
      (Q := Q) P).retainedEdges = Q.directionEdges .forward := rfl

@[simp] theorem retainedEdges_terminalCovered
    {u v : V} {Q : AltPath Gamma.graph}
    (P : ClosedReferenceOwner Y X v) :
    (FiniteSegmentClassification.terminalCovered (kappa := kappa) (u := u)
      (Q := Q) P).retainedEdges = Q.directionEdges .forward := rfl

private theorem directionEdges_subset_edgeSet
    (Q : AltPath Gamma.graph) (d : Direction) :
    Q.directionEdges d ⊆ Q.edgeSet := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hd, hel⟩ := he
  rw [Q.edgeSet_eq_iUnion_links]
  simp only [Set.mem_iUnion]
  exact ⟨l, hl, hel⟩

/-- Both branches of the endpoint-covered repair give an honest relation in
the imaginary graph.  This is the general-interval interface: it does not
assume the classified occurrence is a singleton. -/
theorem retainedEdges_subset_imaginaryGraph
    {u v : V} {Q : AltPath Gamma.graph}
    (C : FiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) Q u v) :
    C.retainedEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  cases C with
  | imaginary h =>
      rintro e rfl
      exact Or.inr h
  | initialCovered _ =>
      intro e he
      exact Or.inl (Q.edgeSet_subset_adj
        (directionEdges_subset_edgeSet Q .forward he))
  | terminalCovered _ =>
      intro e he
      exact Or.inl (Q.edgeSet_subset_adj
        (directionEdges_subset_edgeSet Q .forward he))

end FiniteSegmentClassification

/-! ## A link occurrence inherits internal safeness -/

private theorem eq_of_mem_singleton_links
    {r l : Link Gamma.graph}
    (hr : r ∈ (AltPath.finite (FiniteTrace.singleton l)).links) : r = l := by
  change r ∈ (FiniteTrace.singleton l).links at hr
  rcases hr with ⟨i, rfl⟩
  rfl

private theorem mem_singleton_links (l : Link Gamma.graph) :
    l ∈ (AltPath.finite (FiniteTrace.singleton l)).links := by
  change l ∈ (FiniteTrace.singleton l).links
  exact ⟨0, rfl⟩

private theorem singleton_backwardEdges_forward
    (l : Link Gamma.graph) (hforward : l.direction = .forward) :
    (AltPath.finite (FiniteTrace.singleton l)).directionEdges .backward = ∅ := by
  ext e
  simp only [AltPath.directionEdges, Set.mem_iUnion,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨r, hr, hback, _he⟩
  have hrl : r = l := eq_of_mem_singleton_links hr
  subst r
  simp [hforward] at hback

private theorem singleton_backwardEdges_backward
    (l : Link Gamma.graph) (hbackward : l.direction = .backward) :
    (AltPath.finite (FiniteTrace.singleton l)).directionEdges .backward =
      l.path.edgeSet := by
  ext e
  simp only [AltPath.directionEdges, Set.mem_iUnion]
  constructor
  · rintro ⟨r, hr, hback, he⟩
    have hrl : r = l := eq_of_mem_singleton_links hr
    subst r
    exact he
  · intro he
    exact ⟨l, mem_singleton_links l, hbackward, he⟩

/-- A single link occurring in a safe ambient alternating path retains all
internal safeness clauses, even when cutting exposes a covered endpoint and
therefore destroys ordinary safeness. -/
theorem internallySafe_singleton_of_mem
    {Q : AltPath Gamma.graph} (hQsafe : IsSafe Y Q)
    (l : Link Gamma.graph) (hl : l ∈ Q.links) :
    InternallySafe Y (.finite (.singleton l)) := by
  refine ⟨hQsafe.1.1, ?_, ?_, ?_, ?_⟩
  · intro r hr hback
    have hrl : r = l := eq_of_mem_singleton_links hr
    subst r
    exact hQsafe.1.2.1 l hl hback
  · intro p hpY
    by_cases hforward : l.direction = .forward
    · left
      rw [singleton_backwardEdges_forward l hforward]
      simp
    · have hbackward : l.direction = .backward := by
        cases hdir : l.direction <;> simp_all
      rw [singleton_backwardEdges_backward l hbackward]
      obtain ⟨r, hrY, hlr⟩ := hQsafe.1.2.1 l hl hbackward
      by_cases hpr : p = r
      · subst r
        right
        refine ⟨.inl l.path, hlr, ?_⟩
        exact Set.inter_eq_left.2 hlr.2
      · left
        ext e
        constructor
        · intro he
          have hendL := l.path.edgeSet_subset_support_prod he.1
          have hendP := p.edgeSet_subset_support_prod he.2
          exact False.elim <| Set.disjoint_left.1
            (DWeb.IsWarp.disjoint Gamma hQsafe.1.1 hpY hrY hpr)
            hendP.1 (hlr.1 hendL.1)
        · simp
  · intro hRay
    exact Alternating.FinitePath.edgeSet_not_containsDirectedRay l.path
      ⟨hRay.choose, hRay.choose_spec.trans (by
        intro e he
        rw [← AltPath.edgeSet_single l]
        exact he.1)⟩
  · intro hCycle
    exact Alternating.FinitePath.edgeSet_not_containsDirectedCycle l.path
      ⟨hCycle.choose, hCycle.choose_spec.trans (by
        intro e he
        rw [← AltPath.edgeSet_single l]
        exact he.1)⟩

/-- Both traversal endpoints of a backward link are covered by its reference
owner.  Thus a linkwise switched transaction deletes backward occurrences;
Claim 2 is needed only after grouping links into a larger outside interval. -/
theorem backward_link_endpoints_mem_reference
    {Q : AltPath Gamma.graph} (hQsafe : IsSafe Y Q)
    {l : Link Gamma.graph} (hl : l ∈ Q.links)
    (hbackward : l.direction = .backward) :
    l.entry ∈ Gamma.vertexSet Y ∧ l.exit ∈ Gamma.vertexSet Y := by
  obtain ⟨p, hpY, hlp⟩ := hQsafe.1.2.1 l hl hbackward
  exact ⟨⟨p, hpY, hlp.1 l.entry_mem_support⟩,
    ⟨p, hpY, hlp.1 l.exit_mem_support⟩⟩

/-- A backward occurrence whose entry is a recorded `X`-contact has a
closed reference owner.  No assertion is made for its other, possibly
non-contact endpoint. -/
theorem backward_link_entry_closedOwner_of_mem
    {Q : AltPath Gamma.graph} (hQsafe : IsSafe Y Q)
    {l : Link Gamma.graph} (hl : l ∈ Q.links)
    (hbackward : l.direction = .backward)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (hentryX : l.entry ∈ X) :
    Nonempty (ClosedReferenceOwner Y X l.entry) := by
  exact ClosedReferenceOwner.exists_of_mem hreferenceClosed
    (backward_link_endpoints_mem_reference hQsafe hl hbackward).1 hentryX

/-- The symmetric closed-owner certificate for a recorded exit contact. -/
theorem backward_link_exit_closedOwner_of_mem
    {Q : AltPath Gamma.graph} (hQsafe : IsSafe Y Q)
    {l : Link Gamma.graph} (hl : l ∈ Q.links)
    (hbackward : l.direction = .backward)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (hexitX : l.exit ∈ X) :
    Nonempty (ClosedReferenceOwner Y X l.exit) := by
  exact ClosedReferenceOwner.exists_of_mem hreferenceClosed
    (backward_link_endpoints_mem_reference hQsafe hl hbackward).2 hexitX

/-- If every closing-set contact of one link is one of its traversal
endpoints, its hammock interior is disjoint from the closing set. -/
theorem singleton_hammockInterior_disjoint_of_contacts
    (l : Link Gamma.graph)
    (hcontacts : ∀ x ∈ l.path.support, x ∈ X →
      x = l.entry ∨ x = l.exit) :
    Disjoint
      (hammockInterior l.entry (.vertex l.exit) (.finite (.singleton l))) X := by
  rw [Set.disjoint_left]
  intro x hx hX
  have hsupport : x ∈ l.path.support := by
    have h := hx.1
    change x ∈ (FiniteTrace.singleton l).vertexSet at h
    simpa only [FiniteTrace.vertexSet_singleton] using h
  rcases hcontacts x hsupport hX with hentry | hexit
  · exact hx.2 (by simp [hammockEndpoints, hentry])
  · exact hx.2 (by simp [hammockEndpoints, hexit])

/-- One endpoint outside `X` makes the singleton link genuinely outside
the closing set. -/
theorem singleton_not_vertexSet_subset_of_entry_not_mem
    (l : Link Gamma.graph) (hentry : l.entry ∉ X) :
    ¬ (AltPath.finite (FiniteTrace.singleton l)).vertexSet ⊆ X := by
  intro hsubset
  exact hentry (hsubset (by
    change l.entry ∈ (FiniteTrace.singleton l).vertexSet
    rw [FiniteTrace.vertexSet_singleton]
    exact l.entry_mem_support))

/-- Symmetric outside certificate from the exit endpoint. -/
theorem singleton_not_vertexSet_subset_of_exit_not_mem
    (l : Link Gamma.graph) (hexit : l.exit ∉ X) :
    ¬ (AltPath.finite (FiniteTrace.singleton l)).vertexSet ⊆ X := by
  intro hsubset
  exact hexit (hsubset (by
    change l.exit ∈ (FiniteTrace.singleton l).vertexSet
    rw [FiniteTrace.vertexSet_singleton]
    exact l.exit_mem_support))

/-- Positive classification of a literal link occurrence in an ambient safe
assignment.  Covered first/last fragments are returned with their closed
reference owner instead of being incorrectly asserted safe. -/
theorem classifySingletonLink
    {Q : AltPath Gamma.graph} (hQsafe : IsSafe Y Q)
    (l : Link Gamma.graph) (hl : l ∈ Q.links)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible : l.entry ∉ Gamma.vertexSet Y →
      l.exit ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof l.entry (.vertex l.exit))
    (hQX : Disjoint
      (hammockInterior l.entry (.vertex l.exit) (.finite (.singleton l))) X)
    (hQoutside : ¬
      (AltPath.finite (FiniteTrace.singleton l)).vertexSet ⊆ X)
    (hentryX : l.entry ∈ Gamma.vertexSet Y → l.entry ∈ X)
    (hexitX : l.exit ∈ Gamma.vertexSet Y → l.exit ∈ X) :
    Nonempty (FiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa)
      (.finite (.singleton l)) l.entry l.exit) := by
  apply classifyFinite hclosed hreferenceClosed heligible
      (fun _ _ ↦ internallySafe_singleton_of_mem hQsafe l hl)
  · rfl
  · rfl
  · exact hQX
  · exact hQoutside
  · exact hentryX
  · exact hexitX

/-- Fully contact-facing singleton classification.  The caller supplies
only the literal endpoint-contact property and one outside endpoint; the
two technical Claim-2 set conditions are derived here. -/
theorem classifySingletonLink_of_contacts
    {Q : AltPath Gamma.graph} (hQsafe : IsSafe Y Q)
    (l : Link Gamma.graph) (hl : l ∈ Q.links)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible : l.entry ∉ Gamma.vertexSet Y →
      l.exit ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof l.entry (.vertex l.exit))
    (hcontacts : ∀ x ∈ l.path.support, x ∈ X →
      x = l.entry ∨ x = l.exit)
    (houtside : l.entry ∉ X ∨ l.exit ∉ X)
    (hentryX : l.entry ∈ Gamma.vertexSet Y → l.entry ∈ X)
    (hexitX : l.exit ∈ Gamma.vertexSet Y → l.exit ∈ X) :
    Nonempty (FiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa)
      (.finite (.singleton l)) l.entry l.exit) := by
  apply classifySingletonLink hQsafe l hl hclosed hreferenceClosed heligible
      (singleton_hammockInterior_disjoint_of_contacts l hcontacts)
  · rcases houtside with hentry | hexit
    · exact singleton_not_vertexSet_subset_of_entry_not_mem l hentry
    · exact singleton_not_vertexSet_subset_of_exit_not_mem l hexit
  · exact hentryX
  · exact hexitX

/-! ## Transaction-level link classification -/

/-- Dependency-minimal classification used by the literal switched
transaction.  A forward link is already a real directed path and never needs
Claim 2.  A backward link is either deleted at a closed reference contact or,
when both endpoints are uncovered, compressed to a genuine imaginary edge. -/
inductive SingletonTransactionClassification (l : Link Gamma.graph) : Type u
  | realForward : l.direction = .forward →
      SingletonTransactionClassification l
  | deletedBackward : l.direction = .backward →
      SingletonTransactionClassification l
  | imaginaryBackward : l.direction = .backward →
      IsImaginaryEdge Gamma Y kappa l.entry l.exit →
      SingletonTransactionClassification l
  | closedBackwardInitial : l.direction = .backward →
      ClosedReferenceOwner Y X l.entry →
      SingletonTransactionClassification l
  | closedBackwardTerminal : l.direction = .backward →
      ClosedReferenceOwner Y X l.exit →
      SingletonTransactionClassification l

/-- Canonical unconditional classification of one literal link. -/
def SingletonTransactionClassification.literal (l : Link Gamma.graph) :
    SingletonTransactionClassification
      (Y := Y) (X := X) (kappa := kappa) l := by
  by_cases hforward : l.direction = .forward
  · exact .realForward hforward
  · exact .deletedBackward (by
      cases hdir : l.direction with
      | forward => exact False.elim (hforward hdir)
      | backward => rfl)

/-- Every literal link has an unconditional safe-switch transaction: retain
its real path when traversed forward and delete it when traversed backward.
Closed-owner and imaginary certificates are optional refinements, not
preconditions for the literal transaction. -/
theorem classifySingletonTransaction
    (l : Link Gamma.graph) :
    Nonempty (SingletonTransactionClassification
      (Y := Y) (X := X) (kappa := kappa) l) :=
  ⟨SingletonTransactionClassification.literal l⟩

/-- Unconditional linkwise transaction classification from an ambient safe
occurrence and literal endpoint-contact geometry.  Eligibility is requested
only in the one branch which actually invokes Claim 2: a backward link with
both endpoints uncovered from the reference warp. -/
theorem classifySingletonTransaction_of_contacts
    {Q : AltPath Gamma.graph} (hQsafe : IsSafe Y Q)
    (l : Link Gamma.graph) (hl : l ∈ Q.links)
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (heligible : l.direction = .backward →
      l.entry ∉ Gamma.vertexSet Y → l.exit ∉ Gamma.vertexSet Y →
      HammockEligible before innerRoof outerRoof l.entry (.vertex l.exit))
    (houtsideGeometry : l.direction = .backward →
      l.entry ∉ Gamma.vertexSet Y → l.exit ∉ Gamma.vertexSet Y →
      (∀ x ∈ l.path.support, x ∈ X →
        x = l.entry ∨ x = l.exit) ∧
      (l.entry ∉ X ∨ l.exit ∉ X))
    (hentryX : l.entry ∈ Gamma.vertexSet Y → l.entry ∈ X)
    (hexitX : l.exit ∈ Gamma.vertexSet Y → l.exit ∈ X) :
    Nonempty (SingletonTransactionClassification
      (Y := Y) (X := X) (kappa := kappa) l) := by
  cases hdirection : l.direction with
  | forward => exact ⟨.realForward hdirection⟩
  | backward => exact ⟨.deletedBackward hdirection⟩

namespace SingletonTransactionClassification

/-- The literal relation contributed by one classified link. -/
def retainedEdges {l : Link Gamma.graph}
    (C : SingletonTransactionClassification
      (Y := Y) (X := X) (kappa := kappa) l) : Set (V × V) :=
  match C with
  | .realForward _ => l.path.edgeSet
  | .deletedBackward _ => ∅
  | .imaginaryBackward _ _ => {(l.entry, l.exit)}
  | .closedBackwardInitial _ _ => ∅
  | .closedBackwardTerminal _ _ => ∅

/-- Exact retained relation of the canonical literal classification. -/
theorem retainedEdges_literal (l : Link Gamma.graph) :
    (SingletonTransactionClassification.literal
      (Y := Y) (X := X) (kappa := kappa) l).retainedEdges =
      if l.direction = .forward then l.path.edgeSet else ∅ := by
  cases hdirection : l.direction with
  | forward => simp [SingletonTransactionClassification.literal,
      retainedEdges, hdirection]
  | backward => simp [SingletonTransactionClassification.literal,
      retainedEdges, hdirection]

/-- Every linkwise classified transaction edge belongs to the imaginary
graph; closed backward links contribute no edge. -/
theorem retainedEdges_subset_imaginaryGraph {l : Link Gamma.graph}
    (C : SingletonTransactionClassification
      (Y := Y) (X := X) (kappa := kappa) l) :
    C.retainedEdges ⊆ {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  cases C with
  | realForward _ =>
      intro e he
      exact Or.inl (l.path.edgeSet_subset_adj he)
  | deletedBackward _ => exact Set.empty_subset _
  | imaginaryBackward _ h =>
      rintro e rfl
      exact Or.inr h
  | closedBackwardInitial _ _ => exact Set.empty_subset _
  | closedBackwardTerminal _ _ => exact Set.empty_subset _

end SingletonTransactionClassification

namespace FiniteSegmentClassification

/-- Relation contributed by a classified singleton occurrence.  A genuine
Claim-2 segment contributes its one imaginary edge.  If cutting only exposed
a covered endpoint, an actual forward link is retained; a backward reference
link is deleted, exactly as in safe switching. -/
def retainedSingletonEdges {l : Link Gamma.graph}
    (C : FiniteSegmentClassification (Y := Y) (X := X) (kappa := kappa)
      (.finite (.singleton l)) l.entry l.exit) : Set (V × V) :=
  match C with
  | .imaginary _ => {(l.entry, l.exit)}
  | .initialCovered _ =>
      if l.direction = .forward then l.path.edgeSet else ∅
  | .terminalCovered _ =>
      if l.direction = .forward then l.path.edgeSet else ∅

/-- The classified singleton relation is always an honest relation in the
imaginary graph: covered endpoint pieces use real graph edges. -/
theorem retainedSingletonEdges_subset_imaginaryGraph {l : Link Gamma.graph}
    (C : FiniteSegmentClassification (Y := Y) (X := X) (kappa := kappa)
      (.finite (.singleton l)) l.entry l.exit) :
    C.retainedSingletonEdges ⊆
      {e | (imaginaryGraph Gamma Y kappa).Adj e.1 e.2} := by
  cases C with
  | imaginary h =>
      rintro e rfl
      exact Or.inr h
  | initialCovered _ =>
      by_cases hforward : l.direction = .forward
      · rw [retainedSingletonEdges, if_pos hforward]
        intro e he
        exact Or.inl (l.path.edgeSet_subset_adj he)
      · rw [retainedSingletonEdges, if_neg hforward]
        exact Set.empty_subset _
  | terminalCovered _ =>
      by_cases hforward : l.direction = .forward
      · rw [retainedSingletonEdges, if_pos hforward]
        intro e he
        exact Or.inl (l.path.edgeSet_subset_adj he)
      · rw [retainedSingletonEdges, if_neg hforward]
        exact Set.empty_subset _

end FiniteSegmentClassification

end Blueprint
end Erdos599
