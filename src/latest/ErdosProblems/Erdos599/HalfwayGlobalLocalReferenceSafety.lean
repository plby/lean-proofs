/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayGlobalLocalReferenceIncidence

/-! # Transporting local reference safeness to the limiting reference

The selected reference is finite, while the global limiting reference need
not be.  A locally safe alternating route is nevertheless globally safe as
soon as all of its contacts with the limiting reference already lie in the
selected-reference carrier.  Exact prefix incidence supplies the interval
condition; monotonicity supplies the ray and cycle conditions.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {kappa : Cardinal.{u}}

namespace ladderReference

variable {L : Gamma.KappaLadder kappa} {a : Ladder.Stage kappa}

/-- All global-reference contacts of `Q` are already visible in the finite
selected reference.  This is the precise confinement fact supplied by the
old restricted-web geometry in Assertion 9.31. -/
def ReferenceContactConfined (Q : AltPath Gamma.graph) : Prop :=
  Q.vertexSet ∩ Gamma.vertexSet L.limitWarp ⊆
    Gamma.vertexSet (ladderReference L a)

/-- Only the exposed endpoints of `Q` need to avoid unseen future tails.
The literal source predicate `IsAlternating` permits forward links to meet
reference vertices internally, so whole-carrier confinement is stronger than
the hypothesis actually needed to transport safeness. -/
def ReferenceEndpointConfined (Q : AltPath Gamma.graph) : Prop :=
  (Q.firstDirection? = some .forward →
    Q.initial ∈ Gamma.vertexSet L.limitWarp →
    Q.initial ∈ Gamma.vertexSet (ladderReference L a)) ∧
  (∀ t, Q.terminal? = some t → Q.lastDirection? = some .forward →
    t ∈ Gamma.vertexSet L.limitWarp →
    t ∈ Gamma.vertexSet (ladderReference L a))

theorem ReferenceContactConfined.endpointConfined
    {Q : AltPath Gamma.graph}
    (h : ReferenceContactConfined (L := L) (a := a) Q) :
    ReferenceEndpointConfined (L := L) (a := a) Q := by
  refine ⟨?_, ?_⟩
  · intro _hfirst hglobal
    exact h ⟨Q.initial_mem_vertexSet, hglobal⟩
  · intro t hterminal _hlast hglobal
    exact h ⟨Q.mem_vertexSet_of_terminal_eq hterminal, hglobal⟩

/-- Local backward fragments remain fragments of their limiting owners. -/
theorem isFragmentOf_limitWarp_of_local
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {f : FinitePath Gamma.graph}
    (hf : IsFragmentOf f (ladderReference L a)) :
    IsFragmentOf f L.limitWarp := by
  obtain ⟨q, hq, hfq⟩ := hf
  let qs : ladderReference L a := ⟨q, hq⟩
  refine ⟨limitExtension hL qs, limitExtension_mem hL qs, ?_⟩
  exact ⟨hfq.1.trans
      (Gamma.support_mono_of_extends (extends_limitExtension hL qs)),
    hfq.2.trans
      (Path.edgeSet_mono_of_extends (extends_limitExtension hL qs))⟩

/-- Under contact confinement, local alternation is also alternation with
respect to the global limiting reference. -/
theorem isAlternating_limitWarp_of_contactConfined
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hQ : IsAlternating (ladderReference L a) Q)
    (hconfined : ReferenceContactConfined (L := L) (a := a) Q) :
    IsAlternating L.limitWarp Q := by
  refine ⟨hL.warpStages (Ladder.finalStage kappa), ?_, ?_, ?_⟩
  · intro l hl hdir
    exact isFragmentOf_limitWarp_of_local hL (hQ.2.1 l hl hdir)
  · intro hfirst hglobal
    apply hQ.2.2.1 hfirst
    exact hconfined ⟨Q.initial_mem_vertexSet, hglobal⟩
  · intro t hterminal hlast hglobal
    apply hQ.2.2.2 t hterminal hlast
    exact hconfined
      ⟨Q.mem_vertexSet_of_terminal_eq hterminal, hglobal⟩

/-- Endpoint confinement is the exact condition needed for the two exposed
endpoint clauses in local-to-global alternation.  Backward links transport
without any confinement assumption. -/
theorem isAlternating_limitWarp_of_endpointConfined
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hQ : IsAlternating (ladderReference L a) Q)
    (hconfined : ReferenceEndpointConfined (L := L) (a := a) Q) :
    IsAlternating L.limitWarp Q := by
  refine ⟨hL.warpStages (Ladder.finalStage kappa), ?_, ?_, ?_⟩
  · intro l hl hdir
    exact isFragmentOf_limitWarp_of_local hL (hQ.2.1 l hl hdir)
  · intro hfirst hglobal
    exact hQ.2.2.1 hfirst (hconfined.1 hfirst hglobal)
  · intro t hterminal hlast hglobal
    exact hQ.2.2.2 t hterminal hlast
      (hconfined.2 t hterminal hlast hglobal)

/-- On a limiting owner extending a selected prefix, the backward edges of
`Q` see exactly the selected prefix and none of the future tail. -/
theorem backwardEdges_inter_edgeSet_eq_of_extends
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hQ : IsAlternating (ladderReference L a) Q)
    {p : Gamma.DPath} (hp : p ∈ L.limitWarp)
    {q : Gamma.DPath} (hq : q ∈ ladderReference L a)
    (hqp : Gamma.Extends q p) :
    Q.directionEdges .backward ∩ p.edgeSet =
      Q.directionEdges .backward ∩ q.edgeSet := by
  apply Set.Subset.antisymm
  · rintro e ⟨heBackward, hep⟩
    simp only [AltPath.directionEdges, Set.mem_iUnion] at heBackward
    obtain ⟨l, hl, hdir, hel⟩ := heBackward
    obtain ⟨r, hr, hlr⟩ := hQ.2.1 l hl hdir
    have helEnds := l.path.edgeSet_subset_support_prod hel
    have hrq := eq_of_mem_support_of_extends_limit hL hp hq hqp hr
      (hlr.1 helEnds.1) (p.edgeSet_subset_support_prod hep).1
    refine ⟨?_, ?_⟩
    · simp only [AltPath.directionEdges, Set.mem_iUnion]
      exact ⟨l, hl, hdir, hel⟩
    · rw [← hrq]
      exact hlr.2 hel
  · rintro e ⟨heBackward, heq⟩
    exact ⟨heBackward, Path.edgeSet_mono_of_extends hqp heq⟩

/-- The interval clause in local safeness transports to every limiting
reference member. -/
theorem backwardIntervals_limitWarp_of_local
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hQ : IsSafe (ladderReference L a) Q) :
    ∀ p ∈ L.limitWarp,
      IsEdgeInterval (Q.directionEdges .backward ∩ p.edgeSet) p := by
  intro p hp
  by_cases hempty : Q.directionEdges .backward ∩ p.edgeSet = ∅
  · exact Or.inl hempty
  · have hnonempty :
        (Q.directionEdges .backward ∩ p.edgeSet).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨e, heBackward, hep⟩ := hnonempty
    simp only [AltPath.directionEdges, Set.mem_iUnion] at heBackward
    obtain ⟨l, hl, hdir, hel⟩ := heBackward
    obtain ⟨q, hq, hlq⟩ := hQ.1.2.1 l hl hdir
    let qs : ladderReference L a := ⟨q, hq⟩
    have hxOwner : e.1 ∈ (limitExtension hL qs).support :=
      Gamma.support_mono_of_extends (extends_limitExtension hL qs)
        (hlq.1 ((l.path.edgeSet_subset_support_prod hel).1))
    have howner : limitExtension hL qs = p := by
      apply DWeb.IsWarp.eq_of_mem_support
        (hL.warpStages (Ladder.finalStage kappa))
        (limitExtension_mem hL qs) hp hxOwner
        (p.edgeSet_subset_support_prod hep).1
    have hqp : Gamma.Extends q p := by
      simpa only [howner] using extends_limitExtension hL qs
    have hinter := hQ.2.1 q hq
    rw [backwardEdges_inter_edgeSet_eq_of_extends hL hQ.1 hp hq hqp]
    rcases hinter with hinter | ⟨r, hrq, hinter⟩
    · exact Or.inl hinter
    · apply Or.inr
      refine ⟨r, ?_, hinter⟩
      exact ⟨hrq.1.trans (Gamma.support_mono_of_extends hqp),
        hrq.2.trans (Path.edgeSet_mono_of_extends hqp)⟩

/-- A locally safe route is globally safe once the stage geometry excludes
contacts with unseen future tails of the limiting reference. -/
theorem isSafe_limitWarp_of_contactConfined
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hQ : IsSafe (ladderReference L a) Q)
    (hconfined : ReferenceContactConfined (L := L) (a := a) Q) :
    IsSafe L.limitWarp Q := by
  refine ⟨isAlternating_limitWarp_of_contactConfined hL hQ.1 hconfined,
    backwardIntervals_limitWarp_of_local hL hQ, ?_, ?_⟩
  · rintro ⟨ray, hray⟩
    apply hQ.2.2.1
    refine ⟨ray, ?_⟩
    intro e he
    have heGlobal := hray he
    exact ⟨heGlobal.1, fun heLocal ↦
      heGlobal.2 (familyEdges_subset_limitWarp hL heLocal)⟩
  · rintro ⟨cycle, hcycle⟩
    apply hQ.2.2.2
    refine ⟨cycle, ?_⟩
    intro e he
    have heGlobal := hcycle he
    exact ⟨heGlobal.1, fun heLocal ↦
      heGlobal.2 (familyEdges_subset_limitWarp hL heLocal)⟩

/-- Local safeness transports under exposed-endpoint incidence alone.  The
interval part is controlled by exact selected-prefix incidence, while the
ray and cycle clauses are monotone under enlargement of the reference edge
set. -/
theorem isSafe_limitWarp_of_endpointConfined
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {Q : AltPath Gamma.graph}
    (hQ : IsSafe (ladderReference L a) Q)
    (hconfined : ReferenceEndpointConfined (L := L) (a := a) Q) :
    IsSafe L.limitWarp Q := by
  refine ⟨isAlternating_limitWarp_of_endpointConfined hL hQ.1 hconfined,
    backwardIntervals_limitWarp_of_local hL hQ, ?_, ?_⟩
  · rintro ⟨ray, hray⟩
    apply hQ.2.2.1
    refine ⟨ray, ?_⟩
    intro e he
    have heGlobal := hray he
    exact ⟨heGlobal.1, fun heLocal ↦
      heGlobal.2 (familyEdges_subset_limitWarp hL heLocal)⟩
  · rintro ⟨cycle, hcycle⟩
    apply hQ.2.2.2
    refine ⟨cycle, ?_⟩
    intro e he
    have heGlobal := hcycle he
    exact ⟨heGlobal.1, fun heLocal ↦
      heGlobal.2 (familyEdges_subset_limitWarp hL heLocal)⟩

/-- A finite-end local hammock is already a limiting-reference hammock when
its two common endpoints have no unseen limiting-reference incidence. -/
theorem hammock_limitWarp_vertex_of_endpoint_incidence
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u v : V} {H : Set (AltPath Gamma.graph)}
    (hH : Hammock Gamma (ladderReference L a) u (.vertex v) H)
    (hu : u ∈ Gamma.vertexSet L.limitWarp →
      u ∈ Gamma.vertexSet (ladderReference L a))
    (hv : v ∈ Gamma.vertexSet L.limitWarp →
      v ∈ Gamma.vertexSet (ladderReference L a)) :
    Hammock Gamma L.limitWarp u (.vertex v) H := by
  refine ⟨?_, hH.2⟩
  intro Q hQ
  have hQlocal := hH.1 Q hQ
  refine ⟨isSafe_limitWarp_of_endpointConfined hL hQlocal.1 ?_,
    hQlocal.2⟩
  refine ⟨?_, ?_⟩
  · intro _hfirst hglobal
    rw [hQlocal.2.1] at hglobal ⊢
    exact hu hglobal
  · intro t hterminal _hlast hglobal
    have hterminalV : Q.terminal? = some v := hQlocal.2.2
    have htv : t = v := Option.some.inj (hterminal.symm.trans hterminalV)
    subst t
    exact hv hglobal

/-- The infinite-end version needs only incidence of the common initial
endpoint; an infinite alternating path has no terminal endpoint clause. -/
theorem hammock_limitWarp_infinity_of_endpoint_incidence
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u : V} {H : Set (AltPath Gamma.graph)}
    (hH : Hammock Gamma (ladderReference L a) u .infinity H)
    (hu : u ∈ Gamma.vertexSet L.limitWarp →
      u ∈ Gamma.vertexSet (ladderReference L a)) :
    Hammock Gamma L.limitWarp u .infinity H := by
  refine ⟨?_, hH.2⟩
  intro Q hQ
  have hQlocal := hH.1 Q hQ
  refine ⟨isSafe_limitWarp_of_endpointConfined hL hQlocal.1 ?_,
    hQlocal.2⟩
  refine ⟨?_, ?_⟩
  · intro _hfirst hglobal
    rw [hQlocal.2.1] at hglobal ⊢
    exact hu hglobal
  · intro t hterminal _hlast _hglobal
    have hnone : Q.terminal? = none :=
      Q.isInfinite_iff_terminal?_eq_none.mp hQlocal.2.2
    rw [hterminal] at hnone
    simp at hnone

/-- Cardinal-sized finite-end hammocks transfer without discarding any
members once their common endpoints satisfy selected/global incidence. -/
theorem hasHammockCard_limitWarp_vertex_of_endpoint_incidence
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u v : V} {rho : Cardinal.{u}}
    (hH : HasHammockCard Gamma (ladderReference L a) u (.vertex v) rho)
    (hu : u ∈ Gamma.vertexSet L.limitWarp →
      u ∈ Gamma.vertexSet (ladderReference L a))
    (hv : v ∈ Gamma.vertexSet L.limitWarp →
      v ∈ Gamma.vertexSet (ladderReference L a)) :
    HasHammockCard Gamma L.limitWarp u (.vertex v) rho := by
  obtain ⟨H, hHammock, hcard⟩ := hH
  exact ⟨H, hammock_limitWarp_vertex_of_endpoint_incidence hL hHammock hu hv,
    hcard⟩

/-- Cardinal-sized infinite-end hammocks transfer under the common initial
endpoint incidence condition. -/
theorem hasHammockCard_limitWarp_infinity_of_endpoint_incidence
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u : V} {rho : Cardinal.{u}}
    (hH : HasHammockCard Gamma (ladderReference L a) u .infinity rho)
    (hu : u ∈ Gamma.vertexSet L.limitWarp →
      u ∈ Gamma.vertexSet (ladderReference L a)) :
    HasHammockCard Gamma L.limitWarp u .infinity rho := by
  obtain ⟨H, hHammock, hcard⟩ := hH
  exact ⟨H, hammock_limitWarp_infinity_of_endpoint_incidence hL hHammock hu,
    hcard⟩

/-- A locally certified imaginary edge is a globally certified imaginary
edge under endpoint incidence; no finite-character assumption on the global
limiting reference is used. -/
theorem isImaginaryEdge_limitWarp_of_endpoint_incidence
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u v : V} {kappa0 : Cardinal.{u}}
    (hlocal : IsImaginaryEdge Gamma (ladderReference L a) kappa0 u v)
    (hu : u ∈ Gamma.vertexSet L.limitWarp →
      u ∈ Gamma.vertexSet (ladderReference L a))
    (hv : v ∈ Gamma.vertexSet L.limitWarp →
      v ∈ Gamma.vertexSet (ladderReference L a)) :
    IsImaginaryEdge Gamma L.limitWarp kappa0 u v :=
  hasHammockCard_limitWarp_vertex_of_endpoint_incidence hL hlocal hu hv

/-- Local popularity transfers by the same endpoint argument; the persistent
branch is unchanged. -/
theorem isPopular_limitWarp_of_endpoint_incidence
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {persistent : Set V} {u : V} {kappa0 : Cardinal.{u}}
    (hlocal : IsPopular Gamma (ladderReference L a) persistent kappa0 u)
    (hu : u ∈ Gamma.vertexSet L.limitWarp →
      u ∈ Gamma.vertexSet (ladderReference L a)) :
    IsPopular Gamma L.limitWarp persistent kappa0 u := by
  rcases hlocal with hpersistent | hlarge
  · exact Or.inl hpersistent
  · exact Or.inr
      (hasHammockCard_limitWarp_infinity_of_endpoint_incidence hL hlarge hu)

/-- Discarding at most `kappa` nonconfined routes from a local hammock of
size `kappa+` leaves a global-reference hammock of the same size. -/
theorem hasHammockCard_limitWarp_of_bad_le
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u : V} {e : AltEnd V} {kappa0 : Cardinal.{u}}
    (hkappa0 : aleph0 ≤ kappa0)
    (hlarge : HasHammockCard Gamma (ladderReference L a) u e (succ kappa0))
    (hbad : ∀ K : Set (AltPath Gamma.graph),
      Hammock Gamma (ladderReference L a) u e K →
      #{Q : K // ¬ ReferenceContactConfined (L := L) (a := a) Q.1} ≤
        kappa0) :
    HasHammockCard Gamma L.limitWarp u e (succ kappa0) := by
  obtain ⟨K, hK, hKcard⟩ := hlarge
  let bad : Set (AltPath Gamma.graph) :=
    {Q | Q ∈ K ∧ ¬ ReferenceContactConfined (L := L) (a := a) Q}
  let good : Set (AltPath Gamma.graph) := K \ bad
  have hgoodK : good ⊆ K := Set.sdiff_subset
  have hgoodLocal : Hammock Gamma (ladderReference L a) u e good :=
    hK.subset hgoodK
  have hgoodGlobal : Hammock Gamma L.limitWarp u e good := by
    refine ⟨?_, hgoodLocal.2⟩
    intro Q hQ
    have hQlocal := hgoodLocal.1 Q hQ
    have hQconfined : ReferenceContactConfined (L := L) (a := a) Q := by
      by_contra hnot
      exact hQ.2 ⟨hQ.1, hnot⟩
    exact ⟨isSafe_limitWarp_of_contactConfined hL hQlocal.1 hQconfined,
      hQlocal.2⟩
  have hbadcard : #bad ≤ kappa0 := by
    let f : bad →
        {Q : K // ¬ ReferenceContactConfined (L := L) (a := a) Q.1} :=
      fun Q ↦ ⟨⟨Q.1, Q.2.1⟩, Q.2.2⟩
    exact (Cardinal.mk_le_of_injective (f := f) (by
      intro Q R h
      exact Subtype.ext
        (congrArg (fun x ↦ (x.1 : AltPath Gamma.graph)) h))).trans
      (hbad K hK)
  have hgoodcard : #good = succ kappa0 := by
    apply le_antisymm
    · rw [← hKcard]
      exact Cardinal.mk_le_mk_of_subset hgoodK
    · apply le_of_not_gt
      intro hlt
      have hgoodle : #good ≤ kappa0 := lt_succ_iff.mp hlt
      have hKle : #K ≤ kappa0 := by
        calc
          #K ≤ #(K \ bad : Set (AltPath Gamma.graph)) + #bad :=
            Cardinal.le_mk_sdiff_add_mk K bad
          _ = #good + #bad := rfl
          _ ≤ kappa0 :=
            Cardinal.add_le_of_le hkappa0 hgoodle hbadcard
      have hs : succ kappa0 ≤ kappa0 := by
        simpa only [hKcard] using hKle
      exact (not_le_of_gt (lt_succ kappa0)) hs
  exact ⟨good, hgoodGlobal, hgoodcard⟩

/-- Pairwise-disjoint hammock interiors inject every nonconfined route into
any small carrier which witnesses one interior contact for that route.  This
is the cardinal bookkeeping behind the source's deletion of the bad global
reference components. -/
theorem mk_nonconfined_hammock_members_le_of_small_contactCarrier
    {u : V} {e : AltEnd V} {kappa0 : Cardinal.{u}}
    (hkappa0 : aleph0 ≤ kappa0)
    (K : Set (AltPath Gamma.graph))
    (hK : Hammock Gamma (ladderReference L a) u e K)
    (P : Set Gamma.DPath) (hP : #P ≤ kappa0)
    (hcontact : ∀ Q ∈ K,
      ¬ ReferenceContactConfined (L := L) (a := a) Q →
      ∃ x ∈ hammockInterior u e Q, x ∈ Gamma.vertexSet P) :
    #{Q : K // ¬ ReferenceContactConfined (L := L) (a := a) Q.1} ≤
      kappa0 := by
  let Bad := {Q : K //
    ¬ ReferenceContactConfined (L := L) (a := a) Q.1}
  have hwitness (Q : Bad) :
      ∃ x ∈ hammockInterior u e Q.1.1, x ∈ Gamma.vertexSet P :=
    hcontact Q.1.1 Q.1.2 Q.2
  let contact : Bad → {x // x ∈ Gamma.vertexSet P} := fun Q ↦
    ⟨Classical.choose (hwitness Q),
      (Classical.choose_spec (hwitness Q)).2⟩
  have hinjective : Function.Injective contact := by
    intro Q R hQR
    apply Subtype.ext
    apply Subtype.ext
    by_contra hne
    have hdisjoint := hK.2 Q.1.2 R.1.2 hne
    have hQinterior := (Classical.choose_spec (hwitness Q)).1
    have hRinterior := (Classical.choose_spec (hwitness R)).1
    have hvertex := congrArg Subtype.val hQR
    change Classical.choose (hwitness Q) =
      Classical.choose (hwitness R) at hvertex
    apply Set.disjoint_left.1 hdisjoint hQinterior
    rw [hvertex]
    exact hRinterior
  exact (Cardinal.mk_le_of_injective hinjective).trans
    (CardinalInduction.HalfwayFrontierHeight.mk_vertexSet_le_of_mk_family_le
      hkappa0 P hP)

/-- Small bad-reference carrier form of the hammock transfer. -/
theorem hasHammockCard_limitWarp_of_small_contactCarrier
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u : V} {e : AltEnd V} {kappa0 : Cardinal.{u}}
    (hkappa0 : aleph0 ≤ kappa0)
    (hlarge : HasHammockCard Gamma (ladderReference L a) u e (succ kappa0))
    (P : Set Gamma.DPath) (hP : #P ≤ kappa0)
    (hcontact : ∀ (K : Set (AltPath Gamma.graph))
      (_hK : Hammock Gamma (ladderReference L a) u e K)
      (Q : AltPath Gamma.graph), Q ∈ K →
      ¬ ReferenceContactConfined (L := L) (a := a) Q →
      ∃ x ∈ hammockInterior u e Q, x ∈ Gamma.vertexSet P) :
    HasHammockCard Gamma L.limitWarp u e (succ kappa0) := by
  apply hasHammockCard_limitWarp_of_bad_le hL hkappa0 hlarge
  intro K hK
  exact mk_nonconfined_hammock_members_le_of_small_contactCarrier
    hkappa0 K hK P hP (hcontact K hK)

/-- Imaginary edges certified locally remain imaginary for the limiting
reference once only `kappa` members of each witnessing hammock can meet an
unseen future tail. -/
theorem isImaginaryEdge_limitWarp_of_bad_le
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {u v : V} {kappa0 : Cardinal.{u}}
    (hkappa0 : aleph0 ≤ kappa0)
    (hlocal : IsImaginaryEdge Gamma (ladderReference L a) kappa0 u v)
    (hbad : ∀ K : Set (AltPath Gamma.graph),
      Hammock Gamma (ladderReference L a) u (.vertex v) K →
      #{Q : K // ¬ ReferenceContactConfined (L := L) (a := a) Q.1} ≤
        kappa0) :
    IsImaginaryEdge Gamma L.limitWarp kappa0 u v :=
  hasHammockCard_limitWarp_of_bad_le hL hkappa0 hlocal hbad

/-- The corresponding popularity transport, with the persistent-set branch
unchanged and the infinite-hammock branch transferred by the same discard. -/
theorem isPopular_limitWarp_of_bad_le
    (hL : DWeb.KappaLadder.Deferred.HalfwayGeometry L)
    {persistent : Set V} {u : V} {kappa0 : Cardinal.{u}}
    (hkappa0 : aleph0 ≤ kappa0)
    (hlocal : IsPopular Gamma (ladderReference L a) persistent kappa0 u)
    (hbad : ∀ K : Set (AltPath Gamma.graph),
      Hammock Gamma (ladderReference L a) u .infinity K →
      #{Q : K // ¬ ReferenceContactConfined (L := L) (a := a) Q.1} ≤
        kappa0) :
    IsPopular Gamma L.limitWarp persistent kappa0 u := by
  rcases hlocal with hpersistent | hlarge
  · exact Or.inl hpersistent
  · exact Or.inr
      (hasHammockCard_limitWarp_of_bad_le hL hkappa0 hlarge hbad)

#print axioms isAlternating_limitWarp_of_contactConfined
#print axioms isAlternating_limitWarp_of_endpointConfined
#print axioms backwardIntervals_limitWarp_of_local
#print axioms isSafe_limitWarp_of_contactConfined
#print axioms isSafe_limitWarp_of_endpointConfined
#print axioms hammock_limitWarp_vertex_of_endpoint_incidence
#print axioms hammock_limitWarp_infinity_of_endpoint_incidence
#print axioms isImaginaryEdge_limitWarp_of_endpoint_incidence
#print axioms isPopular_limitWarp_of_endpoint_incidence
#print axioms hasHammockCard_limitWarp_of_bad_le
#print axioms mk_nonconfined_hammock_members_le_of_small_contactCarrier
#print axioms hasHammockCard_limitWarp_of_small_contactCarrier
#print axioms isImaginaryEdge_limitWarp_of_bad_le
#print axioms isPopular_limitWarp_of_bad_le

end ladderReference
end Erdos599.Blueprint.LinkageBlueprint
