/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayDeferredReferenceRoofIncidence
import ErdosProblems.Erdos599.HalfwayClosedEndpointPairing

/-!
# Reclassifying a selected-stage contact against the limiting reference

The finite selected reference is only a prefix family of the possibly
infinite limiting warp.  Consequently a selected-reference imaginary edge
need not remain imaginary for the limiting reference when one of its exposed
endpoints lies on an inessential stage component.

The source construction has a precise repair: the carrier of those
inessential components is `kappa`-small and can be inserted into the closing
seed.  A contact whose endpoint lies in that carrier is a genuine global
reference contact and its already-present real forward links are retained;
one must not demand that the global owner's future tail lie in the local
roof.  If neither endpoint lies there, the large local hammock transfers to
the limiting reference.  The theorems below implement exactly this case
split; no finite-character assertion is made about the limiting warp.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

namespace ClubStageGeometry

variable (C : ClubStageGeometry Gamma Y kappa (succ kappa))

/-- Every accumulated-stage component has a continuation in the limiting
warp.  Unlike `ladderReference.limitExtension`, this also applies to the
inessential components removed by selected-reference trimming. -/
theorem exists_limitWarp_extension_of_mem_warpAt
    {p : Gamma.DPath} (hp : p ∈ C.ladder.warpAt C.newStage) :
    ∃ q ∈ C.ladder.limitWarp, Gamma.Extends p q := by
  have hlimit : Order.IsSuccLimit (succ kappa).ord :=
    Cardinal.isSuccLimit_ord C.legal.regular.aleph0_le
  exact C.legal.limitStages.grows_to_limit
    (Ladder.finalStage (succ kappa)) hlimit
    ⟨C.newStage.1, C.newStage.2⟩ p hp

/-- Every vertex of the literal stage exception is genuinely a vertex of
the global limiting reference. -/
theorem limitingReferenceException_subset_limitWarp :
    C.limitingReferenceException ⊆
      Gamma.vertexSet C.ladder.limitWarp := by
  rintro x ⟨p, hp, hxp⟩
  obtain ⟨q, hq, hpq⟩ :=
    C.exists_limitWarp_extension_of_mem_warpAt hp.1
  exact ⟨q, hq, Gamma.support_mono_of_extends hpq hxp⟩

/-- The exceptional carrier is contained in the roof used by the concrete
closing transaction, so it may soundly be adjoined to that transaction's
seed. -/
theorem limitingReferenceException_subset_outerRoof :
    C.limitingReferenceException ⊆ C.outerRoof := by
  intro x hx
  have hxStage : x ∈ Gamma.vertexSet
      (C.ladder.warpAt C.newStage) := by
    exact ⟨hx.choose, hx.choose_spec.1.1, hx.choose_spec.2⟩
  have hxRoof :=
    DWeb.KappaLadder.Deferred.vertexSet_warpAt_subset_roof_terminalFrontier
      C.legal C.newStage hxStage
  simpa only [outerRoof, newSlice,
    C.ladder.frontier_eq_essential_terminalFrontier
      C.legal.roofsSourceAtStages,
    Gamma.roof_essential] using hxRoof

/-- Essential selected-reference paths and the discarded inessential paths
have disjoint carriers, by warp disjointness at the selected stage. -/
theorem selectedReference_disjoint_limitingReferenceException :
    Disjoint (Gamma.vertexSet C.selectedReference)
      C.limitingReferenceException := by
  rw [Set.disjoint_left]
  rintro x ⟨q, hq, hxq⟩ ⟨p, hp, hxp⟩
  have hpq : p ≠ q := by
    intro hpq
    subst p
    exact hp.2 hq
  exact Set.disjoint_left.1
    (C.legal.warpStages (Ladder.Stage.toExtended C.newStage)
      hp.1 hq.1 hpq) hxp hxq

/-- In particular the selected frontier itself avoids the exceptional
carrier.  This discharges global-reference transport automatically for
9.30 edges whose exposed endpoints lie on the new slice. -/
theorem newSlice_disjoint_limitingReferenceException :
    Disjoint C.newSlice C.limitingReferenceException := by
  apply Disjoint.mono ?_ Set.Subset.rfl
    C.selectedReference_disjoint_limitingReferenceException
  intro x hx
  rw [← C.terminalFrontier_selectedReference] at hx
  obtain ⟨q, hq, hqx⟩ := hx
  exact ⟨q, hq, Gamma.terminal_mem_support hqx⟩

/-- The source-faithful closing seed: retain the caller's concrete seed and
adjoin all inessential selected-stage reference components. -/
def withLimitingReferenceException (seed : Set V) : Set V :=
  seed ∪ C.limitingReferenceException

theorem seed_subset_withLimitingReferenceException (seed : Set V) :
    seed ⊆ C.withLimitingReferenceException seed :=
  Set.subset_union_left

theorem exception_subset_withLimitingReferenceException (seed : Set V) :
    C.limitingReferenceException ⊆
      C.withLimitingReferenceException seed :=
  Set.subset_union_right

theorem mk_withLimitingReferenceException_le {seed : Set V}
    (hseed : #seed ≤ kappa) :
    #(C.withLimitingReferenceException seed) ≤ kappa := by
  refine (Cardinal.mk_union_le _ _).trans ?_
  exact Cardinal.add_le_of_le C.capacity_infinite hseed
    C.mk_limitingReferenceException_le

theorem withLimitingReferenceException_subset_outerRoof {seed : Set V}
    (hseed : seed ⊆ C.outerRoof) :
    C.withLimitingReferenceException seed ⊆ C.outerRoof :=
  Set.union_subset hseed C.limitingReferenceException_subset_outerRoof

private theorem selectedReference_vertex_mem_limitWarp
    {x : V} (hx : x ∈ Gamma.vertexSet C.selectedReference) :
    x ∈ Gamma.vertexSet C.ladder.limitWarp := by
  obtain ⟨p, hp, hxp⟩ := hx
  let ps : ladderReference C.ladder C.newStage := ⟨p, hp⟩
  exact ⟨ladderReference.limitExtension C.legal ps,
    ladderReference.limitExtension_mem C.legal ps,
    Gamma.support_mono_of_extends
      (ladderReference.extends_limitExtension C.legal ps) hxp⟩

private theorem pair_disjoint_exception_of_not_mem
    {u v : V} (hu : u ∉ C.limitingReferenceException)
    (hv : v ∉ C.limitingReferenceException) :
    Disjoint ({u, v} : Set V) C.limitingReferenceException := by
  rw [Set.disjoint_left]
  intro x hx hxException
  rcases hx with rfl | hx
  · exact hu hxException
  · have hxv : x = v := Set.mem_singleton_iff.1 hx
    exact hv (hxv ▸ hxException)

/-- A genuine limiting-reference owner of one exposed endpoint.  No claim is
made that its future tail lies in the stage-local closing set: that would be
false in general because the tail can leave the selected roof.  Covered
contact pieces retain only ambient real forward edges, for which literal
global-owner incidence is the exact required datum. -/
structure LimitingReferenceEndpointOwner (x : V) where
  path : Gamma.DPath
  mem : path ∈ C.ladder.limitWarp
  contains : x ∈ path.support

/-- Exact three-way result of reclassifying a finite selected-stage contact
against the limiting reference. -/
inductive LimitingFiniteContactClassification
    (X : Set V) (Q : AltPath Gamma.graph) (u v : V) : Type u
  | imaginary : IsImaginaryEdge Gamma C.ladder.limitWarp kappa u v →
      LimitingFiniteContactClassification X Q u v
  | initialCovered : LimitingReferenceEndpointOwner C u →
      LimitingFiniteContactClassification X Q u v
  | terminalCovered : LimitingReferenceEndpointOwner C v →
      LimitingFiniteContactClassification X Q u v

/-- Exact two-way result for an infinite selected-stage contact. -/
inductive LimitingInfiniteContactClassification
    (X persistent : Set V) (Q : AltPath Gamma.graph) (u : V) : Type u
  | popular : IsPopular Gamma C.ladder.limitWarp persistent kappa u →
      LimitingInfiniteContactClassification X persistent Q u
  | initialCovered : LimitingReferenceEndpointOwner C u →
      LimitingInfiniteContactClassification X persistent Q u

private theorem limitingReferenceEndpointOwner_of_exception
    {x : V} (hx : x ∈ C.limitingReferenceException) :
    Nonempty (LimitingReferenceEndpointOwner C x) := by
  have hxGlobal := C.limitingReferenceException_subset_limitWarp hx
  obtain ⟨p, hp, hxp⟩ := hxGlobal
  exact ⟨{
    path := p
    mem := hp
    contains := hxp }⟩

/-- A selected-reference owner has a unique global continuation containing
the same exposed endpoint. -/
theorem limitingReferenceEndpointOwner_of_selected
    {x : V} {p : Gamma.DPath} (hp : p ∈ C.selectedReference)
    (hxp : x ∈ p.support) :
    Nonempty (LimitingReferenceEndpointOwner C x) := by
  let ps : ladderReference C.ladder C.newStage := ⟨p, hp⟩
  let q := ladderReference.limitExtension C.legal ps
  have hq : q ∈ C.ladder.limitWarp :=
    ladderReference.limitExtension_mem C.legal ps
  have hpq : Gamma.Extends p q :=
    ladderReference.extends_limitExtension C.legal ps
  have hxq : x ∈ q.support := Gamma.support_mono_of_extends hpq hxp
  exact ⟨{
    path := q
    mem := hq
    contains := hxq }⟩

/-- Reclassify one locally imaginary finite occurrence.  Exception
endpoints are genuine global reference contacts; only an exception-free
pair is compressed to a global imaginary edge. -/
theorem globalizeLocalImaginary
    {X : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {Q : AltPath Gamma.graph} {u v : V}
    (hlocal : IsImaginaryEdge Gamma C.selectedReference kappa u v) :
    Nonempty (LimitingFiniteContactClassification C X Q u v) := by
  by_cases hu : u ∈ C.limitingReferenceException
  · exact ⟨.initialCovered
      (C.limitingReferenceEndpointOwner_of_exception hu).some⟩
  by_cases hv : v ∈ C.limitingReferenceException
  · exact ⟨.terminalCovered
      (C.limitingReferenceEndpointOwner_of_exception hv).some⟩
  · exact ⟨.imaginary
      (C.isImaginaryEdge_limitWarp_of_endpoints_disjoint_exception
        hSafeRoof hlocal
        (C.pair_disjoint_exception_of_not_mem hu hv))⟩

/-- Infinite occurrence version of the same source-faithful reclassification.
If the exposed initial is exceptional, its global owner is retained;
otherwise local popularity transfers to the limiting reference. -/
theorem globalizeLocalPopular
    {X persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    {Q : AltPath Gamma.graph} {u : V}
    (hlocal : IsPopular Gamma C.selectedReference persistent kappa u) :
    Nonempty (LimitingInfiniteContactClassification C X persistent Q u) := by
  by_cases hu : u ∈ C.limitingReferenceException
  · exact ⟨.initialCovered
      (C.limitingReferenceEndpointOwner_of_exception hu).some⟩
  · exact ⟨.popular
      (C.isPopular_limitWarp_of_endpoint_disjoint_exception
        hSafeRoof hlocal hu)⟩

namespace LimitingFiniteContactClassification

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {X : Set V} {Q : AltPath Gamma.graph} {u v : V}

/-- Only the exception-free imaginary branch contributes a new shortcut.
Covered branches keep the occurrence's already-existing forward edges. -/
def shortcutEdges
    (K : LimitingFiniteContactClassification C X Q u v) : Set (V × V) :=
  match K with
  | .imaginary _ => {(u, v)}
  | .initialCovered _ => ∅
  | .terminalCovered _ => ∅

def retainedEdges
    (K : LimitingFiniteContactClassification C X Q u v) : Set (V × V) :=
  match K with
  | .imaginary _ => {(u, v)}
  | .initialCovered _ => Q.directionEdges .forward
  | .terminalCovered _ => Q.directionEdges .forward

private theorem directionEdges_subset_edgeSet
    (Q : AltPath Gamma.graph) (d : Direction) :
    Q.directionEdges d ⊆ Q.edgeSet := by
  intro e he
  simp only [AltPath.directionEdges, Set.mem_iUnion] at he
  obtain ⟨l, hl, _hd, hel⟩ := he
  rw [Q.edgeSet_eq_iUnion_links]
  simp only [Set.mem_iUnion]
  exact ⟨l, hl, hel⟩

/-- Every retained edge is honest in the global imaginary graph: shortcuts
carry the transferred global hammock proof, while covered branches use
literal graph edges. -/
theorem retainedEdges_subset_imaginaryGraph
    (K : LimitingFiniteContactClassification C X Q u v) :
    K.retainedEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  cases K with
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

theorem shortcutEdges_subset_imaginaryGraph
    (K : LimitingFiniteContactClassification C X Q u v) :
    K.shortcutEdges ⊆
      {e | (imaginaryGraph Gamma C.ladder.limitWarp kappa).Adj e.1 e.2} := by
  cases K with
  | imaginary h =>
      rintro e rfl
      exact Or.inr h
  | initialCovered _ => simp [shortcutEdges]
  | terminalCovered _ => simp [shortcutEdges]

/-- Exact merge law used by the literal-contact transaction. -/
theorem retainedEdges_subset_originalForward_union_shortcut
    (K : LimitingFiniteContactClassification C X Q u v) :
    K.retainedEdges ⊆ Q.directionEdges .forward ∪ K.shortcutEdges := by
  cases K with
  | imaginary _ =>
      exact Set.subset_union_right
  | initialCovered _ =>
      exact Set.subset_union_left
  | terminalCovered _ =>
      exact Set.subset_union_left

end LimitingFiniteContactClassification

namespace LimitingInfiniteContactClassification

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {X persistent : Set V} {Q : AltPath Gamma.graph} {u : V}

/-- A covered infinite tail contributes only its already-present forward
real edges.  A globally popular tail contributes vertex data and no edge. -/
def retainedEdges
    (K : LimitingInfiniteContactClassification C X persistent Q u) :
    Set (V × V) :=
  match K with
  | .popular _ => ∅
  | .initialCovered _ => Q.directionEdges .forward

theorem retainedEdges_subset_originalForward
    (K : LimitingInfiniteContactClassification C X persistent Q u) :
    K.retainedEdges ⊆ Q.directionEdges .forward := by
  cases K with
  | popular _ => exact Set.empty_subset _
  | initialCovered _ => exact Set.Subset.rfl

end LimitingInfiniteContactClassification

/-! ## Reclassifying an actual endpoint pairing -/

/-- One finite endpoint witness together with its truthful limiting-reference
classification. -/
structure LimitingFiniteEndpointWitness
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (Zf : FracturedWarp Gamma) (X before innerRoof outerRoof : Set V)
    (u v : V) where
  witness : FiniteClosedEndpointWitness
    (Gamma := Gamma) (Y := C.selectedReference)
    X before innerRoof outerRoof u v
  classification : LimitingFiniteContactClassification
    C X witness.path u v

/-- Infinite counterpart of `LimitingFiniteEndpointWitness`. -/
structure LimitingInfiniteEndpointWitness
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (Zf : FracturedWarp Gamma) (X before innerRoof outerRoof persistent : Set V)
    (u : V) where
  witness : InfiniteClosedEndpointWitness
    (Gamma := Gamma) (Y := C.selectedReference)
    X before innerRoof outerRoof u
  classification : LimitingInfiniteContactClassification
    C X persistent witness.path u

/-- The endpoint map selected by the finite stage, with each concrete local
witness reclassified for the global limiting reference.  Finite endpoint
injectivity is unchanged. -/
structure LimitingClosedEndpointPairing
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    (Zf : FracturedWarp Gamma)
    (X before innerRoof outerRoof persistent : Set V) where
  endpoint :
    {z : V // z ∈ Gamma.initialSet Zf.paths \
      Gamma.initialSet C.selectedReference} → Option V
  finite_mem_terminal : ∀ s v, endpoint s = some v →
    v ∈ Gamma.terminalFrontier Zf.paths
  finite_injective : ∀ ⦃s t v⦄,
    endpoint s = some v → endpoint t = some v → s = t
  finite_witness : ∀ s v, endpoint s = some v →
    Nonempty (LimitingFiniteEndpointWitness C Zf X before innerRoof outerRoof
      s.1 v)
  infinite_witness : ∀ s, endpoint s = none →
    Nonempty (LimitingInfiniteEndpointWitness C Zf X before innerRoof
      outerRoof persistent s.1)

/-- Reclassify the exact local Claim-2 endpoint pairing without assuming
finite character of the limiting reference and without pretending that the
resulting relation is identical to the local shortcut relation. -/
noncomputable def globalizeClosedEndpointPairing
    (C : ClubStageGeometry Gamma Y kappa (succ kappa))
    {Zf : FracturedWarp Gamma}
    {X before innerRoof outerRoof persistent : Set V}
    (hSafeRoof : EligibleHammocksContainedInRoof Gamma C.selectedReference
      C.before C.innerRoof C.outerRoof)
    (A : ClosedEndpointPairing
      (Gamma := Gamma) (Y := C.selectedReference)
      Zf X before innerRoof outerRoof)
    (hclosed : HammockClosedUpTo Gamma C.selectedReference X
      before innerRoof outerRoof kappa) :
    LimitingClosedEndpointPairing C Zf X before innerRoof outerRoof
      persistent where
  endpoint := A.endpoint
  finite_mem_terminal := A.finite_mem_terminal
  finite_injective := A.finite_injective
  finite_witness := by
    intro s v hsv
    let Q := (A.finite_witness s v hsv).some
    have hlocal : IsImaginaryEdge Gamma C.selectedReference kappa s.1 v :=
      isImaginaryEdge_of_closed hclosed Q.eligible Q.safe Q.starts_at
        Q.ends_at Q.interior_disjoint Q.outside
    exact ⟨{
      witness := Q
      classification := (C.globalizeLocalImaginary hSafeRoof
        (Q := Q.path) hlocal).some }⟩
  infinite_witness := by
    intro s hs
    let Q := (A.infinite_witness s hs).some
    have hlocal : IsPopular Gamma C.selectedReference persistent kappa s.1 :=
      isPopular_of_closed_infinite hclosed Q.eligible Q.safe Q.starts_at
        Q.infinite Q.interior_disjoint Q.outside
    exact ⟨{
      witness := Q
      classification := (C.globalizeLocalPopular hSafeRoof
        (Q := Q.path) hlocal).some }⟩

#print axioms exists_limitWarp_extension_of_mem_warpAt
#print axioms limitingReferenceException_subset_limitWarp
#print axioms limitingReferenceException_subset_outerRoof
#print axioms selectedReference_disjoint_limitingReferenceException
#print axioms newSlice_disjoint_limitingReferenceException
#print axioms mk_withLimitingReferenceException_le
#print axioms withLimitingReferenceException_subset_outerRoof
#print axioms limitingReferenceEndpointOwner_of_selected
#print axioms globalizeLocalImaginary
#print axioms globalizeLocalPopular
#print axioms LimitingFiniteContactClassification.retainedEdges_subset_imaginaryGraph
#print axioms LimitingFiniteContactClassification.retainedEdges_subset_originalForward_union_shortcut
#print axioms globalizeClosedEndpointPairing

end ClubStageGeometry
end Erdos599.Blueprint.LinkageBlueprint
