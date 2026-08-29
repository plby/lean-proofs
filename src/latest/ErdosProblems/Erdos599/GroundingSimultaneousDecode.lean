/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingControlledAssembly
import ErdosProblems.Erdos599.GroundingConcreteAvoidance
import ErdosProblems.Erdos599.GroundingAssertion819
import ErdosProblems.Erdos599.GroundingAssertion819Chronology
import ErdosProblems.Erdos599.GroundingGroundedFans
import ErdosProblems.Erdos599.GroundingFragmentAssertion820
import ErdosProblems.Erdos599.GroundingWholeSwitchBoundary
import ErdosProblems.Erdos599.SafeSwitchingAssembly
import ErdosProblems.Erdos599.RayCompatibleRelationDecomposition

/-!
# Simultaneous decoding of the Section 8 grounding routes

This file supplies the relation-decomposition layer needed after the
pairwise-compatible auxiliary routes have been selected.  Unlike the finite
safe-switching theorem, the grounding switch starts from a limiting warp and
may therefore retain one-way infinite components.  Accordingly the main
decomposition theorem below assumes only that the switched relation has no
directed cycle and no reverse-directed ray.  Forward rays are allowed and
become ray members of the realizing warp.

The final definitions package the literal simultaneous symmetric difference
of all decoded auxiliary routes.  Establishing its local bi-uniqueness and
the two forbidden-component properties is the geometric content of
Assertion 8.22; once those facts are available, the exact realizing warp is
constructed here without any finite-character assumption.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath RelationDecomposition

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace RelationDecomposition

end RelationDecomposition

end Alternating

open DirectedPath

variable {V : Type u} {Gamma : DWeb V}

namespace PopularAuxiliary.Input

variable {I : Type u} (L : PopularAuxiliary.Input Gamma I)

/-! ## Literal simultaneous decoded switching data -/

/-- The union of the original-web routes encoded by a whole auxiliary path
family.  This is the simultaneous, rather than iterated, decoding used in
Assertion 8.22. -/
def decodedFamilyRouteEdges
    (P : Set (FinitePath L.lambda.graph)) : Set (V × V) :=
  ⋃ p ∈ P, L.decodedRouteEdges p

theorem decodedFamilyRouteEdges_subset_adj
    (P : Set (FinitePath L.lambda.graph)) :
    L.decodedFamilyRouteEdges P ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  simp only [decodedFamilyRouteEdges, Set.mem_iUnion] at he
  obtain ⟨p, _hp, he⟩ := he
  exact L.decodedRouteEdges_subset_adj p he

/-- The literal simultaneous symmetric difference of the limiting ladder
warp with every decoded route. -/
def decodedFamilySwitchedEdges
    (P : Set (FinitePath L.lambda.graph)) : Set (V × V) :=
  Alternating.edgeSymmDiff (Alternating.familyEdges L.ladder.paths)
    (L.decodedFamilyRouteEdges P)

theorem decodedFamilySwitchedEdges_subset_adj
    (P : Set (FinitePath L.lambda.graph)) :
    L.decodedFamilySwitchedEdges P ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  rcases he with he | he
  · exact Alternating.familyEdges_subset_adj L.ladder.paths he.1
  · exact L.decodedFamilyRouteEdges_subset_adj P he.1

/-- Raw graph-level data of the simultaneous Section 8 switch. -/
def decodedFamilySwitchData
    (P : Set (FinitePath L.lambda.graph)) : Alternating.SwitchData Gamma where
  edges := L.decodedFamilySwitchedEdges P
  edges_in_graph := L.decodedFamilySwitchedEdges_subset_adj P
  isolated := Alternating.isolatedVertices L.ladder.paths

@[simp] theorem decodedFamilySwitchData_edges
    (P : Set (FinitePath L.lambda.graph)) :
    (L.decodedFamilySwitchData P).edges = L.decodedFamilySwitchedEdges P :=
  rfl

@[simp] theorem decodedFamilySwitchData_isolated
    (P : Set (FinitePath L.lambda.graph)) :
    (L.decodedFamilySwitchData P).isolated =
      Alternating.isolatedVertices L.ladder.paths :=
  rfl

/-- The exact component conditions which turn a literal simultaneous switch
relation into an honest warp.  The conditions mention the actual switched
edge relation; no finite-character or surrogate path-family assumption is
hidden in this package. -/
structure DecodedFamilyCompatible
    (P : Set (FinitePath L.lambda.graph)) : Prop where
  biUnique : Relator.BiUnique
    (fun x y ↦ (x, y) ∈ L.decodedFamilySwitchedEdges P)
  noDirectedCycle :
    ¬ Alternating.ContainsDirectedCycle
      (L.decodedFamilySwitchedEdges P)
  noReverseDirectedRay :
    ¬ Alternating.ContainsReverseDirectedRay
      (L.decodedFamilySwitchedEdges P)
  isolated_nonincident : ∀ x ∈ Alternating.isolatedVertices L.ladder.paths, ∀ y,
    (x, y) ∉ L.decodedFamilySwitchedEdges P ∧
      (y, x) ∉ L.decodedFamilySwitchedEdges P

/-- Simultaneously compatible decoded routes have an exact realizing warp,
including precisely the singleton components of the original limiting
warp.  Forward rays are retained. -/
theorem DecodedFamilyCompatible.exists_realization
    {P : Set (FinitePath L.lambda.graph)}
    (h : L.DecodedFamilyCompatible P) :
    ∃ W : Set Gamma.DPath,
      Alternating.SwitchData.RealizedBy (L.decodedFamilySwitchData P) W := by
  obtain ⟨W, hW, hE, hI⟩ :=
    Alternating.RayCompatibleRelationDecomposition.exists_warp_realizing_biUnique_with_isolated
      Gamma (L.decodedFamilySwitchedEdges P)
      (Alternating.isolatedVertices L.ladder.paths)
      (L.decodedFamilySwitchedEdges_subset_adj P) h.biUnique
      h.noDirectedCycle h.noReverseDirectedRay h.isolated_nonincident
  exact ⟨W, hW, hE, hI⟩

end PopularAuxiliary.Input

namespace GroundingSimultaneousDecode

open PopularAuxiliary.Input PopularGroundingBridge

variable {I : Type u}

/-! ## Finitely many ladder components met by one auxiliary path -/

/-- Limiting ladder components whose full auxiliary trace is met by a
finite auxiliary path. -/
def metLadderPaths (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) : Set Gamma.DPath :=
  {Y | Y ∈ L.ladder.paths ∧
    (q.support ∩ PopularSwitching.ladderTrace L Y).Nonempty}

/-- Traces of distinct members of the limiting ladder warp are disjoint.
This includes both old-vertex gadgets and directed-edge gadgets. -/
theorem ladderTrace_pairwiseDisjoint
    (L : PopularAuxiliary.Input Gamma I) :
    L.ladder.paths.PairwiseDisjoint
      (PopularSwitching.ladderTrace L) := by
  intro p hp q hq hpq
  change Disjoint (PopularSwitching.ladderTrace L p)
    (PopularSwitching.ladderTrace L q)
  rw [Set.disjoint_left]
  intro x hxp hxq
  simp only [PopularSwitching.ladderTrace, Set.mem_union,
    Set.mem_image] at hxp hxq
  rcases hxp with ⟨a, ha, rfl⟩ | ⟨e, he, rfl⟩
  · rcases hxq with ⟨b, hb, hab⟩ | ⟨f, hf, hbad⟩
    · cases hab
      exact hpq (Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        hp hq ha hb)
    · cases hbad
  · rcases hxq with ⟨b, hb, hbad⟩ | ⟨f, hf, hef⟩
    · cases hbad
    · have hfst : e.1 = f.1 := by
        exact (PopularAuxiliary.Input.LambdaVertex.edge.inj hef).1.symm
      exact hpq (Alternating.DWeb.IsWarp.eq_of_mem_support L.ladder.disjoint
        hp hq (p.edgeSet_subset_support_prod he).1
          (hfst ▸ (q.edgeSet_subset_support_prod hf).1))

/-- A finite auxiliary path meets the traces of only finitely many limiting
ladder components.  This is the cardinal estimate used at every stage of
the strengthened Assertion 8.22 recursion. -/
theorem metLadderPaths_finite
    (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) :
    (metLadderPaths L q).Finite := by
  apply FamilyTools.finite_of_pairwiseDisjoint_of_meets
    (F := PopularSwitching.ladderTrace L)
  · intro p hp q' hq hpq
    exact ladderTrace_pairwiseDisjoint L hp.1 hq.1 hpq
  · exact q.support_finite
  · intro p hp
    obtain ⟨x, hxq, hxp⟩ := hp.2
    exact ⟨x, hxq, hxp⟩

/-- The full gadget trace of the represented component when the auxiliary
path starts at a proxy.  A proxy attachment is chosen at an original vertex
of `proxyPath i`, while the auxiliary support contains only `.proxy i`;
therefore this component is not in general detected by `metLadderPaths`. -/
def startingProxyTrace (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) : Set L.LV :=
  match q.start with
  | .proxy i => PopularSwitching.ladderTrace L (L.proxyPath i)
  | _ => ∅

theorem startingProxyTrace_countable
    (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) :
    (startingProxyTrace L q).Countable := by
  cases h : q.start with
  | old x => simp [startingProxyTrace, h]
  | edge x y => simp [startingProxyTrace, h]
  | proxy i =>
      simpa [startingProxyTrace, h] using
        (PopularSwitching.ladderTrace_countable L (L.proxyPath i))

/-- The complete ladder trace exposed by one earlier finite auxiliary path.
Besides components met through ordinary/edge gadgets, it includes the one
component represented by a possible starting proxy. -/
def metLadderTrace (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) : Set L.LV :=
  (⋃ Y ∈ metLadderPaths L q, PopularSwitching.ladderTrace L Y) ∪
    startingProxyTrace L q

theorem metLadderTrace_countable
    (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) :
    (metLadderTrace L q).Countable := by
  apply Set.Countable.union
  · apply FamilyTools.countable_biUnion (metLadderPaths_finite L q).countable
    intro Y _hY
    exact PopularSwitching.ladderTrace_countable L Y
  · exact startingProxyTrace_countable L q

/-- The finite set of limiting components exposed by an auxiliary path,
including the component represented only by a possible initial proxy. -/
def exposedLadderPaths (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) : Set Gamma.DPath :=
  metLadderPaths L q ∪
    match q.start with
    | .proxy i => {L.proxyPath i}
    | _ => ∅

theorem exposedLadderPaths_finite
    (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) :
    (exposedLadderPaths L q).Finite := by
  apply (metLadderPaths_finite L q).union
  cases q.start <;> simp

/-- Membership in the complete exposed trace has a concrete exposed
component witness.  This is the bridge needed to reason about a later
proxy attachment, which is not itself a vertex of the auxiliary path. -/
theorem mem_metLadderTrace_iff
    (L : PopularAuxiliary.Input Gamma I)
    (q : FinitePath L.lambda.graph) (x : L.LV) :
    x ∈ metLadderTrace L q ↔
      ∃ Y ∈ exposedLadderPaths L q,
        x ∈ PopularSwitching.ladderTrace L Y := by
  constructor
  · rintro (hx | hx)
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨Y, hx⟩ := hx
      obtain ⟨hY, hxY⟩ := hx
      exact ⟨Y, Or.inl hY, hxY⟩
    · cases hstart : q.start with
      | old v => simp [startingProxyTrace, hstart] at hx
      | edge u v => simp [startingProxyTrace, hstart] at hx
      | proxy i =>
          exact ⟨L.proxyPath i, by
            simp [exposedLadderPaths, hstart], by
            simpa [startingProxyTrace, hstart] using hx⟩
  · rintro ⟨Y, hY | hY, hxY⟩
    · left
      exact Set.mem_iUnion.2 ⟨Y, Set.mem_iUnion.2 ⟨hY, hxY⟩⟩
    · right
      cases hstart : q.start with
      | old v => simp [exposedLadderPaths, hstart] at hY
      | edge u v => simp [exposedLadderPaths, hstart] at hY
      | proxy i =>
          have hEq : Y = L.proxyPath i := by
            simpa [exposedLadderPaths, hstart] using hY
          simpa [startingProxyTrace, hstart, hEq] using hxY

/-- If proxy paths are genuine distinct ladder components, a proxy trace
meeting an exposed trace represents one of the finitely many exposed
components. -/
theorem proxyPath_mem_exposedLadderPaths_of_meets
    (L : PopularAuxiliary.Input Gamma I)
    (hproxy_mem : ∀ i, L.proxyPath i ∈ L.ladder.paths)
    (q : FinitePath L.lambda.graph) (i : I)
    (hmeet : (PopularSwitching.ladderTrace L (L.proxyPath i) ∩
      metLadderTrace L q).Nonempty) :
    L.proxyPath i ∈ exposedLadderPaths L q := by
  obtain ⟨x, hxi, hxq⟩ := hmeet
  obtain ⟨Y, hY, hxY⟩ := (mem_metLadderTrace_iff L q x).1 hxq
  have hYmem : Y ∈ L.ladder.paths := by
    rcases hY with hY | hY
    · exact hY.1
    · cases hstart : q.start with
      | old v => simp [exposedLadderPaths, hstart] at hY
      | edge u v => simp [exposedLadderPaths, hstart] at hY
      | proxy j =>
          have hEq : Y = L.proxyPath j := by
            simpa [exposedLadderPaths, hstart] using hY
          exact hEq.symm ▸ hproxy_mem j
  by_contra hne
  have hne' : L.proxyPath i ≠ Y := by
    intro hEq
    exact hne (hEq ▸ hY)
  exact Set.disjoint_left.1
    (ladderTrace_pairwiseDisjoint L (hproxy_mem i) hYmem hne')
      hxi hxY

/-- Candidate paths whose hidden initial proxy component meets an earlier
exposed ladder trace away from the current request apex. -/
def proxyComponentCollidingPaths
    (L : PopularAuxiliary.Input Gamma I) {a : L.LV}
    (F : Popular.JoinedFamily L.lambda {a})
    (q : FinitePath L.lambda.graph) : Set (FinitePath L.lambda.graph) :=
  {p | p ∈ F.paths ∧
    ∃ x ∈ metLadderTrace L q \ {a},
      x ∈ startingProxyTrace L p}

/-- Under the concrete source-faithful hypotheses, hidden proxy collisions
have only finitely many initial indices. -/
theorem proxyComponentCollidingIndices_finite
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa)
    (hproxy_mem : ∀ i, L.proxyPath i ∈ L.ladder.paths)
    (hproxy_inj : Function.Injective L.proxyPath)
    {a : L.LV} (F : Popular.JoinedFamily L.lambda {a})
    (q : FinitePath L.lambda.graph) :
    (GroundingSelection.restrictedIndices U F
      (proxyComponentCollidingPaths L F q)).Finite := by
  let badI : Set I := {i | L.proxyPath i ∈ exposedLadderPaths L q}
  have hbadI : badI.Finite := by
    exact Set.Finite.preimage hproxy_inj.injOn
      (exposedLadderPaths_finite L q)
  let sourceOf : I → L.lambda.source := fun i ↦
    ⟨PopularAuxiliary.Input.LambdaVertex.proxy i,
      L.mem_lambda_source_proxy i⟩
  have hfiniteImage : (U.f '' (sourceOf '' badI)).Finite :=
    (hbadI.image sourceOf).image U.f
  apply hfiniteImage.subset
  rintro b ⟨p, hp, hpb⟩
  obtain ⟨x, hxq, hxp⟩ := hp.2.2
  cases hstart : p.start with
  | old v => simp [startingProxyTrace, hstart] at hxp
  | edge u v => simp [startingProxyTrace, hstart] at hxp
  | proxy i =>
      have hiExposed : L.proxyPath i ∈ exposedLadderPaths L q := by
        apply proxyPath_mem_exposedLadderPaths_of_meets L hproxy_mem q i
        exact ⟨x, by simpa [startingProxyTrace, hstart] using hxp, hxq.1⟩
      have hs :
          (⟨p.start, F.starts_in_source hp.1⟩ : L.lambda.source) =
            sourceOf i := by
        apply Subtype.ext
        change p.start = PopularAuxiliary.Input.LambdaVertex.proxy i
        exact hstart
      refine ⟨sourceOf i, ⟨i, hiExposed, rfl⟩, ?_⟩
      rw [← hpb, hs]

/-- The exact structural condition under which initial proxies faithfully
name distinct members of the limiting ladder warp.  It holds for the
concrete legal-ladder auxiliary input. -/
def ProxyPathsFaithful (L : PopularAuxiliary.Input Gamma I) : Prop :=
  (∀ i, L.proxyPath i ∈ L.ladder.paths) ∧
    Function.Injective L.proxyPath

/-- Hidden proxy collisions are imposed only when the input certifies that
its proxies name distinct ladder components.  This keeps the generic
auxiliary API honest while making the concrete Section 8 recursion
source-faithful. -/
noncomputable def certifiedProxyComponentCollidingPaths
    (L : PopularAuxiliary.Input Gamma I) {a : L.LV}
    (F : Popular.JoinedFamily L.lambda {a})
    (q : FinitePath L.lambda.graph) : Set (FinitePath L.lambda.graph) := by
  classical
  exact if _h : ProxyPathsFaithful L then
    proxyComponentCollidingPaths L F q
  else ∅

theorem certifiedProxyComponentCollidingIndices_finite
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa)
    {a : L.LV} (F : Popular.JoinedFamily L.lambda {a})
    (q : FinitePath L.lambda.graph) :
    (GroundingSelection.restrictedIndices U F
      (certifiedProxyComponentCollidingPaths L F q)).Finite := by
  classical
  by_cases h : ProxyPathsFaithful L
  · rw [certifiedProxyComponentCollidingPaths, dif_pos h]
    exact proxyComponentCollidingIndices_finite L U h.1 h.2 F q
  · rw [certifiedProxyComponentCollidingPaths, dif_neg h]
    have heq : GroundingSelection.restrictedIndices U F
        (∅ : Set (FinitePath L.lambda.graph)) = ∅ := by
      ext b
      simp [GroundingSelection.restrictedIndices]
    rw [heq]
    exact Set.finite_empty

theorem certifiedProxyComponentCollidingIndices_nonstationary
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa)
    {a : L.LV} (F : Popular.JoinedFamily L.lambda {a})
    (q : FinitePath L.lambda.graph) :
    ¬ Stationary.IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U F
        (certifiedProxyComponentCollidingPaths L F q)) := by
  apply Stationary.not_isStationaryBelow_of_countable
    U.regular U.uncountable
  exact (certifiedProxyComponentCollidingIndices_finite L U F q).countable

/-- Members of a local fan which meet, away from the fan apex, a limiting
ladder component already exposed by `q`. -/
def componentCollidingPaths
    (L : PopularAuxiliary.Input Gamma I) {a : L.LV}
    (F : Popular.JoinedFamily L.lambda {a})
    (q : FinitePath L.lambda.graph) : Set (FinitePath L.lambda.graph) :=
  {p | p ∈ F.paths ∧
    ∃ x ∈ metLadderTrace L q \ {a}, x ∈ p.support}

/-- For a fixed earlier finite path, the current fan members which touch
one of its exposed ladder components away from their own apex have a
nonstationary initial-index set. -/
theorem componentCollidingIndices_nonstationary
    {kappa : Cardinal.{u}}
    (L : PopularAuxiliary.Input Gamma I)
    (U : Popular.KappaIndexed L.lambda kappa) {a : L.LV}
    (F : Popular.JoinedFamily L.lambda {a})
    (q : FinitePath L.lambda.graph) :
    ¬ Stationary.IsStationaryBelow kappa
      (GroundingSelection.restrictedIndices U F
        (componentCollidingPaths L F q)) := by
  apply PopularAuxiliary.Input.joinedFamily_initialIndices_nonstationary_of_meets_countable
    U (PopularSwitching.restrictPaths F (componentCollidingPaths L F q))
    ((metLadderTrace_countable L q).mono (Set.diff_subset))
  · exact Set.disjoint_sdiff_left
  · intro p hp
    obtain ⟨x, hxtrace, hxp⟩ := hp.2.2
    exact ⟨x, hxtrace, hxp⟩

/-! ## The component-compatible request recursion -/

abbrev RequestPath (L : PopularAuxiliary.Input Gamma I) :=
  FinitePath L.lambda.graph

/-- Candidates at a request avoid both every earlier selected path and,
away from their own apex, every limiting ladder component exposed by an
earlier selected path. -/
def strongFreshCandidates
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (a : Stationary.Below kappa) (r : Request L S.cut)
    (previous : ∀ b : Stationary.Below kappa, b < a → Option (RequestPath L)) :
    Set (RequestPath L) :=
  {p | p ∈ (GroundingControlledAssembly.controlledRequestFan S K r).paths ∧
    ∀ b (hba : b < a) q, previous b hba = some q →
      Disjoint p.support q.support ∧
        p ∉ componentCollidingPaths L
          (GroundingControlledAssembly.controlledRequestFan S K r) q ∧
        p ∉ certifiedProxyComponentCollidingPaths L
          (GroundingControlledAssembly.controlledRequestFan S K r) q}

def strongChooseAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Stationary.Below kappa)
    (a : Stationary.Below kappa)
    (previous : ∀ b : Stationary.Below kappa, b < a → Option (RequestPath L)) :
    Option (RequestPath L) :=
  match GroundingAssembly.requestAt rank a with
  | none => none
  | some r => GroundingAssembly.chooseSome
      (strongFreshCandidates S K a r previous)

def strongRecursiveChoice
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Stationary.Below kappa)
    (a : Stationary.Below kappa) : Option (RequestPath L) :=
  WellFounded.fix wellFounded_lt
    (fun a previous => strongChooseAt S K rank a previous) a

theorem strongRecursiveChoice_eq
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Stationary.Below kappa)
    (a : Stationary.Below kappa) :
    strongRecursiveChoice S K rank a =
      strongChooseAt S K rank a
        (fun b _hba => strongRecursiveChoice S K rank b) := by
  exact WellFounded.fix_eq wellFounded_lt
    (fun a previous => strongChooseAt S K rank a previous) a

def StrongChoiceValidAt
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Stationary.Below kappa)
    (a : Stationary.Below kappa)
    (previous : ∀ b : Stationary.Below kappa, b < a → Option (RequestPath L))
    (chosen : Option (RequestPath L)) : Prop :=
  match GroundingAssembly.requestAt rank a with
  | none => chosen = none
  | some r => ∃ p, chosen = some p ∧
      p ∈ strongFreshCandidates S K a r previous

/-- The strengthened fresh set is nonempty.  For each earlier path, both
the ordinary support-collision family and the whole-component-collision
family are nonstationary; regularity handles their union over all earlier
stages. -/
theorem strongFreshCandidates_nonempty
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Stationary.Below kappa)
    (a : Stationary.Below kappa) (r : Request L S.cut)
    (hra : GroundingAssembly.requestAt rank a = some r)
    (previous : ∀ b : Stationary.Below kappa, b < a → Option (RequestPath L))
    (hprevious : ∀ b (hba : b < a),
      StrongChoiceValidAt S K rank b
        (fun c _hcb => previous c (lt_trans _hcb hba))
        (previous b hba)) :
    (strongFreshCandidates S K a r previous).Nonempty := by
  let F := GroundingControlledAssembly.controlledRequestFan S K r
  let bad : Set.Iio a → Set (Stationary.Below kappa) := fun b =>
    match previous b.1 b.2 with
    | none => ∅
    | some q => GroundingSelection.restrictedIndices U F
        (GroundingAssembly.collidingPaths F q ∪
          (componentCollidingPaths L F q ∪
            certifiedProxyComponentCollidingPaths L F q))
  have hbad : ∀ b, ¬ Stationary.IsStationaryBelow kappa (bad b) := by
    intro b
    dsimp only [bad]
    cases hq : previous b.1 b.2 with
    | none => simp [hq]
    | some q =>
        have hv := hprevious b.1 b.2
        cases hrb : GroundingAssembly.requestAt rank b.1 with
        | none =>
            simp only [StrongChoiceValidAt, hrb] at hv
            exact False.elim (by simpa [hq] using hv)
        | some rb =>
            simp only [StrongChoiceValidAt, hrb] at hv
            obtain ⟨q', hq', hq'fresh⟩ := hv
            have hqq' : q = q' := Option.some.inj (hq.symm.trans hq')
            subst q'
            have hrankb : rank rb = b.1 :=
              (GroundingAssembly.requestAt_eq_some_iff rank b.1 rb).1 hrb
            have hranka : rank r = a :=
              (GroundingAssembly.requestAt_eq_some_iff rank a r).1 hra
            have hrbr : rb ≠ r := by
              intro h
              subst rb
              exact (ne_of_lt b.2) (hrankb.symm.trans hranka)
            have hqapex : Disjoint q.support {requestAuxVertex r} :=
              GroundingAssembly.normalized_member_disjoint_other_apex S K hrbr
                hq'fresh.1.1
            have hpath : ¬ Stationary.IsStationaryBelow kappa
                (GroundingSelection.restrictedIndices U F
                  (GroundingAssembly.collidingPaths F q)) :=
              GroundingAssembly.collidingIndices_nonstationary U F q hqapex
            have hcomponent : ¬ Stationary.IsStationaryBelow kappa
                (GroundingSelection.restrictedIndices U F
                  (componentCollidingPaths L F q)) :=
              componentCollidingIndices_nonstationary L U F q
            have hproxy : ¬ Stationary.IsStationaryBelow kappa
                (GroundingSelection.restrictedIndices U F
                  (certifiedProxyComponentCollidingPaths L F q)) :=
              certifiedProxyComponentCollidingIndices_nonstationary L U F q
            have hcomponentProxy :=
              GroundingSelection.not_isStationaryBelow_union
                U.regular U.uncountable hcomponent hproxy
            have hcomponentProxy' : ¬ Stationary.IsStationaryBelow kappa
                (GroundingSelection.restrictedIndices U F
                  (componentCollidingPaths L F q ∪
                    certifiedProxyComponentCollidingPaths L F q)) := by
              intro hstationary
              apply hcomponentProxy
              exact hstationary.mono
                (GroundingControlledAssembly.restrictedIndices_union_subset
                  U F (componentCollidingPaths L F q)
                    (certifiedProxyComponentCollidingPaths L F q))
            have hunion := GroundingSelection.not_isStationaryBelow_union
              U.regular U.uncountable hpath hcomponentProxy'
            simpa only [hq] using fun hstationary => hunion
              (hstationary.mono
                (GroundingControlledAssembly.restrictedIndices_union_subset
                  U F (GroundingAssembly.collidingPaths F q)
                    (componentCollidingPaths L F q ∪
                      certifiedProxyComponentCollidingPaths L F q)))
  have hbadUnion : ¬ Stationary.IsStationaryBelow kappa (⋃ b, bad b) :=
    Stationary.not_isStationaryBelow_iUnion_of_lt U.regular U.uncountable
      (GroundingAssembly.mk_Iio_below_lt_lift a) hbad
  have hfreshIndices : Stationary.IsStationaryBelow kappa
      (Popular.initialIndicesOf U F.paths F.starts_in_source \ ⋃ b, bad b) :=
    PopularSwitching.stationary_diff_of_stationary_of_nonstationary
      U.regular U.uncountable
      (GroundingControlledAssembly.controlledRequestFan_stationary S K r)
      hbadUnion
  obtain ⟨i, hiFan, hiBad⟩ := hfreshIndices.nonempty
  obtain ⟨p, hpFan, hip⟩ := hiFan
  refine ⟨p, hpFan, ?_⟩
  intro b hba q hbq
  have index_in_bad_of
      (hpP : p ∈ GroundingAssembly.collidingPaths F q ∪
        (componentCollidingPaths L F q ∪
          certifiedProxyComponentCollidingPaths L F q)) :
      i ∈ bad ⟨b, hba⟩ := by
    have hindex := GroundingSelection.mem_restrictedIndices_of U F
      (GroundingAssembly.collidingPaths F q ∪
        (componentCollidingPaths L F q ∪
          certifiedProxyComponentCollidingPaths L F q))
      hpFan hpP
    have heq : U.f ⟨p.start, F.starts_in_source hpFan⟩ = i := hip
    dsimp only [bad]
    rw [hbq]
    exact heq ▸ hindex
  constructor
  · by_contra hdisj
    have hmeet : (p.support ∩ q.support).Nonempty :=
      Set.not_disjoint_iff.mp hdisj
    have hpcoll : p ∈ GroundingAssembly.collidingPaths F q :=
      ⟨hpFan, hmeet⟩
    exact hiBad (Set.mem_iUnion.2 ⟨⟨b, hba⟩,
      index_in_bad_of (Or.inl hpcoll)⟩)
  · constructor
    · intro hpcomponent
      exact hiBad (Set.mem_iUnion.2 ⟨⟨b, hba⟩,
        index_in_bad_of (Or.inr (Or.inl hpcomponent))⟩)
    · intro hpproxy
      exact hiBad (Set.mem_iUnion.2 ⟨⟨b, hba⟩,
        index_in_bad_of (Or.inr (Or.inr hpproxy))⟩)

theorem strongRecursiveChoice_valid
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    {U : Popular.KappaIndexed L.lambda kappa}
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (rank : Request L S.cut ↪ Stationary.Below kappa)
    (a : Stationary.Below kappa) :
    StrongChoiceValidAt S K rank a
      (fun b _hba => strongRecursiveChoice S K rank b)
      (strongRecursiveChoice S K rank a) := by
  rw [strongRecursiveChoice_eq S K rank a]
  cases hra : GroundingAssembly.requestAt rank a with
  | none => simp [StrongChoiceValidAt, strongChooseAt, hra]
  | some r =>
      have hnonempty :
          (strongFreshCandidates S K a r
            (fun b _hba => strongRecursiveChoice S K rank b)).Nonempty := by
        apply strongFreshCandidates_nonempty S K rank a r hra
        intro b hba
        simpa only using strongRecursiveChoice_valid S K rank b
      obtain ⟨p, hpchoose, hp⟩ :=
        GroundingAssembly.chooseSome_spec hnonempty
      simp only [StrongChoiceValidAt, hra, strongChooseAt]
      exact ⟨p, by simpa [hra] using hpchoose, hp⟩
termination_by a.1

/-- The component-compatible selected path at one request. -/
def strongSelectedPath
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) : RequestPath L :=
  Classical.choose (show ∃ p,
      strongRecursiveChoice S K (GroundingAssembly.requestRank U S)
          (GroundingAssembly.requestRank U S r) = some p ∧
        p ∈ strongFreshCandidates S K
          (GroundingAssembly.requestRank U S r) r
          (fun b _h => strongRecursiveChoice S K
            (GroundingAssembly.requestRank U S) b) by
    have hv := strongRecursiveChoice_valid S K
      (GroundingAssembly.requestRank U S)
      (GroundingAssembly.requestRank U S r)
    have hra : GroundingAssembly.requestAt (GroundingAssembly.requestRank U S)
        (GroundingAssembly.requestRank U S r) = some r :=
      (GroundingAssembly.requestAt_eq_some_iff
        (GroundingAssembly.requestRank U S) _ r).2 rfl
    simpa only [StrongChoiceValidAt, hra] using hv)

theorem strongSelectedPath_spec
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    strongRecursiveChoice S K (GroundingAssembly.requestRank U S)
        (GroundingAssembly.requestRank U S r) =
          some (strongSelectedPath U S K r) ∧
      strongSelectedPath U S K r ∈ strongFreshCandidates S K
        (GroundingAssembly.requestRank U S r) r
        (fun b _h => strongRecursiveChoice S K
          (GroundingAssembly.requestRank U S) b) := by
  unfold strongSelectedPath
  exact Classical.choose_spec (show ∃ p,
      strongRecursiveChoice S K (GroundingAssembly.requestRank U S)
          (GroundingAssembly.requestRank U S r) = some p ∧
        p ∈ strongFreshCandidates S K
          (GroundingAssembly.requestRank U S r) r
          (fun b _h => strongRecursiveChoice S K
            (GroundingAssembly.requestRank U S) b) by
    have hv := strongRecursiveChoice_valid S K
      (GroundingAssembly.requestRank U S)
      (GroundingAssembly.requestRank U S r)
    have hra : GroundingAssembly.requestAt (GroundingAssembly.requestRank U S)
        (GroundingAssembly.requestRank U S r) = some r :=
      (GroundingAssembly.requestAt_eq_some_iff
        (GroundingAssembly.requestRank U S) _ r).2 rfl
    simpa only [StrongChoiceValidAt, hra] using hv)

theorem strongSelectedPath_mem_controlledRequestFan
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    strongSelectedPath U S K r ∈
      (GroundingControlledAssembly.controlledRequestFan S K r).paths :=
  (strongSelectedPath_spec U S K r).2.1

/-- The strongly selected route meets the popular cut only at the auxiliary
vertex representing its own request.  This is the literal `Lambda - C`
boundary condition needed when the route is decoded back into the ladder. -/
theorem strongSelectedPath_support_inter_cut_subset_requestAuxVertex
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (strongSelectedPath U S K r).support ∩ S.cut ⊆
      {requestAuxVertex r} := by
  exact GroundingAssembly.normalizedRequestFan_cut_normalized S K r
    (strongSelectedPath_mem_controlledRequestFan U S K r).1

/-- Pointwise form of
`strongSelectedPath_support_inter_cut_subset_requestAuxVertex`. -/
theorem strongSelectedPath_cut_contact_eq_requestAuxVertex
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut)
    {x : PopularAuxiliary.Input.LambdaVertex V I}
    (hxp : x ∈ (strongSelectedPath U S K r).support)
    (hxCut : x ∈ S.cut) :
    x = requestAuxVertex r := by
  exact Set.mem_singleton_iff.1
    (strongSelectedPath_support_inter_cut_subset_requestAuxVertex
      U S K r ⟨hxp, hxCut⟩)

theorem strongSelectedPath_not_mem_hangingLadder
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    strongSelectedPath U S K r ∉ K.hangingLadder r := by
  intro h
  exact (strongSelectedPath_mem_controlledRequestFan U S K r).2 (Or.inl h)

theorem strongSelectedPath_not_mem_hangingFragment
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    strongSelectedPath U S K r ∉ K.hangingFragment r := by
  intro h
  exact (strongSelectedPath_mem_controlledRequestFan U S K r).2 (Or.inr h)

theorem strongSelectedPath_not_hangingLadderCollision
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    (r : Request L S.cut) :
    ¬ GroundingConcreteControls.hangingLadderCollision L S.cut r
      (strongSelectedPath U S K.toControls r) := by
  intro h
  apply strongSelectedPath_not_mem_hangingLadder U S K.toControls r
  rw [K.hangingLadder_exact r]
  exact h

/-- Source condition (b), in its exact off-apex form: a strongly selected
request path cannot meet any gadget of a hanging ladder component except
possibly its own request apex.  In particular this applies even when that
same hanging component contains the apex. -/
theorem strongSelectedPath_no_offApex_hangingLadder_contact
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    (r : Request L S.cut) {Y : Gamma.DPath}
    (hY : Y ∈ PopularAuxiliary.hangingPaths Gamma L.ladder.paths)
    {a : PopularAuxiliary.Input.LambdaVertex V I}
    (haY : a ∈ PopularSwitching.ladderTrace L Y)
    (haApex : a ≠ requestAuxVertex r) :
    a ∉ (strongSelectedPath U S K.toControls r).support := by
  intro hap
  exact strongSelectedPath_not_hangingLadderCollision U S K r
    ⟨Y, hY, a, ⟨haY, by
      intro ha
      exact haApex (Set.mem_singleton_iff.1 ha)⟩, hap⟩

theorem strongSelectedPath_not_hangingFragmentCollision
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    (r : Request L S.cut) :
    ¬ GroundingConcreteControls.hangingFragmentCollision L S.cut r
      (strongSelectedPath U S K.toControls r) := by
  intro h
  apply strongSelectedPath_not_mem_hangingFragment U S K.toControls r
  rw [K.hangingFragment_exact r]
  exact h

theorem strongSelectedPath_finish
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (strongSelectedPath U S K r).finish = requestAuxVertex r :=
  Set.mem_singleton_iff.1
    ((GroundingControlledAssembly.controlledRequestFan S K r).ends_in_join
      (strongSelectedPath_mem_controlledRequestFan U S K r))

/-- Later selected paths miss, off their own apex, every full limiting
ladder trace exposed by an earlier selected path. -/
theorem strongSelectedPath_avoids_earlier_components
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s) :
    Disjoint (strongSelectedPath U S K s).support
      (metLadderTrace L (strongSelectedPath U S K r) \
        {requestAuxVertex s}) := by
  have hfresh := (strongSelectedPath_spec U S K s).2.2
    (GroundingAssembly.requestRank U S r) hrs
    (strongSelectedPath U S K r) (strongSelectedPath_spec U S K r).1
  rw [Set.disjoint_left]
  intro x hxp hxtrace
  exact hfresh.2.1 ⟨strongSelectedPath_mem_controlledRequestFan U S K s,
    x, hxtrace, hxp⟩

/-- Later selected paths also avoid an earlier exposed component through
their hidden initial proxy attachment.  This is the candidate-side half of
the proxy-source repair. -/
theorem strongSelectedPath_proxy_avoids_earlier_components
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r s : Request L S.cut)
    (hrs : GroundingAssembly.requestRank U S r <
      GroundingAssembly.requestRank U S s) :
    strongSelectedPath U S K s ∉
      certifiedProxyComponentCollidingPaths L
        (GroundingControlledAssembly.controlledRequestFan S K s)
        (strongSelectedPath U S K r) := by
  exact (strongSelectedPath_spec U S K s).2.2
    (GroundingAssembly.requestRank U S r) hrs
    (strongSelectedPath U S K r)
    (strongSelectedPath_spec U S K r).1 |>.2.2

/-- The strengthened selected family is still an honest auxiliary warp. -/
def strongSelectedWarp
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S) :
    Popular.XSWarp L.lambda (GroundingSelection.requestCut L S.cut) where
  paths := Set.range (strongSelectedPath U S K)
  disjoint := by
    rintro p ⟨r, rfl⟩ q ⟨s, rfl⟩ hpq
    rcases lt_trichotomy (GroundingAssembly.requestRank U S r)
        (GroundingAssembly.requestRank U S s) with hrs | hrs | hrs
    · exact ((strongSelectedPath_spec U S K s).2.2 _ hrs _
        (strongSelectedPath_spec U S K r).1).1.symm
    · have hrs' : r = s := (GroundingAssembly.requestRank U S).injective hrs
      subst s
      exact False.elim (hpq rfl)
    · exact ((strongSelectedPath_spec U S K r).2.2 _ hrs _
        (strongSelectedPath_spec U S K s).1).1
  starts_in_source := by
    rintro p ⟨r, rfl⟩
    exact (GroundingControlledAssembly.controlledRequestFan S K r).starts_in_source
      (strongSelectedPath_mem_controlledRequestFan U S K r)
  ends_in_target := by
    rintro p ⟨r, rfl⟩
    exact ⟨r, (strongSelectedPath_finish U S K r).symm⟩

theorem strongSelectedWarp_covers_requests
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ∃ p ∈ (strongSelectedWarp U S K).paths,
      p.finish = requestAuxVertex r :=
  ⟨strongSelectedPath U S K r, ⟨r, rfl⟩,
    strongSelectedPath_finish U S K r⟩

theorem strongSelectedWarp_member_avoids_concrete_collisions
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingConcreteControls.ConcreteControls S)
    {p : RequestPath L}
    (hp : p ∈ (strongSelectedWarp U S K.toControls).paths) :
    ∃ r : Request L S.cut,
      p = strongSelectedPath U S K.toControls r ∧
      ¬ GroundingConcreteControls.hangingLadderCollision L S.cut r p ∧
      ¬ GroundingConcreteControls.hangingFragmentCollision L S.cut r p := by
  obtain ⟨r, rfl⟩ := hp
  exact ⟨r, rfl, strongSelectedPath_not_hangingLadderCollision U S K r,
    strongSelectedPath_not_hangingFragmentCollision U S K r⟩

end GroundingSimultaneousDecode

namespace DWeb.KappaLadder

open DirectedPath Stationary PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- The concrete legal-ladder proxies are distinct recorded rays in the
limiting warp, so the generic hidden-proxy collision guard is active. -/
theorem popularAuxiliary_proxyPathsFaithful
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance) :
    GroundingSimultaneousDecode.ProxyPathsFaithful
      (L.popularAuxiliaryInput hL.legal) := by
  constructor
  · intro i
    obtain ⟨a, _ha, hchosen⟩ := i.2
    have hi := L.recorded_mem_inessential
      hL.legal.recordedPathsPersist hchosen
      (b := Ladder.finalStage kappa) (by
        change a.1 + 1 ≤ kappa.ord
        exact (Order.add_one_le_iff).2 a.2)
    change i.1 ∈ L.limitWarp
    exact hi.1
  · intro i j hij
    apply Subtype.ext
    simpa only [KappaLadder.popularAuxiliaryInput,
      KappaLadder.groundedInfinitePath] using hij

/-- Source-faithful controls for the simultaneous Section 8 selector.

The ordinary concrete controls remove the strict hanging-ladder and
hanging-fragment collisions.  They do not by themselves prevent a local fan
member from starting at the terminal of a *hanging* finite record.  Such
source indices form the nonstationary set `phiHanging`.  We therefore add
the complement of `groundedSourcePaths` to the fragment exceptional family.
This is only a thinning device: the original two geometric collision
predicates remain included verbatim. -/
noncomputable def groundedConcreteControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL)) :
    GroundingSelection.Controls S where
  hangingLadder r :=
    {p | L.assertion819StrictCollisionPath hL S r p}
  hangingFragment r :=
    {p | GroundingConcreteControls.hangingFragmentCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r p} ∪
    (L.groundedSourcePaths hL)ᶜ
  ladderRank := L.assertion819StrictRank hL S
  ladderTrace := L.assertion819Trace hL S
  ladderRank_regressive := by
    intro r
    rw [L.assertion819StrictCollisionPath_initialIndices hL S r]
    exact L.assertion819StrictRank_regressive hL S r
  ladderTrace_countable := L.assertion819Trace_countable hL S
  ladderTrace_disjoint_apex := L.assertion819Trace_disjoint_apex hL S
  hangingLadder_meets := by
    intro r p hp
    have haStrict :
        (L.popularAuxiliaryIndexed hL).f
          ⟨p.start,
            (PopularSwitching.restrictPaths (requestFan S r)
              {q | L.assertion819StrictCollisionPath hL S r q})
                |>.starts_in_source hp⟩ ∈
          L.assertion819StrictCollisionIndices hL S r := by
      rw [← L.assertion819StrictCollisionPath_initialIndices hL S r]
      exact ⟨p, hp, rfl⟩
    obtain ⟨hpCollision, _a, _d, _hd⟩ := hp.2
    have hs :
        (⟨p.start,
          (PopularSwitching.restrictPaths (requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ :
            (L.popularAuxiliaryInput hL.legal).lambda.source) =
          ⟨p.start,
            (PopularSwitching.restrictPaths (requestFan S r)
              {q | L.assertion819StrictCollisionPath hL S r q})
                |>.starts_in_source hp⟩ := Subtype.ext rfl
    have haCollision :
        (L.popularAuxiliaryIndexed hL).f
          ⟨p.start,
            (PopularSwitching.restrictPaths (requestFan S r)
              {q | GroundingConcreteControls.hangingLadderCollision
                (L.popularAuxiliaryInput hL.legal) S.cut r q})
                |>.starts_in_source hpCollision⟩ ∈
          L.assertion819StrictCollisionIndices hL S r := by
      rw [congrArg (L.popularAuxiliaryIndexed hL).f hs]
      exact haStrict
    have hmeet := L.assertion819StrictCollision_meets_trace hL S r p
      hpCollision haCollision
    simpa only [congrArg (L.popularAuxiliaryIndexed hL).f hs] using hmeet
  fragmentIndices_nonstationary := by
    intro r
    have hfragment : ¬ IsStationaryBelow kappa
        (GroundingSelection.restrictedIndices
          (L.popularAuxiliaryIndexed hL) (requestFan S r)
            {p | GroundingConcreteControls.hangingFragmentCollision
              (L.popularAuxiliaryInput hL.legal) S.cut r p}) :=
      (GroundingFragmentAssertion820.hangingFragmentWarpData S)
        |>.initialIndices_nonstationary r
    have hground : ¬ IsStationaryBelow kappa
        (GroundingSelection.restrictedIndices
          (L.popularAuxiliaryIndexed hL) (requestFan S r)
            (L.groundedSourcePaths hL)ᶜ) :=
      L.nongroundedSourceIndices_nonstationary hL (requestFan S r)
    intro hstationary
    apply GroundingSelection.not_isStationaryBelow_union
      hL.legal.regular hL.legal.uncountable hfragment hground
    exact hstationary.mono
      (GroundingControlledAssembly.restrictedIndices_union_subset
        (L.popularAuxiliaryIndexed hL) (requestFan S r)
          {p | GroundingConcreteControls.hangingFragmentCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r p}
          (L.groundedSourcePaths hL)ᶜ)

/-- Every path retained by the grounded control package starts at an
auxiliary source whose ordinal index is in `phiGround`. -/
theorem mem_controlledRequestFan_groundedConcreteControls
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    {p : FinitePath (L.popularAuxiliaryInput hL.legal).lambda.graph}
    (hp : p ∈ (GroundingControlledAssembly.controlledRequestFan S
      (L.groundedConcreteControls hL S) r).paths) :
    p ∈ L.groundedSourcePaths hL := by
  have hnot : p ∉
      (L.groundedConcreteControls hL S).hangingFragment r := by
    intro hfragment
    exact hp.2 (Or.inr hfragment)
  by_contra hbad
  exact hnot (Or.inr hbad)

/-- The strengthened simultaneous choice made with grounded controls has a
canonical grounded obstruction stage at every request. -/
theorem strongSelectedPath_mem_groundedSourcePaths
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    GroundingSimultaneousDecode.strongSelectedPath
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S) r ∈
      L.groundedSourcePaths hL := by
  apply L.mem_controlledRequestFan_groundedConcreteControls hL S r
  exact GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r

/-- The grounded stage carried by a selected path, phrased with the exact
source proof used by the selected warp. -/
theorem strongSelectedPath_sourceIndex_mem_phiGround
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    (L.popularAuxiliaryIndexed hL).f
        ⟨(GroundingSimultaneousDecode.strongSelectedPath
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S) r).start,
          (GroundingSimultaneousDecode.strongSelectedWarp
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S)).starts_in_source
                ⟨r, rfl⟩⟩ ∈
      L.phiGround := by
  obtain ⟨hsource, hground⟩ :=
    L.strongSelectedPath_mem_groundedSourcePaths hL S r
  have hs :
      (⟨_, (GroundingSimultaneousDecode.strongSelectedWarp
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)).starts_in_source ⟨r, rfl⟩⟩ :
          (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨_, hsource⟩ := Subtype.ext rfl
  rw [congrArg (L.popularAuxiliaryIndexed hL).f hs]
  exact hground

/-- Grounded thinning removes every genuinely earlier hanging contact and
every cut-preceded hanging-fragment contact.  Equal-stage hanging contacts
are intentionally retained for matched absorption. -/
theorem strongSelectedPath_grounded_avoids_strict_and_fragment
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut) :
    let p := GroundingSimultaneousDecode.strongSelectedPath
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) r
    ¬ L.assertion819StrictCollisionPath hL S r p ∧
      ¬ GroundingConcreteControls.hangingFragmentCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r p := by
  dsimp only
  have hp := GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r
  constructor
  · intro hcollision
    apply hp.2
    left
    exact hcollision
  · intro hcollision
    apply hp.2
    right
    left
    exact hcollision

/-- Every literal hanging contact left by the strict selector is matched to
the selected path's own grounded source stage, for every possible collision
owner. -/
theorem strongSelectedPath_hangingCollision_equalMatch
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (S : Popular.PopularSeparator (L.popularAuxiliaryIndexed hL))
    (r : Request (L.popularAuxiliaryInput hL.legal) S.cut)
    (hcollision : GroundingConcreteControls.hangingLadderCollision
      (L.popularAuxiliaryInput hL.legal) S.cut r
        (GroundingSimultaneousDecode.strongSelectedPath
          (L.popularAuxiliaryIndexed hL) S
            (L.groundedConcreteControls hL S) r)) :
    let p := GroundingSimultaneousDecode.strongSelectedPath
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) r
    let hp : p.start ∈ (L.popularAuxiliaryInput hL.legal).lambda.source :=
      (GroundingSimultaneousDecode.strongSelectedWarp
        (L.popularAuxiliaryIndexed hL) S
          (L.groundedConcreteControls hL S)).starts_in_source ⟨r, rfl⟩
    Nonempty (L.Assertion819EqualMatch hL S r
      ((L.popularAuxiliaryIndexed hL).f ⟨p.start, hp⟩)) := by
  dsimp only
  let p := GroundingSimultaneousDecode.strongSelectedPath
    (L.popularAuxiliaryIndexed hL) S
      (L.groundedConcreteControls hL S) r
  have hpControlled :=
    GroundingSimultaneousDecode.strongSelectedPath_mem_controlledRequestFan
      (L.popularAuxiliaryIndexed hL) S
        (L.groundedConcreteControls hL S) r
  let hpCollision : p ∈ (PopularSwitching.restrictPaths (requestFan S r)
      {q | GroundingConcreteControls.hangingLadderCollision
        (L.popularAuxiliaryInput hL.legal) S.cut r q}).paths :=
    ⟨hpControlled.1.1.1, hcollision⟩
  have hgroundSelected :=
    L.strongSelectedPath_sourceIndex_mem_phiGround hL S r
  have hs :
      (⟨p.start,
        (PopularSwitching.restrictPaths (requestFan S r)
          {q | GroundingConcreteControls.hangingLadderCollision
            (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ :
          (L.popularAuxiliaryInput hL.legal).lambda.source) =
        ⟨p.start,
          (GroundingSimultaneousDecode.strongSelectedWarp
            (L.popularAuxiliaryIndexed hL) S
              (L.groundedConcreteControls hL S)).starts_in_source
                ⟨r, rfl⟩⟩ := Subtype.ext rfl
  have hground :
      (L.popularAuxiliaryIndexed hL).f
        ⟨p.start,
          (PopularSwitching.restrictPaths (requestFan S r)
            {q | GroundingConcreteControls.hangingLadderCollision
              (L.popularAuxiliaryInput hL.legal) S.cut r q})
              |>.starts_in_source hpCollision⟩ ∈ L.phiGround := by
    rw [congrArg (L.popularAuxiliaryIndexed hL).f hs]
    exact hgroundSelected
  have hnot :=
    (L.strongSelectedPath_grounded_avoids_strict_and_fragment hL S r).1
  have hmatch :=
    L.assertion819EqualMatch_of_grounded_collision_of_not_strict
      hL S r p hpCollision hground hnot
  simpa only [congrArg (L.popularAuxiliaryIndexed hL).f hs] using hmatch

end DWeb.KappaLadder

end Erdos599
