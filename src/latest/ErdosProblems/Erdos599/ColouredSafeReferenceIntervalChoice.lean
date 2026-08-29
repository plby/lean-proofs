/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SafeSwitchingRelationalIntervalStep
import ErdosProblems.Erdos599.AlternatingSourceAssertions
import ErdosProblems.Erdos599.GroundingCut
import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# Choosing the next finite reference interval

This file isolates the ordered-path argument used by the safe occurrence
recursion.  A newly found reference contact has an immediate predecessor
outside the boundary.  If a removed interval already exists, its lower end
is the first reference vertex outside the boundary, its upper end has a
forward incoming edge, and the new contact has no such incoming edge.  The
new contact is outside the open removed interior.  These facts force the new
contact to occur strictly after the old upper end.  If no removed interval
exists, the same conclusion starts at the first reference vertex outside the
boundary.

The output is the literal intervening finite subpath of the reference owner;
in particular its freshness is proved rather than postulated.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.SwitchingCore.RelationalInterval

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The path-order formulation of being the first vertex outside `C`. -/
structure IsEarliestOutside (owner : FinitePath Gamma.graph) (C : Set V)
    (a : V) : Prop where
  mem_support : a ∈ owner.support
  outside : a ∉ C
  earlier_mem : ∀ {z : V},
    GroundingCut.Before (.inl owner : Gamma.DPath) z a → z ∈ C

/-- A nonempty removed interval already selected on a finite reference
owner.  `path` is allowed to be trivial; incoming incidence at its finish is
the fact which distinguishes its upper end from the new contact. -/
structure PriorRemovedInterval (owner : FinitePath Gamma.graph)
    (C : Set V) (R F : Set (V × V)) where
  path : FinitePath Gamma.graph
  isSubpath : path.IsSubpathOf (.inl owner)
  removed_eq : R ∩ owner.edgeSet = path.edgeSet
  start_earliest : IsEarliestOutside owner C path.start
  finish_outside : path.finish ∉ C
  finish_incoming : HasIncoming F path.finish

/-- The selected old interval and the literal fresh segment extending its
upper end to `w`. -/
structure BackwardIntervalChoice (owner : FinitePath Gamma.graph)
    (C : Set V) (R : Set (V × V)) (w : V) where
  old : FinitePath Gamma.graph
  extension : FinitePath Gamma.graph
  old_isSubpath : old.IsSubpathOf (.inl owner)
  extension_isSubpath : extension.IsSubpathOf (.inl owner)
  removed_eq : R ∩ owner.edgeSet = old.edgeSet
  old_start_earliest : IsEarliestOutside owner C old.start
  old_finish_outside : old.finish ∉ C
  join : old.finish = extension.start
  extension_finish : extension.finish = w
  strict : Nonempty (FinitePath.OrderedOccurrence owner old.finish w)
  nontrivial : old.finish ≠ w
  extension_nontrivial : extension.start ≠ extension.finish
  fresh : Disjoint extension.edgeSet R

namespace PathOrder

/-- Occurrence indices on a finite simple path are unique. -/
theorem occursAt_index_injective
    {owner : FinitePath Gamma.graph} {n m : ℕ} {x : V}
    (hn : GroundingCut.OccursAt (.inl owner : Gamma.DPath) n x)
    (hm : GroundingCut.OccursAt (.inl owner : Gamma.DPath) m x) : n = m := by
  rcases hn with ⟨hnLen, hnx⟩
  rcases hm with ⟨hmLen, hmx⟩
  have hfin : (⟨n, hnLen⟩ : Fin owner.walk.support.length) = ⟨m, hmLen⟩ :=
    owner.isPath.get_inj_iff.mp (hnx.trans hmx.symm)
  exact congrArg Fin.val hfin

/-- Non-strict path order is antisymmetric on a finite simple path. -/
theorem beforeEq_antisymm
    {owner : FinitePath Gamma.graph} {x y : V}
    (hxy : GroundingCut.BeforeEq (.inl owner : Gamma.DPath) x y)
    (hyx : GroundingCut.BeforeEq (.inl owner : Gamma.DPath) y x) : x = y := by
  rcases hxy with ⟨i, j, hix, hjy, hij⟩
  rcases hyx with ⟨j', i', hjy', hi'x, hji⟩
  have hj : j = j' := occursAt_index_injective hjy hjy'
  have hi : i = i' := occursAt_index_injective hix hi'x
  subst j'
  subst i'
  have hijEq : i = j := le_antisymm hij hji
  subst j
  rcases hix with ⟨_, hix⟩
  rcases hjy with ⟨_, hjy⟩
  exact hix.symm.trans hjy

/-- Strict path order is asymmetric. -/
theorem before_asymm
    {owner : FinitePath Gamma.graph} {x y : V}
    (hxy : GroundingCut.Before (.inl owner : Gamma.DPath) x y) :
    ¬ GroundingCut.Before (.inl owner : Gamma.DPath) y x := by
  intro hyx
  exact hxy.2 (beforeEq_antisymm hxy.1 hyx.1)

/-- Strict order, expressed with occurrence indices, gives the concrete
ordered-occurrence certificate used by `FinitePath.between`. -/
theorem orderedOccurrence_of_before
    {owner : FinitePath Gamma.graph} {x y : V}
    (hxy : GroundingCut.Before (.inl owner : Gamma.DPath) x y) :
    Nonempty (FinitePath.OrderedOccurrence owner x y) := by
  rcases hxy.1 with ⟨i, j, hix, hjy, hij⟩
  have hx : x ∈ owner.support := GroundingCut.occursAt_mem_support hix
  have hy : y ∈ owner.support := GroundingCut.occursAt_mem_support hjy
  apply owner.orderedOccurrence_of_not_reverse hx hy hxy.2
  rintro ⟨hyx⟩
  let q := owner.between hyx
  have hmono : j ≤ i := by
    apply DirectedPath.Walk.position_mono_in_finitePath owner q.walk
      (owner.between_edgeSet_subset hyx)
      ⟨j, by rcases hjy with ⟨h, _⟩; exact h⟩
      ⟨i, by rcases hix with ⟨h, _⟩; exact h⟩
    · rcases hjy with ⟨_, hjy⟩
      exact hjy.trans (owner.between_start hyx).symm
    · rcases hix with ⟨_, hix⟩
      exact hix.trans (owner.between_finish hyx).symm
  have hijEq : i = j := le_antisymm hij hmono
  apply hxy.2
  subst j
  rcases hix with ⟨_, hix⟩
  rcases hjy with ⟨_, hjy⟩
  exact hix.symm.trans hjy

/-- The tail of an owner edge occurs immediately before its head. -/
theorem before_of_mem_edgeSet
    {owner : FinitePath Gamma.graph} {x y : V}
    (hxy : (x, y) ∈ owner.edgeSet) :
    GroundingCut.Before (.inl owner : Gamma.DPath) x y := by
  obtain ⟨n, hn, hnx, hny⟩ :=
    DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet owner.walk hxy
  have hne : x ≠ y := by
    intro h
    have heq : owner.walk.support[n] = owner.walk.support[n + 1] :=
      hnx.trans (h.trans hny.symm)
    have := owner.isPath.getElem_inj_iff.mp heq
    omega
  exact ⟨⟨n, n + 1, ⟨by omega, hnx⟩, ⟨hn, hny⟩, by omega⟩, hne⟩

/-- Transitivity of the non-strict occurrence order. -/
theorem beforeEq_trans
    {owner : FinitePath Gamma.graph} {x y z : V}
    (hxy : GroundingCut.BeforeEq (.inl owner : Gamma.DPath) x y)
    (hyz : GroundingCut.BeforeEq (.inl owner : Gamma.DPath) y z) :
    GroundingCut.BeforeEq (.inl owner : Gamma.DPath) x z := by
  rcases hxy with ⟨i, j, hix, hjy, hij⟩
  rcases hyz with ⟨j', k, hjy', hkz, hjk⟩
  have hj : j = j' := occursAt_index_injective hjy hjy'
  subst j'
  exact ⟨i, k, hix, hkz, hij.trans hjk⟩

/-- Public conversion from the concrete list decomposition to strict path
order. -/
theorem before_of_orderedOccurrence
    {owner : FinitePath Gamma.graph} {x y : V}
    (hxy : FinitePath.OrderedOccurrence owner x y) :
    GroundingCut.Before (.inl owner : Gamma.DPath) x y := by
  have hx : x ∈ owner.support := by
    apply owner.between_support_subset hxy
    simpa using (owner.between hxy).start_mem_support
  have hy : y ∈ owner.support := by
    apply owner.between_support_subset hxy
    simpa using (owner.between hxy).finish_mem_support
  obtain ⟨i, hi⟩ := (GroundingCut.mem_support_iff_exists_occursAt
    (.inl owner : Gamma.DPath) x).1 hx
  obtain ⟨j, hj⟩ := (GroundingCut.mem_support_iff_exists_occursAt
    (.inl owner : Gamma.DPath) y).1 hy
  have hij : i ≤ j := by
    apply DirectedPath.Walk.position_mono_in_finitePath owner
      (owner.between hxy).walk (owner.between_edgeSet_subset hxy)
      ⟨i, by rcases hi with ⟨h, _⟩; exact h⟩
      ⟨j, by rcases hj with ⟨h, _⟩; exact h⟩
    · rcases hi with ⟨_, hi⟩
      exact hi.trans (owner.between_start hxy).symm
    · rcases hj with ⟨_, hj⟩
      exact hj.trans (owner.between_finish hxy).symm
  exact ⟨⟨i, j, hi, hj, hij⟩, hxy.ne⟩

/-- Numerical positions respect strict path order. -/
theorem idxOf_lt_of_before
    [DecidableEq V] {owner : FinitePath Gamma.graph} {x y : V}
    (hxy : GroundingCut.Before (.inl owner : Gamma.DPath) x y) :
    owner.walk.support.idxOf x < owner.walk.support.idxOf y := by
  classical
  rcases hxy.1 with ⟨i, j, hi, hj, hij⟩
  rcases hi with ⟨hiLen, hi⟩
  rcases hj with ⟨hjLen, hj⟩
  have hix : owner.walk.support.idxOf x = i := by
    calc
      owner.walk.support.idxOf x =
          owner.walk.support.idxOf owner.walk.support[i] := by rw [hi]
      _ = i := owner.isPath.idxOf_getElem i hiLen
  have hjy : owner.walk.support.idxOf y = j := by
    calc
      owner.walk.support.idxOf y =
          owner.walk.support.idxOf owner.walk.support[j] := by rw [hj]
      _ = j := owner.isPath.idxOf_getElem j hjLen
  have hijNe : i ≠ j := by
    intro hEq
    cases hEq
    exact hxy.2 (hi.symm.trans hj)
  rw [hix, hjy]
  exact lt_of_le_of_ne hij hijNe

/-- A vertex lying between the endpoints of a finite directed subpath lies
on that subpath. -/
theorem mem_support_of_between_subpath
    (owner q : FinitePath Gamma.graph)
    (hsub : q.IsSubpathOf (.inl owner : Gamma.DPath)) {z : V}
    (hz : z ∈ owner.support)
    (hlo : GroundingCut.Before (.inl owner : Gamma.DPath) q.start z)
    (hhi : GroundingCut.Before (.inl owner : Gamma.DPath) z q.finish) :
    z ∈ q.support := by
  classical
  have hloIdx := idxOf_lt_of_before hlo
  have hhiIdx := idxOf_lt_of_before hhi
  have hzNotFinish : z ≠ owner.finish := by
    intro hzFinish
    have hqMem : q.finish ∈ owner.support :=
      hsub.1 q.finish_mem_support
    have hqBound : owner.walk.support.idxOf q.finish < owner.walk.support.length :=
      List.idxOf_lt_length_iff.mpr hqMem
    have hownerFinish : owner.walk.support.idxOf owner.finish = owner.walk.length := by
      have hlen : owner.walk.length < owner.walk.support.length := by
          rw [Alternating.Walk.support_length_eq owner.walk]
          omega
      have hlast : owner.walk.support[owner.walk.length]'hlen = owner.finish :=
        Alternating.Walk.getElem_length_eq_end owner.walk
      calc
        owner.walk.support.idxOf owner.finish =
            owner.walk.support.idxOf
              (owner.walk.support[owner.walk.length]'hlen) := by
              exact congrArg owner.walk.support.idxOf hlast.symm
        _ = owner.walk.length := owner.isPath.idxOf_getElem _ hlen
    rw [hzFinish, hownerFinish] at hhiIdx
    rw [Alternating.Walk.support_length_eq owner.walk] at hqBound
    omega
  obtain ⟨t, hzt⟩ :=
    Alternating.FinitePath.exists_edge_from_of_mem_of_ne_finish
      owner hz hzNotFinish
  have hpos := Alternating.FinitePath.edgeSet_eq_position_interval owner q hsub
  have hztq : (z, t) ∈ q.edgeSet := by
    rw [hpos]
    exact ⟨hzt, hloIdx.le, hhiIdx⟩
  exact (q.edgeSet_subset_support_prod hztq).1

end PathOrder

/-- Exact owner-edge equality makes every vertex strictly between the
subpath endpoints incident with a removed edge on both sides. -/
theorem interior_removed_of_subpath
    {owner p : FinitePath Gamma.graph} {R : Set (V × V)}
    (hsub : p.IsSubpathOf (.inl owner : Gamma.DPath))
    (hR : R ∩ owner.edgeSet = p.edgeSet) {z : V}
    (hlo : GroundingCut.Before (.inl owner : Gamma.DPath) p.start z)
    (hhi : GroundingCut.Before (.inl owner : Gamma.DPath) z p.finish) :
    z ∈ removedInterior R := by
  have hzOwner : z ∈ owner.support := by
    rcases hlo.1 with ⟨_, _, _, hz, _⟩
    exact GroundingCut.occursAt_mem_support hz
  have hzp : z ∈ p.support :=
    PathOrder.mem_support_of_between_subpath owner p hsub hzOwner hlo hhi
  have hpR : p.edgeSet ⊆ R := by
    intro e he
    have he' : e ∈ R ∩ owner.edgeSet := by
      rw [hR]
      exact he
    exact he'.1
  constructor
  · obtain ⟨x, hx⟩ :=
      FinitePath.exists_incoming_edge_of_mem_support_of_ne_start
        p hzp hlo.2.symm
    exact ⟨x, hpR hx⟩
  · obtain ⟨x, hx⟩ :=
      FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
        p hzp hhi.2
    exact ⟨x, hpR hx⟩

/-- Interior removal is derived from the literal prior interval; it is not
stored as recursive state. -/
theorem PriorRemovedInterval.interior_removed
    {owner : FinitePath Gamma.graph} {C : Set V} {R F : Set (V × V)}
    (old : PriorRemovedInterval owner C R F) {z : V}
    (hlo : GroundingCut.Before (.inl owner : Gamma.DPath) old.path.start z)
    (hhi : GroundingCut.Before (.inl owner : Gamma.DPath) z old.path.finish) :
    z ∈ removedInterior R :=
  interior_removed_of_subpath old.isSubpath old.removed_eq hlo hhi

/-- Build prior-interval state from literal subpath data.  Interior removal
is a consequence, not an additional recursive invariant. -/
def PriorRemovedInterval.of_subpath
    {owner p : FinitePath Gamma.graph} {C : Set V} {R F : Set (V × V)}
    (hsub : p.IsSubpathOf (.inl owner : Gamma.DPath))
    (hR : R ∩ owner.edgeSet = p.edgeSet)
    (hstart : IsEarliestOutside owner C p.start)
    (hfinish : p.finish ∉ C) (hFin : HasIncoming F p.finish) :
    PriorRemovedInterval owner C R F where
  path := p
  isSubpath := hsub
  removed_eq := hR
  start_earliest := hstart
  finish_outside := hfinish
  finish_incoming := hFin

/-- In the repeated-owner case the next reference contact lies strictly
after the upper end of the old removed interval. -/
theorem PriorRemovedInterval.finish_before_newContact
    {owner : FinitePath Gamma.graph} {C : Set V} {R F : Set (V × V)}
    (old : PriorRemovedInterval owner C R F) {y w : V}
    (hyw : (y, w) ∈ owner.edgeSet) (hyC : y ∉ C)
    (hwInterior : w ∉ removedInterior R)
    (hwNoIncoming : ¬ HasIncoming F w) :
    GroundingCut.Before (.inl owner : Gamma.DPath) old.path.finish w := by
  have hywBefore := PathOrder.before_of_mem_edgeSet hyw
  have hwMem : w ∈ owner.support :=
    (owner.edgeSet_subset_support_prod hyw).2
  have hsMem : old.path.start ∈ owner.support := old.start_earliest.mem_support
  have hsBeforeW : GroundingCut.Before
      (.inl owner : Gamma.DPath) old.path.start w := by
    rcases GroundingCut.beforeEq_total
      (P := (.inl owner : Gamma.DPath)) hsMem hwMem with hsw | hws
    · refine ⟨hsw, ?_⟩
      intro hEq
      have hyStart : GroundingCut.Before
          (.inl owner : Gamma.DPath) y old.path.start := by
        simpa [hEq] using hywBefore
      exact hyC (old.start_earliest.earlier_mem hyStart)
    · have hyStartEq : GroundingCut.BeforeEq
          (.inl owner : Gamma.DPath) y old.path.start :=
        PathOrder.beforeEq_trans hywBefore.1 hws
      have hyStartNe : y ≠ old.path.start := by
        intro hEq
        subst y
        exact hywBefore.2
          (PathOrder.beforeEq_antisymm hywBefore.1 hws)
      exact (hyC (old.start_earliest.earlier_mem
        ⟨hyStartEq, hyStartNe⟩)).elim
  have hfMem : old.path.finish ∈ owner.support :=
    old.isSubpath.1 old.path.finish_mem_support
  have hfinishNe : old.path.finish ≠ w := by
    intro hEq
    apply hwNoIncoming
    exact hEq ▸ old.finish_incoming
  rcases GroundingCut.beforeEq_total
    (P := (.inl owner : Gamma.DPath)) hfMem hwMem with hfw | hwf
  · exact ⟨hfw, hfinishNe⟩
  · have hwfStrict : GroundingCut.Before
        (.inl owner : Gamma.DPath) w old.path.finish :=
      ⟨hwf, hfinishNe.symm⟩
    exact (hwInterior (old.interior_removed hsBeforeW hwfStrict)).elim

/-- Literal backward extension in the repeated-owner case. -/
theorem exists_backwardIntervalChoice_of_prior
    {owner : FinitePath Gamma.graph} {C : Set V} {R F : Set (V × V)}
    (old : PriorRemovedInterval owner C R F) {y w : V}
    (hyw : (y, w) ∈ owner.edgeSet) (hyC : y ∉ C)
    (hwInterior : w ∉ removedInterior R)
    (hwNoIncoming : ¬ HasIncoming F w) :
    Nonempty (BackwardIntervalChoice owner C R w) := by
  have hbefore := old.finish_before_newContact hyw hyC hwInterior hwNoIncoming
  obtain ⟨hocc⟩ := PathOrder.orderedOccurrence_of_before hbefore
  let q := owner.between hocc
  have hq : q.IsSubpathOf (.inl owner : Gamma.DPath) :=
    owner.between_isSubpathOf hocc
  have hfresh : Disjoint q.edgeSet R :=
    backward_interval_extension_fresh (.inl owner : Gamma.DPath)
      old.path q old.isSubpath hq (by simp [q]) old.removed_eq
  exact ⟨{
    old := old.path
    extension := q
    old_isSubpath := old.isSubpath
    extension_isSubpath := hq
    removed_eq := old.removed_eq
    old_start_earliest := old.start_earliest
    old_finish_outside := old.finish_outside
    join := by simp [q]
    extension_finish := by simp [q]
    strict := ⟨hocc⟩
    nontrivial := hbefore.2
    extension_nontrivial := by simpa [q] using hbefore.2
    fresh := hfresh }⟩

/-- The first reference anchor is chosen canonically as the first owner
vertex outside `C`. -/
theorem firstOutside_isEarliest
    (owner : FinitePath Gamma.graph) (C : Set V)
    (hS : (owner.support ∩ Cᶜ).Nonempty) :
    IsEarliestOutside owner C
      (GroundingCut.firstVertex (.inl owner : Gamma.DPath) Cᶜ hS) := by
  let a := GroundingCut.firstVertex (.inl owner : Gamma.DPath) Cᶜ hS
  have ha := GroundingCut.firstVertex_mem
    (.inl owner : Gamma.DPath) Cᶜ hS
  refine {
    mem_support := ha.1
    outside := ha.2
    earlier_mem := ?_ }
  intro z hz
  by_contra hzC
  have hzMem : z ∈ owner.support := by
    rcases hz.1 with ⟨_, _, hzx, _, _⟩
    exact GroundingCut.occursAt_mem_support hzx
  have haz : GroundingCut.BeforeEq (.inl owner : Gamma.DPath) a z :=
    GroundingCut.firstVertex_beforeEq (.inl owner : Gamma.DPath) Cᶜ hS
      ⟨hzMem, hzC⟩
  exact hz.2 (PathOrder.beforeEq_antisymm hz.1 haz)

/-- Literal backward extension when no owner edge has yet been removed.  The
old interval is represented by the trivial path at the first outside
vertex. -/
theorem exists_backwardIntervalChoice_of_empty
    {owner : FinitePath Gamma.graph} {C : Set V} {R : Set (V × V)}
    {y w : V} (hR : R ∩ owner.edgeSet = ∅)
    (hyw : (y, w) ∈ owner.edgeSet) (hyC : y ∉ C) (hwC : w ∉ C) :
    Nonempty (BackwardIntervalChoice owner C R w) := by
  have hwMem : w ∈ owner.support :=
    (owner.edgeSet_subset_support_prod hyw).2
  have hS : (owner.support ∩ Cᶜ).Nonempty :=
    ⟨w, hwMem, hwC⟩
  let a := GroundingCut.firstVertex (.inl owner : Gamma.DPath) Cᶜ hS
  have ha : IsEarliestOutside owner C a := firstOutside_isEarliest owner C hS
  have hawEq : GroundingCut.BeforeEq (.inl owner : Gamma.DPath) a w :=
    GroundingCut.firstVertex_beforeEq (.inl owner : Gamma.DPath) Cᶜ hS
      ⟨hwMem, hwC⟩
  have hawNe : a ≠ w := by
    intro hEq
    have hyA : GroundingCut.Before (.inl owner : Gamma.DPath) y a := by
      simpa [hEq] using PathOrder.before_of_mem_edgeSet hyw
    exact hyC (ha.earlier_mem hyA)
  have haw : GroundingCut.Before (.inl owner : Gamma.DPath) a w :=
    ⟨hawEq, hawNe⟩
  obtain ⟨hocc⟩ := PathOrder.orderedOccurrence_of_before haw
  let old := FinitePath.trivial Gamma.graph a
  let q := owner.between hocc
  have hold : old.IsSubpathOf (.inl owner : Gamma.DPath) := by
    constructor
    · intro x hx
      change x ∈ old.support at hx
      have hxa : x = a := by
        simpa [old, FinitePath.support_trivial] using hx
      exact hxa ▸ ha.mem_support
    · simp [old, FinitePath.edgeSet, FinitePath.trivial]
  have hq : q.IsSubpathOf (.inl owner : Gamma.DPath) :=
    owner.between_isSubpathOf hocc
  have hReq : R ∩ owner.edgeSet = old.edgeSet := by
    rw [hR]
    simp [old, FinitePath.edgeSet, FinitePath.trivial]
  have hfresh : Disjoint q.edgeSet R :=
    backward_interval_extension_fresh (.inl owner : Gamma.DPath)
      old q hold hq (by simp [old, q]) hReq
  exact ⟨{
    old := old
    extension := q
    old_isSubpath := hold
    extension_isSubpath := hq
    removed_eq := hReq
    old_start_earliest := by simpa [old] using ha
    old_finish_outside := by simpa [old] using ha.outside
    join := by simp [old, q]
    extension_finish := by simp [q]
    strict := ⟨hocc⟩
    nontrivial := haw.2
    extension_nontrivial := by simpa [q] using haw.2
    fresh := hfresh }⟩

/-- Uniform first/repeated owner choice used by the safe occurrence
recursion. -/
theorem exists_backwardIntervalChoice
    {owner : FinitePath Gamma.graph} {C : Set V} {R F : Set (V × V)}
    {y w : V}
    (hold : R ∩ owner.edgeSet = ∅ ∨
      Nonempty (PriorRemovedInterval owner C R F))
    (hyw : (y, w) ∈ owner.edgeSet) (hyC : y ∉ C) (hwC : w ∉ C)
    (hwInterior : w ∉ removedInterior R)
    (hwNoIncoming : ¬ HasIncoming F w) :
    Nonempty (BackwardIntervalChoice owner C R w) := by
  rcases hold with hEmpty | hPrior
  · exact exists_backwardIntervalChoice_of_empty hEmpty hyw hyC hwC
  · obtain ⟨prior⟩ := hPrior
    exact exists_backwardIntervalChoice_of_prior prior hyw hyC
      hwInterior hwNoIncoming

theorem BackwardIntervalChoice.extension_start_outside
    {owner : FinitePath Gamma.graph} {C : Set V} {R : Set (V × V)} {w : V}
    (Q : BackwardIntervalChoice owner C R w) : Q.extension.start ∉ C := by
  simpa [← Q.join] using Q.old_finish_outside

/-- Appending the chosen literal segment gives the next exact removed
interval on this owner. -/
theorem BackwardIntervalChoice.exists_appendedInterval
    {owner : FinitePath Gamma.graph} {C : Set V} {R : Set (V × V)} {w : V}
    (Q : BackwardIntervalChoice owner C R w) :
    ∃ s : FinitePath Gamma.graph,
      s.start = Q.old.start ∧ s.finish = w ∧
      s.IsSubpathOf (.inl owner : Gamma.DPath) ∧
      s.support = Q.old.support ∪ Q.extension.support ∧
      (R ∪ Q.extension.edgeSet) ∩ owner.edgeSet = s.edgeSet := by
  obtain ⟨s, hsStart, hsFinish, hsSub, hsSupport, hsEdges⟩ :=
    FinitePath.exists_append_isSubpathOf Q.old Q.extension
      (.inl owner : Gamma.DPath) Q.old_isSubpath Q.extension_isSubpath Q.join
  refine ⟨s, hsStart, hsFinish.trans Q.extension_finish, hsSub, hsSupport, ?_⟩
  rw [Set.union_inter_distrib_right, Q.removed_eq]
  have hsubset : Q.extension.edgeSet ⊆ owner.edgeSet :=
    Q.extension_isSubpath.2
  rw [Set.inter_eq_left.mpr hsubset]
  exact hsEdges.symm

/-- Once the new upper contact has acquired an incoming forward edge, the
literal appended interval is immediately a valid prior-interval state for
the next visit to this owner. -/
theorem BackwardIntervalChoice.exists_updatedPrior
    {owner : FinitePath Gamma.graph} {C : Set V} {R F' : Set (V × V)}
    {w : V} (Q : BackwardIntervalChoice owner C R w)
    (hwC : w ∉ C) (hwIncoming : HasIncoming F' w) :
    Nonempty (PriorRemovedInterval owner C
      (R ∪ Q.extension.edgeSet) F') := by
  obtain ⟨s, hsStart, hsFinish, hsSub, _hsSupport, hsEdges⟩ :=
    Q.exists_appendedInterval
  have hsIncoming : HasIncoming F' s.finish := by
    rw [hsFinish]
    exact hwIncoming
  refine ⟨PriorRemovedInterval.of_subpath hsSub hsEdges ?_ ?_ hsIncoming⟩
  · rw [hsStart]
    exact Q.old_start_earliest
  · rw [hsFinish]
    exact hwC

#print axioms exists_backwardIntervalChoice
#print axioms BackwardIntervalChoice.exists_appendedInterval
#print axioms BackwardIntervalChoice.exists_updatedPrior

end Erdos599.Alternating.SwitchingCore.RelationalInterval
