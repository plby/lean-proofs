/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPersistentRequestSplit

/-!
# The global admissible-stage boundary for the regular recursion

The local regular slice constructions do not by themselves give an iterable
recursion.  A successor must make two choices simultaneously:

* the family actually installed on the pending row;
* a full comparison warp carrying shadows of all completed components.

The completed displayed row need not be terminal-clean at a later frontier,
so it does not honestly carry a quotient-restoration state.  This file records
the exact source-faithful global choice consumed by the history-sensitive
splice, with no phantom residual field and no deletion/quotient commutation
assertion.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularGlobalAdmissibleProvider

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- One globally admissible regular stage.  `base` is the limit/successor row
to which the new installed family is attached.  `comparison` is used only to
prove that the installed family avoids all completed components; it is not
itself installed.  The final block contains the ladder-tight pending payload
consumed at the next recursive stage. -/
structure InstalledComparisonGeometry
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  baseStage : Ladder.Stage kappa
  base : Set G.DPath
  base_warp : G.IsWarp base
  base_finite : G.HasFiniteCharacter base
  base_initial : G.initialSet base = A
  base_extends : ∀ j (hji : j < i),
    G.ForwardExtension (previous j hji).row base
  base_freezes : ∀ j (hji : j < i),
    completedPart G (previous j hji).row ⊆ completedPart G base

  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_strict : ∀ j (hji : j < i),
    (previous j hji).stageIndex < stageIndex

  comparison : Set G.DPath
  installed : Set G.DPath
  comparison_warp : G.IsWarp comparison
  installed_subset : installed ⊆ comparison
  installed_avoids_old_strictRoof :
    G.vertexSet installed ⊆ (G.strictRoof (L.frontier baseStage))ᶜ
  completed_shadow : ∀ f ∈ completedPart G base,
    ∃ t ∈ comparison, t ∉ installed ∧
      f.support \ G.strictRoof (L.frontier baseStage) ⊆ t.support
  compatible : G.StarCompatible (pendingPart G base) installed
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)

  vertices_closed :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible) ⊆ Z
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible)))
    (L.frontier stageIndex)
    (pendingPart G (RegularCompletedPendingSplice.freezeCompletedStar
      G base installed compatible))
  pending_below_roof :
    G.vertexSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible)) ⊆
      G.roof (L.frontier stageIndex)
  pendingRequest : Set V
  pendingRequest_subset : pendingRequest ⊆ L.frontier stageIndex ∩ Z
  pendingRequest_small : #pendingRequest < kappa
  pending_status : ∀ p ∈ pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible),
    SliceSpliceConstructor.IsStagePrefix G L stageIndex p ∨
      ∃ x ∈ pendingRequest, G.terminal? p = some x

/-- The geometry installed at one regular recursion stage, together with the
two completion consequences consumed by the abstract recursive scheduler.

The consequences are separated from `InstalledComparisonGeometry` so that
the source-faithful 9.15 provider below can derive them from a single selected
terminal coverage property rather than take them as unexplained facts. -/
structure InstalledComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    extends InstalledComparisonGeometry G L Sigma Z A request i previous where

  resolves_pending : ∀ j (hji : j < i) p,
    p ∈ pendingPart G (previous j hji).row →
    (∃ x ∈ (previous j hji).pendingRequest,
      G.terminal? p = some x) →
      ∃ q ∈ completedPart G
        (RegularCompletedPendingSplice.freezeCompletedStar
          G base installed compatible), q.initial = p.initial
  realizes_request : ∀ a : A, request i = some a →
    ∃ p ∈ completedPart G
      (RegularCompletedPendingSplice.freezeCompletedStar
        G base installed compatible), p.initial = a.1

/-- An initial coordinate which the current global slice must finish.  There
are exactly two sources of such obligations: the source scheduled now, and a
component which an earlier stage marked by a small pending request. -/
def IsRequiredInitial
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (x : V) : Prop :=
  (∃ a : A, request i = some a ∧ x = a.1) ∨
    ∃ (j : Ladder.Stage kappa) (hji : j < i) (p : G.DPath),
      p ∈ pendingPart G (previous j hji).row ∧
        (∃ y ∈ (previous j hji).pendingRequest,
          G.terminal? p = some y) ∧
        x = p.initial

/-- Initial coordinates of the pending components of one recursive row
whose terminal has been registered in its small pending request. -/
def pendingRequiredInitials
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (P : RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    Set V :=
  {x | ∃ p ∈ pendingPart G P.row,
    ∃ y ∈ P.pendingRequest, G.terminal? p = some y ∧ x = p.initial}

/-- A required pending initial has a registered terminal and a witnessing
pending component. -/
theorem exists_pendingRequiredTerminal
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (P : RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (x : pendingRequiredInitials P) :
    ∃ y ∈ P.pendingRequest, ∃ p ∈ pendingPart G P.row,
      G.terminal? p = some y ∧ x.1 = p.initial := by
  obtain ⟨p, hp, y, hy, hpy, hxp⟩ := x.2
  exact ⟨y, hy, p, hp, hpy, hxp⟩

/-- Choose the registered terminal belonging to one required pending
initial.  Warp disjointness makes this choice injective. -/
noncomputable def pendingRequiredTerminal
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (P : RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (x : pendingRequiredInitials P) : P.pendingRequest :=
  ⟨Classical.choose (exists_pendingRequiredTerminal P x),
    (Classical.choose_spec (exists_pendingRequiredTerminal P x)).1⟩

theorem pendingRequiredTerminal_spec
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (P : RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (x : pendingRequiredInitials P) :
    ∃ p ∈ pendingPart G P.row,
      G.terminal? p = some (pendingRequiredTerminal P x).1 ∧
        x.1 = p.initial := by
  let h := (Classical.choose_spec
    (exists_pendingRequiredTerminal P x)).2
  let p := Classical.choose h
  refine ⟨p, (Classical.choose_spec h).1, ?_,
    (Classical.choose_spec h).2.2⟩
  exact (Classical.choose_spec h).2.1

theorem pendingRequiredTerminal_injective
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (P : RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    Function.Injective (pendingRequiredTerminal P) := by
  intro x z hxz
  obtain ⟨p, hp, hpterm, hxp⟩ := pendingRequiredTerminal_spec P x
  obtain ⟨q, hq, hqterm, hzq⟩ := pendingRequiredTerminal_spec P z
  have hterminal : (pendingRequiredTerminal P x).1 =
      (pendingRequiredTerminal P z).1 := congrArg Subtype.val hxz
  have hpq : p = q := by
    by_contra hpq
    exact Set.disjoint_left.1 (P.isWarp hp.1 hq.1 hpq)
      (G.terminal_mem_support hpterm)
      (G.terminal_mem_support (hterminal ▸ hqterm))
  apply Subtype.ext
  exact hxp.trans (hpq ▸ hzq.symm)

/-- One row contributes fewer than `kappa` required pending initials. -/
theorem mk_pendingRequiredInitials_lt
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V}
    (P : RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    #(pendingRequiredInitials P) < kappa :=
  (Cardinal.mk_le_of_injective
    (pendingRequiredTerminal_injective P)).trans_lt P.pendingRequest_small

/-- The source scheduled at the current recursion coordinate contributes at
most one required initial. -/
def currentRequiredInitials
    {kappa : Cardinal.{u}} {A : Set V}
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa) : Set V :=
  {x | ∃ a : A, request i = some a ∧ x = a.1}

theorem mk_currentRequiredInitials_lt
    {kappa : Cardinal.{u}} {A : Set V}
    (huncountable : aleph0 < kappa)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa) :
    #(currentRequiredInitials request i) < kappa := by
  cases h : request i with
  | none =>
      have hempty : currentRequiredInitials request i = ∅ := by
        ext x
        simp only [currentRequiredInitials, Set.mem_setOf_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨a, ha, _⟩
        rw [h] at ha
        contradiction
      rw [hempty, Cardinal.mk_emptyCollection]
      exact Cardinal.aleph0_pos.trans huncountable
  | some a =>
      have hsingleton : currentRequiredInitials request i = {a.1} := by
        ext x
        constructor
        · rintro ⟨b, hb, rfl⟩
          rw [h] at hb
          have hba : b = a := Option.some.inj hb.symm
          exact Set.mem_singleton_iff.2 (congrArg Subtype.val hba)
        · intro hx
          exact ⟨a, h, Set.mem_singleton_iff.1 hx⟩
      rw [hsingleton, Cardinal.mk_singleton]
      exact Cardinal.one_lt_aleph0.trans huncountable

/-- All pending initial requests appearing strictly before `i`.  The
ordinal subtype is used instead of `Iio i` so the index stays in the same
universe as `kappa`. -/
def predecessorStage
    {kappa : Cardinal.{u}} (i : Ladder.Stage kappa)
    (j : i.1.ToType) : Ladder.Stage kappa := by
  refine ⟨j.toOrd.1, ?_⟩
  change j.toOrd.1 < kappa.ord
  exact j.toOrd.2.trans (show i.1 < kappa.ord from i.2)

@[simp]
theorem predecessorStage_lt
    {kappa : Cardinal.{u}} (i : Ladder.Stage kappa)
    (j : i.1.ToType) : predecessorStage i j < i := by
  change j.toOrd.1 < i.1
  exact j.toOrd.2

@[simp]
theorem predecessorStage_toType_mk
    {kappa : Cardinal.{u}} (i j : Ladder.Stage kappa) (hji : j < i) :
    predecessorStage i (Ordinal.ToType.mk ⟨j.1, hji⟩) = j := by
  apply Subtype.ext
  change (Ordinal.ToType.mk ⟨j.1, hji⟩).toOrd.1 = j.1
  exact congrArg Subtype.val
    (Ordinal.ToType.mk.symm_apply_apply ⟨j.1, hji⟩)

def previousPendingRequiredInitials
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    Set V :=
  ⋃ j : i.1.ToType,
    pendingRequiredInitials
      (previous (predecessorStage i j) (predecessorStage_lt i j))

theorem mk_previousPendingRequiredInitials_lt
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} (hregular : kappa.IsRegular)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    #(previousPendingRequiredInitials i previous) < kappa := by
  change #(⋃ j : i.1.ToType,
    pendingRequiredInitials
      (previous (predecessorStage i j) (predecessorStage_lt i j))) < kappa
  apply mk_iUnion_lt_of_isRegular hregular
  · rw [Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp i.2
  · intro j
    exact mk_pendingRequiredInitials_lt
      (previous (predecessorStage i j) (predecessorStage_lt i j))

/-- Concrete set of all initial coordinates which the source-faithful
successor must finish. -/
def requiredInitials
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    Set V :=
  {x | IsRequiredInitial G L Sigma Z A request i previous x}

theorem requiredInitials_eq
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A} :
    requiredInitials G L Sigma Z A request i previous =
      currentRequiredInitials request i ∪
        previousPendingRequiredInitials i previous := by
  ext x
  constructor
  · intro hx
    rcases hx with hx | ⟨j, hji, p, hp, hy, rfl⟩
    · exact Or.inl hx
    · right
      change p.initial ∈ ⋃ j : i.1.ToType,
        pendingRequiredInitials
          (previous (predecessorStage i j) (predecessorStage_lt i j))
      apply Set.mem_iUnion.2
      let jo : i.1.ToType := Ordinal.ToType.mk ⟨j.1, hji⟩
      refine ⟨jo, ?_⟩
      have hstage : predecessorStage i jo = j := by
        exact predecessorStage_toType_mk i j hji
      simpa only [hstage] using
        (show p.initial ∈ pendingRequiredInitials (previous j hji) from
          ⟨p, hp, Classical.choose hy, (Classical.choose_spec hy).1,
            (Classical.choose_spec hy).2, rfl⟩)
  · rintro (hx | hx)
    · exact Or.inl hx
    · change x ∈ ⋃ j : i.1.ToType,
        pendingRequiredInitials
          (previous (predecessorStage i j) (predecessorStage_lt i j)) at hx
      obtain ⟨jo, hjo⟩ := Set.mem_iUnion.1 hx
      obtain ⟨p, hp, y, hy, hpy, rfl⟩ := hjo
      exact Or.inr
        ⟨predecessorStage i jo, predecessorStage_lt i jo, p, hp,
          ⟨y, hy, hpy⟩, rfl⟩

/-- Regularity makes the complete request at one global 9.15 successor
small. -/
theorem mk_requiredInitials_lt
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} (hregular : kappa.IsRegular)
    (huncountable : aleph0 < kappa)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) :
    #(requiredInitials G L Sigma Z A request i previous) < kappa := by
  rw [requiredInitials_eq]
  exact RegularCardinal.mk_union_lt hregular
    (mk_currentRequiredInitials_lt huncountable request i)
    (mk_previousPendingRequiredInitials_lt hregular i previous)

/-- The canonical small request made to the next 9.15 slice: terminals of
the still-pending base components whose original initials are required now.
No arbitrary provider-side choice is involved in this definition. -/
def requiredPendingTerminals
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (base : Set G.DPath) : Set V :=
  {u | ∃ p ∈ pendingPart G base,
    IsRequiredInitial G L Sigma Z A request i previous p.initial ∧
      G.terminal? p = some u}

/-- For a base which is literally one earlier recursive row, its existing
stage-status certificate is already in the exact form required by the next
canonical terminal request.  Every registered old exception has a required
initial by definition, so its same terminal belongs to
`requiredPendingTerminals`; old exact prefixes are left unchanged. -/
theorem previous_pending_status_into_requiredPendingTerminals
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (j : Ladder.Stage kappa) (hji : j < i) :
    ∀ p ∈ pendingPart G (previous j hji).row,
      SliceSpliceConstructor.IsStagePrefix G L
          (previous j hji).stageIndex p ∨
        ∃ x ∈ requiredPendingTerminals
            G L Sigma Z A request i previous (previous j hji).row,
          G.terminal? p = some x := by
  intro p hpPending
  rcases (previous j hji).pending_status p hpPending with
      hpPrefix | ⟨x, hxRequest, hpx⟩
  · exact Or.inl hpPrefix
  · right
    refine ⟨x, ?_, hpx⟩
    exact ⟨p, hpPending,
      Or.inr ⟨j, hji, p, hpPending, ⟨x, hxRequest, hpx⟩, rfl⟩,
      hpx⟩

theorem exists_mem_requiredPendingTerminals
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {base : Set G.DPath} (hfinite : G.HasFiniteCharacter base)
    {p : G.DPath} (hp : p ∈ pendingPart G base)
    (hrequired : IsRequiredInitial G L Sigma Z A request i previous
      p.initial) :
    ∃ u ∈ requiredPendingTerminals G L Sigma Z A request i previous base,
      G.terminal? p = some u := by
  obtain ⟨f, rfl⟩ := hfinite hp.1
  exact ⟨f.finish, ⟨Sum.inl f, hp, hrequired, rfl⟩, rfl⟩

noncomputable def requiredPendingPath
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (base : Set G.DPath)
    (u : requiredPendingTerminals G L Sigma Z A request i previous base) :
    G.DPath :=
  Classical.choose u.2

theorem requiredPendingPath_spec
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (base : Set G.DPath)
    (u : requiredPendingTerminals G L Sigma Z A request i previous base) :
    requiredPendingPath G L Sigma Z A request i previous base u ∈
        pendingPart G base ∧
      IsRequiredInitial G L Sigma Z A request i previous
        (requiredPendingPath G L Sigma Z A request i previous base u).initial ∧
      G.terminal?
        (requiredPendingPath G L Sigma Z A request i previous base u) =
          some u.1 :=
  Classical.choose_spec u.2

noncomputable def requiredPendingInitial
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    (base : Set G.DPath) :
    requiredPendingTerminals G L Sigma Z A request i previous base →
      requiredInitials G L Sigma Z A request i previous :=
  fun u ↦ ⟨(requiredPendingPath G L Sigma Z A request i previous base u).initial,
    (requiredPendingPath_spec G L Sigma Z A request i previous base u).2.1⟩

theorem requiredPendingInitial_injective
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {base : Set G.DPath} (hbase : G.IsWarp base) :
    Function.Injective
      (requiredPendingInitial G L Sigma Z A request i previous base) := by
  intro u v huv
  have hinit :
      (requiredPendingPath G L Sigma Z A request i previous base u).initial =
        (requiredPendingPath G L Sigma Z A request i previous base v).initial :=
    congrArg Subtype.val huv
  have hpq :
      requiredPendingPath G L Sigma Z A request i previous base u =
        requiredPendingPath G L Sigma Z A request i previous base v :=
    DWeb.IsWarp.eq_of_initial_eq G hbase
      (requiredPendingPath_spec G L Sigma Z A request i previous base u).1.1
      (requiredPendingPath_spec G L Sigma Z A request i previous base v).1.1
      hinit
  apply Subtype.ext
  apply Option.some.inj
  exact
    (requiredPendingPath_spec G L Sigma Z A request i previous base u).2.2.symm.trans
      ((congrArg (fun p : G.DPath ↦ G.terminal? p) hpq).trans
        (requiredPendingPath_spec G L Sigma Z A request i previous base v).2.2)

theorem mk_requiredPendingTerminals_le_requiredInitials
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {base : Set G.DPath} (hbase : G.IsWarp base) :
    #(requiredPendingTerminals G L Sigma Z A request i previous base) ≤
      #(requiredInitials G L Sigma Z A request i previous) :=
  Cardinal.mk_le_of_injective (requiredPendingInitial_injective hbase)

/-- The canonical terminal request passed to the global 9.15 slice is small.
This is the exact cardinal estimate required by the slice lemma. -/
theorem mk_requiredPendingTerminals_lt
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} (hregular : kappa.IsRegular)
    (huncountable : aleph0 < kappa)
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {base : Set G.DPath} (hbase : G.IsWarp base) :
    #(requiredPendingTerminals G L Sigma Z A request i previous base) <
      kappa :=
  (mk_requiredPendingTerminals_le_requiredInitials hbase).trans_lt
    (mk_requiredInitials_lt hregular huncountable request i previous)

theorem requiredPendingTerminals_subset_terminalFrontier
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {base : Set G.DPath} :
    requiredPendingTerminals G L Sigma Z A request i previous base ⊆
      G.terminalFrontier (pendingPart G base) := by
  intro u hu
  obtain ⟨p, hp, _hrequired, hpu⟩ := hu
  exact ⟨p, hp, hpu⟩

/-- Minimal source-faithful 9.15 successor datum.

The installed family is explicitly decomposed into target and clean tracks.
Instead of postulating `resolves_pending` and `realizes_request`, its selected
set is definitionally the terminals of all still-pending base components with
a required initial.  The target half of the clean slice then completes each
such component after starring. -/
structure TargetedComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V)
    (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A)
    extends InstalledComparisonGeometry G L Sigma Z A request i previous where
  slice : RegularCompletedPendingSplice.CleanTargetSlice
    G (G.terminalFrontier (pendingPart G base)) (L.frontier stageIndex)
      (requiredPendingTerminals G L Sigma Z A request i previous base)
  installed_eq : installed = slice.target ∪ slice.clean

namespace TargetedComparisonStage

/-- Normalization turns the selected target coordinate on each required
pending component into an actual target terminal.  Thus the geometric 9.15
datum supplies both completion fields of `InstalledComparisonStage`. -/
def toInstalledComparisonStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : TargetedComparisonStage G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) :
    InstalledComparisonStage G L Sigma Z A request i previous where
  toInstalledComparisonGeometry := S.toInstalledComparisonGeometry
  resolves_pending := by
    intro j hji p hp hrequested
    obtain ⟨q, hqBase, hpq⟩ := (S.base_extends j hji).1 p hp.1
    by_cases hqCompleted : q ∈ completedPart G S.base
    · refine ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base S.installed S.compatible hqCompleted, ?_⟩
      exact (G.extends_initial hpq).symm
    · have hqPending : q ∈ pendingPart G S.base :=
        ⟨hqBase, hqCompleted⟩
      have hrequired : IsRequiredInitial G L Sigma Z A request i previous
          q.initial := by
        exact Or.inr ⟨j, hji, p, hp, hrequested,
          (G.extends_initial hpq).symm⟩
      obtain ⟨u, huSelected, hqu⟩ :=
        exists_mem_requiredPendingTerminals S.base_finite hqPending hrequired
      obtain ⟨r, hrStar, hrInitial, hrTarget⟩ :=
        S.slice.exists_completed_starPath_of_installed_eq hNorm
          S.installed_eq S.compatible hqPending hqu huSelected
      refine ⟨r, ⟨Or.inr hrStar, hrTarget⟩, ?_⟩
      exact hrInitial.trans (G.extends_initial hpq).symm
  realizes_request := by
    intro a haRequest
    have haBase : a.1 ∈ G.initialSet S.base := by
      rw [S.base_initial]
      exact a.2
    obtain ⟨q, hqBase, hqInitial⟩ := haBase
    by_cases hqCompleted : q ∈ completedPart G S.base
    · refine ⟨q,
        RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
          G S.base S.installed S.compatible hqCompleted, hqInitial⟩
    · have hqPending : q ∈ pendingPart G S.base :=
        ⟨hqBase, hqCompleted⟩
      have hrequired : IsRequiredInitial G L Sigma Z A request i previous
          q.initial := by
        exact Or.inl ⟨a, haRequest, hqInitial⟩
      obtain ⟨u, huSelected, hqu⟩ :=
        exists_mem_requiredPendingTerminals S.base_finite hqPending hrequired
      obtain ⟨r, hrStar, hrInitial, hrTarget⟩ :=
        S.slice.exists_completed_starPath_of_installed_eq hNorm
          S.installed_eq S.compatible hqPending hqu huSelected
      exact ⟨r, ⟨Or.inr hrStar, hrTarget⟩,
        hrInitial.trans hqInitial⟩

end TargetedComparisonStage

namespace InstalledComparisonStage

/-- The full comparison witness proves the cross-disjointness needed to
install the selected family. -/
theorem cleanStep
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : InstalledComparisonStage G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.IsCleanTargetStep G S.base S.installed
      S.compatible := by
  exact RegularEventualCompatibility.cleanTargetStep_of_used_suffixShadow
    G S.base_warp S.comparison_warp S.installed_subset
      S.installed_avoids_old_strictRoof S.completed_shadow S.compatible

/-- Forget the comparison witness after it has discharged cross-disjointness.
The returned payload retains only data used by the recursive splice. -/
def payload
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : InstalledComparisonStage G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A where
  stageIndex := S.stageIndex
  stageIndex_mem := S.stageIndex_mem
  row := RegularCompletedPendingSplice.freezeCompletedStar
    G S.base S.installed S.compatible
  isWarp := S.cleanStep.result_isWarp
  finiteCharacter := S.cleanStep.result_finiteCharacter
    S.base_finite S.installed_star_finite
  initialSet_eq :=
    S.cleanStep.result_initialSet.trans S.base_initial
  vertices_closed := S.vertices_closed
  pending_tight := S.pending_tight
  pending_below_roof := S.pending_below_roof
  pendingRequest := S.pendingRequest
  pendingRequest_subset := S.pendingRequest_subset
  pendingRequest_small := S.pendingRequest_small
  pending_status := S.pending_status

/-- The installed comparison stage satisfies exactly the recursive validity
contract. -/
theorem valid
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : InstalledComparisonStage G L Sigma Z A request i previous) :
    RegularCompletedPendingSplice.IsValidRecursiveStage request i previous
      S.payload := by
  refine
    { index_strict := S.index_strict
      extends_previous := ?_
      freezes_completed := ?_
      resolves_pending := S.resolves_pending
      realizes_request := S.realizes_request }
  · intro j hji
    exact G.forwardExtension_trans (S.base_extends j hji)
      S.cleanStep.result_forwardExtension
  · intro j hji
    exact (S.base_freezes j hji).trans
      (RegularCompletedPendingSplice.completedPart_subset_completedPart_freezeCompletedStar
        G S.base S.installed S.compatible)

end InstalledComparisonStage

/-- The exact remaining global selection theorem in provider form.  Unlike a
bare annular-slice table, this callback must return the installed pending
family and its full comparison shadows together. -/
def HasInstalledComparisonStageProvider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A),
    (∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      Nonempty (InstalledComparisonStage G L Sigma Z A request i previous)

/-- The provider boundary corresponding directly to the global 9.15 slice
selection.  The selected set is the canonical pending-terminal request;
there is no separate provider-side completion or coverage premise. -/
def HasTargetedComparisonStageProvider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A) : Prop :=
  ∀ (i : Ladder.Stage kappa)
      (previous : ∀ j : Ladder.Stage kappa, j < i →
        RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A),
    (∀ j (hji : j < i),
      RegularCompletedPendingSplice.IsValidRecursiveStage request j
        (fun l hlj ↦ previous l (lt_trans hlj hji))
        (previous j hji)) →
      Nonempty (TargetedComparisonStage G L Sigma Z A request i previous)

/-- Forget the target/clean decomposition after normalization has derived
the two recursive completion consequences. -/
theorem hasInstalledComparisonStageProvider_of_targeted
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (hNorm : G.IsNormalized)
    (h : HasTargetedComparisonStageProvider G L Sigma Z A request) :
    HasInstalledComparisonStageProvider G L Sigma Z A request := by
  intro i previous hprevious
  obtain ⟨S⟩ := h i previous hprevious
  exact ⟨S.toInstalledComparisonStage hNorm⟩

/-- A globally admissible installed-comparison selector is sufficient for
the completed/pending splice provider. -/
theorem hasCleanTargetStepProvider_of_installedComparison
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (h : HasInstalledComparisonStageProvider G L Sigma Z A request) :
    RegularCompletedPendingSplice.HasCleanTargetStepProvider
      G L Sigma Z A request := by
  intro i previous hprevious
  obtain ⟨S⟩ := h i previous hprevious
  exact ⟨S.payload, S.valid⟩

/-- The minimal global target-coverage provider is sufficient for the whole
history-sensitive completed/pending recursion. -/
theorem hasCleanTargetStepProvider_of_targetedComparison
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    (hNorm : G.IsNormalized)
    (h : HasTargetedComparisonStageProvider G L Sigma Z A request) :
    RegularCompletedPendingSplice.HasCleanTargetStepProvider
      G L Sigma Z A request :=
  hasCleanTargetStepProvider_of_installedComparison
    (hasInstalledComparisonStageProvider_of_targeted hNorm h)

end RegularGlobalAdmissibleProvider
end CardinalInduction
end Erdos599
