/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BoundarySimultaneousAssignment
import ErdosProblems.Erdos599.FracturedDuplication

/-!
# Peeling singleton members before fractured-warp assignment

The occurrence-duplication proof of Remark 4.20 has one genuine endpoint
exception.  A singleton fractured member at `x` is lifted to the outgoing
copy of `x`, whereas the uniformly expanded reference path ends at the
incoming copy.  Consequently one cannot apply the ordinary boundary theorem
to all lifted members at once.

This file performs the source-faithful repair.  Reference singleton paths
which coincide with singleton fractured members are removed, and only
nontrivial fractured members are passed to the expanded-reference assignment
problem.  A singleton fractured member is either already covered by the
reference warp or is assigned the trivial alternating path downstairs.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating
open FracturedDuplication

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}

namespace FracturedAssignmentPeel

/-- Vertices which occur as singleton members of the fractured family. -/
def singletonVertices (Z : FracturedWarp Gamma) : Set V :=
  {x | Gamma.trivialPath x ∈ Z.paths}

/-- The nontrivial members of a fractured family. -/
def activePaths (Z : FracturedWarp Gamma) : Set Gamma.DPath :=
  {p | p ∈ Z.paths ∧ PathNontrivial p}

/-- Reference singleton paths already covering singleton fractured members. -/
def coveredSingletonReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) : Set Gamma.DPath :=
  Gamma.trivialPath '' singletonVertices Z ∩ Y

/-- The reference family used for the nontrivial assignment problem. -/
def activeReference
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) : Set Gamma.DPath :=
  Y \ coveredSingletonReference Z Y

/-- Occurrence-lift only the nontrivial fractured members. -/
def activeLiftedPaths (Z : FracturedWarp Gamma) :
    Set (web Gamma Z).DPath :=
  liftPath Z '' activePaths Z

private theorem walk_eq_nil_of_isPath {D : Digraph V} {x : V}
    (p : Walk D x x) (hp : p.IsPath) : p = .nil := by
  cases p with
  | nil => rfl
  | @cons _ y _ h q =>
      exact False.elim ((List.nodup_cons.mp hp).1 q.end_mem_support)

/-- A finite simple path with equal endpoints is the singleton path. -/
theorem finitePath_eq_trivial_of_start_eq_finish
    {D : Digraph V} (p : FinitePath D) (h : p.start = p.finish) :
    p = FinitePath.trivial D p.start := by
  rcases p with ⟨start, finish, walk, isPath⟩
  dsimp at h ⊢
  subst finish
  have hw : walk = .nil := walk_eq_nil_of_isPath walk isPath
  subst walk
  rfl

/-- A finite-character path which is not nontrivial is its singleton path. -/
theorem path_eq_trivial_of_not_nontrivial
    {p : Gamma.DPath} (hfinite : Gamma.HasFiniteCharacter {p})
    (htrivial : ¬ PathNontrivial p) :
    p = Gamma.trivialPath p.initial := by
  have hp : p ∈ ({p} : Set Gamma.DPath) := Set.mem_singleton p
  obtain ⟨q, rfl⟩ := hfinite hp
  have hends : q.start = q.finish := by
    by_contra hne
    apply htrivial
    exact ⟨q.start, q.start_mem_support, q.finish,
      q.finish_mem_support, hne⟩
  rw [finitePath_eq_trivial_of_start_eq_finish q hends]
  rfl

/-- A singleton fractured member which meets the reference warp is covered
by the corresponding singleton reference member. -/
theorem referencePath_eq_trivial_of_singletonHole
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    {x : V} (hxZ : Gamma.trivialPath x ∈ Z.paths)
    {q : Gamma.DPath} (hqY : q ∈ Y) (hxq : x ∈ q.support) :
    q = Gamma.trivialPath x := by
  have hxZinitial : x ∈ Gamma.initialSet Z.paths :=
    ⟨Gamma.trivialPath x, hxZ, Gamma.initial_trivialPath x⟩
  have hxZterminal : x ∈ Gamma.terminalFrontier Z.paths :=
    ⟨Gamma.trivialPath x, hxZ, Gamma.terminal?_trivialPath x⟩
  have hxYvertex : x ∈ Gamma.vertexSet Y := ⟨q, hqY, hxq⟩
  obtain ⟨qi, hqiY, hqi⟩ := hboundary.1 ⟨hxZinitial, hxYvertex⟩
  obtain ⟨qt, hqtY, hqt⟩ := hboundary.2 ⟨hxZterminal, hxYvertex⟩
  have hqqi : q = qi :=
    DWeb.IsWarp.eq_of_mem_support hY hqY hqiY hxq
      (hqi.symm ▸ qi.initial_mem_support)
  have hqqt : q = qt :=
    DWeb.IsWarp.eq_of_mem_support hY hqY hqtY hxq
      (Gamma.terminal_mem_support hqt)
  subst qi
  subst qt
  rcases q with q | r
  · have hstart : q.start = x := hqi
    have hfinish : q.finish = x := by
      simpa [DWeb.terminal?, Path.terminal?] using hqt
    rw [finitePath_eq_trivial_of_start_eq_finish q
      (hstart.trans hfinish.symm), hstart]
    rfl
  · simp [DWeb.terminal?, Path.terminal?] at hqt

/-- A singleton hole meeting `Y` is absent from the simultaneous-assignment
domain, since its initial vertex is a reference initial. -/
theorem singletonHole_initial_mem_reference
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    {x : V} (hxZ : Gamma.trivialPath x ∈ Z.paths)
    (hxY : x ∈ Gamma.vertexSet Y) :
    x ∈ Gamma.initialSet Y := by
  apply hboundary.1
  exact ⟨⟨Gamma.trivialPath x, hxZ, Gamma.initial_trivialPath x⟩, hxY⟩

theorem not_pathNontrivial_trivialPath (x : V) :
    ¬ PathNontrivial (Gamma.trivialPath x) := by
  rintro ⟨a, ha, b, hb, hab⟩
  have hax : a = x := by
    simpa [Gamma.support_trivialPath] using ha
  have hbx : b = x := by
    simpa [Gamma.support_trivialPath] using hb
  exact hab (hax.trans hbx.symm)

/-- A singleton member of a fractured family is isolated from every other
member.  This is forced by `allowed_intersection`, whose two participants
must both be nontrivial. -/
theorem eq_trivialPath_of_mem_support_singletonHole
    (Z : FracturedWarp Gamma) {x : V}
    (hxZ : Gamma.trivialPath x ∈ Z.paths)
    {p : Gamma.DPath} (hpZ : p ∈ Z.paths) (hxp : x ∈ p.support) :
    p = Gamma.trivialPath x := by
  by_contra hne
  have hmeet : ¬ Disjoint (Gamma.trivialPath x).support p.support := by
    rw [Set.not_disjoint_iff]
    exact ⟨x, by simp [Gamma.support_trivialPath], hxp⟩
  have hnontrivial := Z.allowed_intersection hxZ hpZ (Ne.symm hne) hmeet
  exact not_pathNontrivial_trivialPath x hnontrivial.1

/-- Nontrivial active members avoid all singleton-hole vertices. -/
theorem activePath_avoids_singletonVertices
    (Z : FracturedWarp Gamma) {p : Gamma.DPath}
    (hp : p ∈ activePaths Z) :
    Disjoint p.support (singletonVertices Z) := by
  rw [Set.disjoint_left]
  intro x hxp hxSingleton
  have hp0 := eq_trivialPath_of_mem_support_singletonHole Z hxSingleton hp.1 hxp
  exact not_pathNontrivial_trivialPath x (hp0 ▸ hp.2)

/-- Conversely, an uncovered singleton hole has the canonical trivial safe
assignment downstairs. -/
theorem uncoveredSingleton_has_trivialAssignment
    (hY : Gamma.IsWarp Y) (Z : FracturedWarp Gamma)
    {x : V} (hxZ : Gamma.trivialPath x ∈ Z.paths)
    (hxY : x ∉ Gamma.initialSet Y) :
    IsSafe Y (.trivial x) ∧
      (AltPath.trivial x : AltPath Gamma.graph).initial = x ∧
      (AltPath.trivial x : AltPath Gamma.graph).terminal? = some x := by
  exact ⟨Alternating.isSafe_trivial hY x, rfl, rfl⟩

theorem activePaths_subset (Z : FracturedWarp Gamma) :
    activePaths Z ⊆ Z.paths := fun _ hp => hp.1

theorem activeReference_subset (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) :
    activeReference Z Y ⊆ Y := fun _ hp => hp.1

theorem activeLiftedPaths_subset_liftedPaths (Z : FracturedWarp Gamma) :
    activeLiftedPaths Z ⊆ liftedPaths Z := by
  rintro P ⟨p, hp, rfl⟩
  exact liftPath_mem_liftedPaths Z hp.1

theorem activeLiftedPaths_isWarp (Z : FracturedWarp Gamma) :
    (web Gamma Z).IsWarp (activeLiftedPaths Z) := by
  intro p hp q hq hpq
  exact liftedPaths_isWarp Z
    (activeLiftedPaths_subset_liftedPaths Z hp)
    (activeLiftedPaths_subset_liftedPaths Z hq) hpq

theorem activeLiftedPaths_hasFiniteCharacter
    (Z : FracturedWarp Gamma)
    (hfinite : Gamma.HasFiniteCharacter Z.paths) :
    (web Gamma Z).HasFiniteCharacter (activeLiftedPaths Z) := by
  intro P hP
  exact liftedPaths_hasFiniteCharacter Z hfinite
    (activeLiftedPaths_subset_liftedPaths Z hP)

theorem activeReference_isWarp (Z : FracturedWarp Gamma)
    (hY : Gamma.IsWarp Y) :
    Gamma.IsWarp (activeReference Z Y) := by
  intro p hp q hq hpq
  exact hY hp.1 hq.1 hpq

theorem activeReference_hasFiniteCharacter (Z : FracturedWarp Gamma)
    (hfinite : Gamma.HasFiniteCharacter Y) :
    Gamma.HasFiniteCharacter (activeReference Z Y) := by
  intro p hp
  exact hfinite hp.1

/-- Removing the covered singleton components preserves the literal boundary
alignment on the nontrivial fractured members. -/
theorem boundaryAligned_active
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y) :
    BoundaryAligned (activePaths Z) (activeReference Z Y) := by
  constructor
  · rintro x ⟨⟨p, hp, hpx⟩, ⟨r, hr, hxr⟩⟩
    have hxY : x ∈ Gamma.vertexSet Y := ⟨r, hr.1, hxr⟩
    obtain ⟨q, hqY, hqx⟩ := hboundary.1
      ⟨⟨p, hp.1, hpx⟩, hxY⟩
    have hqr : q = r :=
      DWeb.IsWarp.eq_of_mem_support hY hqY hr.1
        (hqx.symm ▸ q.initial_mem_support) hxr
    subst r
    exact ⟨q, ⟨hqY, hr.2⟩, hqx⟩
  · rintro x ⟨⟨p, hp, hpx⟩, ⟨r, hr, hxr⟩⟩
    have hxY : x ∈ Gamma.vertexSet Y := ⟨r, hr.1, hxr⟩
    obtain ⟨q, hqY, hqx⟩ := hboundary.2
      ⟨⟨p, hp.1, hpx⟩, hxY⟩
    have hqr : q = r :=
      DWeb.IsWarp.eq_of_mem_support hY hqY hr.1
        (Gamma.terminal_mem_support hqx) hxr
    subst r
    exact ⟨q, ⟨hqY, hr.2⟩, hqx⟩

/-- Initials of the active reference remain initials of active nontrivial
fractured members.  The only possible failure would be a singleton hole;
the boundary lemma then identifies the reference member with the removed
singleton component. -/
theorem activeReference_initials_subset_activePaths
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Gamma.initialSet (activeReference Z Y) ⊆
      Gamma.initialSet (activePaths Z) := by
  rintro x ⟨q, hq, hqx⟩
  obtain ⟨p, hpZ, hpx⟩ := hinitial ⟨q, hq.1, hqx⟩
  by_cases hpnt : PathNontrivial p
  · exact ⟨p, ⟨hpZ, hpnt⟩, hpx⟩
  · have hpfinite : Gamma.HasFiniteCharacter ({p} : Set Gamma.DPath) := by
      intro r hr
      have hrp : r = p := by simpa using hr
      subst r
      exact hZfinite hpZ
    have hp0 : p = Gamma.trivialPath x := by
      have hp0' := path_eq_trivial_of_not_nontrivial hpfinite hpnt
      simpa [hpx] using hp0'
    have hq0 : q = Gamma.trivialPath x := by
      apply referencePath_eq_trivial_of_singletonHole Z hboundary hY
        (hp0 ▸ hpZ) hq.1
      exact hqx.symm ▸ q.initial_mem_support
    exact False.elim <| hq.2 ⟨by
      refine ⟨x, ?_, hq0.symm⟩
      change Gamma.trivialPath x ∈ Z.paths
      rw [← hp0]
      exact hpZ, hq0 ▸ hq.1⟩

/-- On active nontrivial members, deleting covered reference singleton
components does not change which initials are uncovered. -/
theorem active_initial_difference_eq
    (Z : FracturedWarp Gamma) :
    Gamma.initialSet (activePaths Z) \
        Gamma.initialSet (activeReference Z Y) =
      Gamma.initialSet (activePaths Z) \ Gamma.initialSet Y := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxActive, hxNotActiveReference⟩
    refine ⟨hxActive, ?_⟩
    intro hxY
    obtain ⟨q, hqY, hqx⟩ := hxY
    have hqNotActive : q ∉ activeReference Z Y := by
      intro hqActive
      exact hxNotActiveReference ⟨q, hqActive, hqx⟩
    have hqCovered : q ∈ coveredSingletonReference Z Y := by
      exact Classical.byContradiction fun hnot ↦
        hqNotActive ⟨hqY, hnot⟩
    rcases hqCovered.1 with ⟨y, hySingleton, hqy⟩
    have hyx : y = x := by
      have : x ∈ (Gamma.trivialPath y).support := hqy ▸
        (hqx.symm ▸ q.initial_mem_support)
      have hxy : x = y := by
        simpa [Gamma.support_trivialPath] using this
      exact hxy.symm
    subst y
    obtain ⟨p, hpActive, hpx⟩ := hxActive
    exact Set.disjoint_left.1
      (activePath_avoids_singletonVertices Z hpActive)
      (hpx.symm ▸ p.initial_mem_support) hySingleton
  · rintro x ⟨hxActive, hxNotY⟩
    refine ⟨hxActive, ?_⟩
    rintro ⟨q, hqActive, hqx⟩
    exact hxNotY ⟨q, (activeReference_subset Z Y) hqActive, hqx⟩

/-- Likewise, deleting covered reference singleton components does not
change which active finite terminals are outside the reference carrier. -/
theorem active_terminal_difference_eq
    (Z : FracturedWarp Gamma) :
    Gamma.terminalFrontier (activePaths Z) \
        Gamma.vertexSet (activeReference Z Y) =
      Gamma.terminalFrontier (activePaths Z) \ Gamma.vertexSet Y := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxActive, hxNotActiveReference⟩
    refine ⟨hxActive, ?_⟩
    rintro ⟨q, hqY, hxq⟩
    have hqNotActive : q ∉ activeReference Z Y := by
      intro hqActive
      exact hxNotActiveReference ⟨q, hqActive, hxq⟩
    have hqCovered : q ∈ coveredSingletonReference Z Y := by
      exact Classical.byContradiction fun hnot ↦
        hqNotActive ⟨hqY, hnot⟩
    rcases hqCovered.1 with ⟨y, hySingleton, hqy⟩
    have hyx : y = x := by
      have : x ∈ (Gamma.trivialPath y).support := hqy ▸ hxq
      have hxy : x = y := by
        simpa [Gamma.support_trivialPath] using this
      exact hxy.symm
    subst y
    obtain ⟨p, hpActive, hpx⟩ := hxActive
    exact Set.disjoint_left.1
      (activePath_avoids_singletonVertices Z hpActive)
      (Gamma.terminal_mem_support hpx) hySingleton
  · rintro x ⟨hxActive, hxNotY⟩
    refine ⟨hxActive, ?_⟩
    rintro ⟨q, hqActive, hxq⟩
    exact hxNotY ⟨q, (activeReference_subset Z Y) hqActive, hxq⟩

/-- The original assignment domain is the disjoint union of the active
domain and the uncovered singleton-hole vertices. -/
theorem original_initial_difference_eq_union
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths) :
    Gamma.initialSet Z.paths \ Gamma.initialSet Y =
      (Gamma.initialSet (activePaths Z) \ Gamma.initialSet Y) ∪
        (singletonVertices Z \ Gamma.initialSet Y) := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨p, hpZ, hpx⟩, hxNotY⟩
    by_cases hpnt : PathNontrivial p
    · exact Or.inl ⟨⟨p, ⟨hpZ, hpnt⟩, hpx⟩, hxNotY⟩
    · have hpfinite : Gamma.HasFiniteCharacter ({p} : Set Gamma.DPath) := by
        intro q hq
        have hqp : q = p := by simpa using hq
        subst q
        exact hZfinite hpZ
      have hp0 := path_eq_trivial_of_not_nontrivial hpfinite hpnt
      right
      refine ⟨?_, hxNotY⟩
      change Gamma.trivialPath x ∈ Z.paths
      rw [← hpx, ← hp0]
      exact hpZ
  · rintro x (hxActive | hxSingleton)
    · exact ⟨by
        obtain ⟨p, hp, hpx⟩ := hxActive.1
        exact ⟨p, hp.1, hpx⟩, hxActive.2⟩
    · exact ⟨⟨Gamma.trivialPath x, hxSingleton.1,
        Gamma.initial_trivialPath x⟩, hxSingleton.2⟩

/-- An original uncovered source which is not a singleton-hole vertex is an
active source. -/
theorem activeInitial_of_not_singleton
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    {x : V} (hx : x ∈ Gamma.initialSet Z.paths)
    (hxNotSingleton : x ∉ singletonVertices Z) :
    x ∈ Gamma.initialSet (activePaths Z) := by
  obtain ⟨p, hpZ, hpx⟩ := hx
  refine ⟨p, ⟨hpZ, ?_⟩, hpx⟩
  by_contra hpNot
  have hpfinite : Gamma.HasFiniteCharacter ({p} : Set Gamma.DPath) := by
    intro q hq
    have hqp : q = p := by simpa using hq
    subst q
    exact hZfinite hpZ
  have hp0 := path_eq_trivial_of_not_nontrivial hpfinite hpNot
  apply hxNotSingleton
  change Gamma.trivialPath x ∈ Z.paths
  rw [← hpx, ← hp0]
  exact hpZ

/-- Reindex a non-singleton original assignment source into the active
assignment domain. -/
noncomputable def toActiveSource
    (Z : FracturedWarp Gamma)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (z : {x // x ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y})
    (hz : z.1 ∉ singletonVertices Z) :
    {x // x ∈ Gamma.initialSet (activePaths Z) \ Gamma.initialSet Y} :=
  ⟨z.1, activeInitial_of_not_singleton Z hZfinite z.property.1 hz,
    z.property.2⟩

/-- Reindex an active source into the original assignment domain. -/
def ofActiveSource
    (Z : FracturedWarp Gamma)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    {x // x ∈ Gamma.initialSet Z.paths \ Gamma.initialSet Y} :=
  ⟨z.1, by
    obtain ⟨p, hp, hpx⟩ := z.property.1
    exact ⟨p, hp.1, hpx⟩, z.property.2⟩

/-- Combine a projected assignment on the active nontrivial holes with the
canonical trivial assignments at uncovered singleton holes. -/
noncomputable def combineActiveAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (A : SimultaneousAssignment (activePaths Z) Y) :
    SimultaneousAssignment Z.paths Y := by
  classical
  refine {
  assigned z := if hz : z.1 ∈ singletonVertices Z then .trivial z.1
    else A.assigned (toActiveSource Z hZfinite z hz)
  starts_at := by
    intro z
    split
    · rfl
    · exact A.starts_at _
  safe := by
    intro z
    split
    · exact Alternating.isSafe_trivial hY z.1
    · exact A.safe _
  leaving := by
    intro z
    split
    · rename_i hz
      right
      refine ⟨z.1, AltPath.terminal?_trivial z.1, ?_⟩
      intro hzY
      exact z.property.2
        (singletonHole_initial_mem_reference Z hboundary hz hzY)
    · exact A.leaving _
  maximal := by
    intro z
    split
    · rename_i hz
      right
      refine ⟨z.1, ⟨?_, ?_⟩, AltPath.terminal?_trivial z.1⟩
      · exact ⟨Gamma.trivialPath z.1, hz,
          Gamma.terminal?_trivialPath z.1⟩
      · intro hzY
        exact z.property.2
          (singletonHole_initial_mem_reference Z hboundary hz hzY)
    · rename_i hz
      rcases A.maximal (toActiveSource Z hZfinite z hz) with hinf | hfinite
      · exact Or.inl hinf
      · right
        rcases hfinite with ⟨v, hv, hterm⟩
        exact ⟨v, ⟨by
          obtain ⟨p, hp, hpterm⟩ := hv.1
          exact ⟨p, hp.1, hpterm⟩, hv.2⟩, hterm⟩
  finite_terminals_injective := by
    intro z₁ z₂ v hv₁ hv₂
    split at hv₁ <;> split at hv₂
    · rename_i hz₁ hz₂
      simp only [AltPath.terminal?_trivial, Option.some.injEq] at hv₁ hv₂
      apply Subtype.ext
      exact hv₁.trans hv₂.symm
    · rename_i hz₁ hz₂
      simp only [AltPath.terminal?_trivial, Option.some.injEq] at hv₁
      have hvSingleton : v ∈ singletonVertices Z := hv₁ ▸ hz₁
      have hvActive := A.finite_terminal_mem
        (toActiveSource Z hZfinite z₂ hz₂) hv₂
      obtain ⟨p, hpActive, hpterm⟩ := hvActive.1
      exact False.elim <| Set.disjoint_left.1
        (activePath_avoids_singletonVertices Z hpActive)
        (Gamma.terminal_mem_support hpterm) hvSingleton
    · rename_i hz₁ hz₂
      simp only [AltPath.terminal?_trivial, Option.some.injEq] at hv₂
      have hvSingleton : v ∈ singletonVertices Z := hv₂ ▸ hz₂
      have hvActive := A.finite_terminal_mem
        (toActiveSource Z hZfinite z₁ hz₁) hv₁
      obtain ⟨p, hpActive, hpterm⟩ := hvActive.1
      exact False.elim <| Set.disjoint_left.1
        (activePath_avoids_singletonVertices Z hpActive)
        (Gamma.terminal_mem_support hpterm) hvSingleton
    · rename_i hz₁ hz₂
      have hactive := A.finite_terminals_injective hv₁ hv₂
      apply Subtype.ext
      exact congrArg (fun w => w.1) hactive
  }

/-- Initials of the occurrence-lifted active family. -/
theorem initialSet_activeLiftedPaths (Z : FracturedWarp Gamma) :
    (web Gamma Z).initialSet (activeLiftedPaths Z) =
      sourceCopy Z '' Gamma.initialSet (activePaths Z) := by
  ext z
  constructor
  · rintro ⟨P, ⟨p, hp, rfl⟩, hP⟩
    rw [initial_liftPath, occurrence_initial] at hP
    exact ⟨p.initial, ⟨p, hp, rfl⟩, hP⟩
  · rintro ⟨x, ⟨p, hp, hpx⟩, rfl⟩
    refine ⟨liftPath Z p, ⟨p, hp, rfl⟩, ?_⟩
    rw [initial_liftPath, occurrence_initial, hpx]

/-- The expanded active reference and the occurrence-lifted active fractured
family satisfy exactly the boundary hypothesis of the ordinary simultaneous
assignment theorem. -/
theorem boundaryAligned_activeLifted
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hYfinite : Gamma.HasFiniteCharacter Y) :
    BoundaryAligned (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) := by
  have hactive := boundaryAligned_active Z hboundary hY
  have hactiveFinite :
      Gamma.HasFiniteCharacter (activeReference Z Y) :=
    activeReference_hasFiniteCharacter Z hYfinite
  constructor
  · rintro z ⟨hzInitial, hzReference⟩
    rw [initialSet_activeLiftedPaths] at hzInitial
    rcases hzInitial with ⟨x, hxInitial, rfl⟩
    rw [vertexSet_liftedReference Z hactiveFinite] at hzReference
    rcases hzReference with ⟨y, hyReference, hrole⟩
    have hyx : y = x := by
      simpa only [project_sourceCopy] using
        (mem_vertexBlock_project Z hrole).symm
    subst y
    have hxActiveVertex : x ∈ Gamma.vertexSet (activeReference Z Y) :=
      hyReference
    have hxActiveInitial := hactive.1 ⟨hxInitial, hxActiveVertex⟩
    rw [initialSet_liftedReference Z hactiveFinite]
    exact ⟨x, hxActiveInitial, rfl⟩
  · rintro z ⟨hzTerminal, hzReference⟩
    rcases hzTerminal with ⟨P, ⟨p, hpActive, rfl⟩, hpterm⟩
    rw [vertexSet_liftedReference Z hactiveFinite] at hzReference
    rcases hzReference with ⟨x, hxReference, hzx⟩
    have hptermOriginal : Gamma.terminal? p = some x := by
      have hmap := congrArg (Option.map project) hpterm
      rw [terminal_liftPath_projected] at hmap
      rw [show Option.map project (some z) = some (project z) from rfl,
        mem_vertexBlock_project Z hzx] at hmap
      exact hmap
    have hxActiveTerminal :
        x ∈ Gamma.terminalFrontier (activeReference Z Y) :=
      hactive.2 ⟨⟨p, hpActive, hptermOriginal⟩, hxReference⟩
    rcases hxActiveTerminal with ⟨q, hqActive, hqterm⟩
    rcases hactiveFinite hqActive with ⟨qf, rfl⟩
    refine ⟨Sum.inl (expandFinitePath Z qf),
      ⟨qf, hqActive, rfl⟩, ?_⟩
    change some (terminalCopy Z qf.finish) = some z
    have hqfinish : qf.finish = x := by
      simpa [DWeb.terminal?, Path.terminal?] using hqterm
    have hpOccurrence : occurrence Z p x = incoming x := by
      have hne : x ≠ p.initial :=
        (initial_ne_terminal_of_nontrivial hpActive.2 hptermOriginal).symm
      simp [occurrence, hne, hptermOriginal, incoming]
    have hzOccurrence : occurrence Z p x = z := by
      change (liftPath Z p).terminal? = some z at hpterm
      rw [terminal_liftPath] at hpterm
      have hptermPath : p.terminal? = some x := by
        simpa [DWeb.terminal?] using hptermOriginal
      rw [hptermPath] at hpterm
      simpa only [Option.map_some, Option.some.injEq] using hpterm
    rw [hqfinish]
    exact congrArg some (by
      change incoming x = z
      exact hpOccurrence.symm.trans hzOccurrence)

/-- The peeled and expanded problem has a simultaneous assignment retaining
the bracket-safe provenance of every selected path.  This strengthened form
is the exact upstream input for connector deletion and projection. -/
theorem exists_activeLiftedBracketAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y))) := by
  exact boundaryBracketSimultaneousAssignment (web Gamma Z)
    (activeLiftedPaths Z)
    (liftedReference Z (activeReference Z Y))
    (boundaryAligned_activeLifted Z hboundary hY hYfinite)
    (activeLiftedPaths_isWarp Z)
    (liftedReference_isWarp Z
      (activeReference_isWarp Z hY))
    (activeLiftedPaths_hasFiniteCharacter Z hZfinite)
    (liftedReference_hasFiniteCharacter Z (activeReference Z Y))
    (by
      rw [initialSet_liftedReference Z
        (activeReference_hasFiniteCharacter Z hYfinite),
        initialSet_activeLiftedPaths]
      exact Set.image_mono
        (activeReference_initials_subset_activePaths Z hboundary hY
          hZfinite hinitial))

/-- Forgetting forward-family provenance recovers the ordinary assignment
interface. -/
theorem exists_activeLiftedAssignment
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (hinitial : Gamma.initialSet Y ⊆ Gamma.initialSet Z.paths) :
    Nonempty (SimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y))) :=
  Nonempty.map BracketSimultaneousAssignment.toSimultaneousAssignment
    (exists_activeLiftedBracketAssignment Z hboundary hY hZfinite
      hYfinite hinitial)

/-! ## Abstract projection assembly -/

/-- Reindex one active downstairs source by its canonical outgoing copy in
the peeled expanded-reference problem. -/
noncomputable def toLiftedSource
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    {w // w ∈ (web Gamma Z).initialSet (activeLiftedPaths Z) \
      (web Gamma Z).initialSet
        (liftedReference Z (activeReference Z Y))} := by
  refine ⟨sourceCopy Z z.1, ?_, ?_⟩
  · rw [initialSet_activeLiftedPaths]
    exact ⟨z.1, z.property.1, rfl⟩
  · intro hzReference
    rw [initialSet_liftedReference Z
      (activeReference_hasFiniteCharacter Z hYfinite)] at hzReference
    rcases hzReference with ⟨x, hxActive, hxz⟩
    have hx : x = z.1 := sourceCopy_injective Z hxz
    subst x
    exact z.property.2 <| by
      obtain ⟨q, hqActive, hqz⟩ := hxActive
      exact ⟨q, (activeReference_subset Z Y) hqActive, hqz⟩

@[simp] theorem project_toLiftedSource
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y}) :
    project (toLiftedSource Z hYfinite z).1 = z.1 :=
  project_sourceCopy Z z.1

/-- Every finite terminal of an active lifted member is the incoming copy of
its projected vertex.  Hence projection is injective on the active lifted
terminal frontier. -/
theorem terminal_eq_incoming_project_of_mem_activeLiftedFrontier
    (Z : FracturedWarp Gamma) {z : Vertex V}
    (hz : z ∈ (web Gamma Z).terminalFrontier (activeLiftedPaths Z)) :
    z = incoming (project z) := by
  rcases hz with ⟨P, ⟨p, hpActive, rfl⟩, hpterm⟩
  have hptermOriginal : Gamma.terminal? p = some (project z) := by
    have hmap := congrArg (Option.map project) hpterm
    rw [terminal_liftPath_projected] at hmap
    simpa only [Option.map_some] using hmap
  have hpOccurrence : occurrence Z p (project z) = incoming (project z) := by
    have hne : project z ≠ p.initial :=
      (initial_ne_terminal_of_nontrivial hpActive.2 hptermOriginal).symm
    simp [occurrence, hne, hptermOriginal, incoming]
  have hzOccurrence : occurrence Z p (project z) = z := by
    change (liftPath Z p).terminal? = some z at hpterm
    rw [terminal_liftPath] at hpterm
    have hptermPath : p.terminal? = some (project z) := by
      simpa [DWeb.terminal?] using hptermOriginal
    rw [hptermPath] at hpterm
    simpa only [Option.map_some, Option.some.injEq] using hpterm
  exact hzOccurrence.symm.trans hpOccurrence

theorem project_injective_on_activeLiftedFrontier
    (Z : FracturedWarp Gamma) :
    Set.InjOn project
      ((web Gamma Z).terminalFrontier (activeLiftedPaths Z)) := by
  intro a ha b hb hab
  rw [terminal_eq_incoming_project_of_mem_activeLiftedFrontier Z ha,
    terminal_eq_incoming_project_of_mem_activeLiftedFrontier Z hb, hab]

/-- Minimal output required from connector deletion and run compression for
one selected lifted path.  It retains precisely the assignment clauses and
a witness lifting each finite terminal back to the selected upstairs path. -/
structure AssignedPathProjection
    (Z : FracturedWarp Gamma)
    (upstairs : AltPath (web Gamma Z).graph) (source : V) where
  path : AltPath Gamma.graph
  starts_at : path.initial = source
  /-- The projected path retains the forward-owner provenance of the honest
  recombination.  This is stronger than ordinary safeness and is the input
  used by the closing-set intersection argument. -/
  bracket_safe : IsBracketSafe Z.edgeWarp Y path
  safe : IsSafe Y path
  leaving : IsLeaving Y path
  maximal : path.IsInfinite ∨
    ∃ v ∈ Gamma.terminalFrontier (activePaths Z) \ Gamma.vertexSet Y,
      path.terminal? = some v
  terminal_lift : ∀ {v : V}, path.terminal? = some v →
    ∃ w : Vertex V, upstairs.terminal? = some w ∧ project w = v

/-- Assemble per-source projected paths into a simultaneous assignment on
the active nontrivial holes.  Injectivity of finite terminals is inherited
from the lifted assignment because active lifted terminals all use the
canonical incoming role. -/
noncomputable def activeAssignmentOfProjections
    (Z : FracturedWarp Gamma)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (P : ∀ z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y},
      AssignedPathProjection (Y := Y) Z
        (B.assigned (toLiftedSource Z hYfinite z)) z.1) :
    SimultaneousAssignment (activePaths Z) Y where
  assigned z := (P z).path
  starts_at z := (P z).starts_at
  safe z := (P z).safe
  leaving z := (P z).leaving
  maximal z := (P z).maximal
  finite_terminals_injective := by
    intro z₁ z₂ v hv₁ hv₂
    obtain ⟨w₁, hw₁, hpw₁⟩ := (P z₁).terminal_lift hv₁
    obtain ⟨w₂, hw₂, hpw₂⟩ := (P z₂).terminal_lift hv₂
    have hw₁frontier := B.toSimultaneousAssignment.finite_terminal_mem
      (toLiftedSource Z hYfinite z₁) hw₁
    have hw₂frontier := B.toSimultaneousAssignment.finite_terminal_mem
      (toLiftedSource Z hYfinite z₂) hw₂
    have hwEq : w₁ = w₂ :=
      project_injective_on_activeLiftedFrontier Z
        hw₁frontier.1 hw₂frontier.1 (hpw₁.trans hpw₂.symm)
    subst w₂
    have hzEq := B.finite_terminals_injective hw₁ hw₂
    apply Subtype.ext
    have hcopy : sourceCopy Z z₁.1 = sourceCopy Z z₂.1 :=
      congrArg Subtype.val hzEq
    exact sourceCopy_injective Z hcopy

/-- Final abstract assembly: once every selected active lifted path has been
projected, reinsert uncovered singleton holes and obtain the literal
fractured-family assignment. -/
noncomputable def assignmentOfActiveLiftedProjections
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (P : ∀ z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y},
      AssignedPathProjection (Y := Y) Z
        (B.assigned (toLiftedSource Z hYfinite z)) z.1) :
    SimultaneousAssignment Z.paths Y :=
  combineActiveAssignment Z hboundary hY hZfinite
    (activeAssignmentOfProjections Z hYfinite B P)

/-- A simultaneous assignment on the literal fractured family together with
the recombined-forward provenance retained by every assigned path.  The
ordinary assignment theorem deliberately forgets this information, whereas
the outside-cut closure argument needs it to prove that an assigned path
cannot leave and then re-enter the closing set. -/
structure BracketFracturedAssignment
    (Z : FracturedWarp Gamma) (Y : Set Gamma.DPath) where
  assignment : SimultaneousAssignment Z.paths Y
  bracket_safe : ∀ z, IsBracketSafe Z.edgeWarp Y (assignment.assigned z)

/-- Strengthened final assembly.  Active sources use the concrete projected
bracket certificate; uncovered singleton holes use the canonical trivial
bracket-safe path. -/
noncomputable def bracketAssignmentOfActiveLiftedProjections
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.paths)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (P : ∀ z : {x // x ∈ Gamma.initialSet (activePaths Z) \
        Gamma.initialSet Y},
      AssignedPathProjection (Y := Y) Z
        (B.assigned (toLiftedSource Z hYfinite z)) z.1) :
    BracketFracturedAssignment Z Y where
  assignment := assignmentOfActiveLiftedProjections Z hboundary hY
    hZfinite hYfinite B P
  bracket_safe := by
    intro z
    change IsBracketSafe Z.edgeWarp Y
      ((combineActiveAssignment Z hboundary hY hZfinite
        (activeAssignmentOfProjections Z hYfinite B P)).assigned z)
    simp only [combineActiveAssignment]
    split
    · exact isBracketSafe_trivial hY z.1
    · exact (P _).bracket_safe

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
