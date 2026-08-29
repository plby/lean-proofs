/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.NestedProtectedSeparator
import ErdosProblems.Erdos599.HalfwayLocalizedProtectedGeometry
import ErdosProblems.Erdos599.SingularBoundarySplit

/-!
# Source-star splice for a protected singular successor

The lower protected construction in `H / C` returns two disjoint tracks:
finite target paths `P` and a terminal-clean remainder `U`.  This file
attaches only those members of `P ∪ U` whose initial vertex is the terminal
of an actual member of the old full-source linkage `R`.  Thus unused lower
paths based at points of `C` never enter the ambient result.

The target and pending tracks are starred separately.  Their union is a
warp because both are subfamilies of the single source-star by `P ∪ U`.
The result exposes exactly the data used by the protected singular state:
a target linkage, a clean complementary linkage, carrier disjointness,
the nested boundary invariants, roof containment of the newly frozen
carrier, and the cardinal bound on newly completed owners.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularProtectedSplitSplice

open DirectedPath SingularContinuation SliceSpliceSource
open Blueprint.LinkageBlueprint.CardinalInduction

universe u

variable {V : Type u}

private theorem mk_initialSet_le_family
    (G : DWeb V) (W : Set G.DPath) :
    #(G.initialSet W) ≤ #W := by
  let f : G.initialSet W → W := fun x ↦
    ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro x y hxy
  apply Subtype.ext
  have hx := (Classical.choose_spec x.2).2
  have hy := (Classical.choose_spec y.2).2
  exact calc
    x.1 = (f x).1.initial := hx.symm
    _ = (f y).1.initial := congrArg (fun p : W ↦ p.1.initial) hxy
    _ = y.1 := hy

private theorem mk_family_le_terminalFrontier
    (G : DWeb V) {W : Set G.DPath} (hW : G.IsWarp W)
    (hterminal : ∀ p ∈ W, ∃ t, G.terminal? p = some t) :
    #W ≤ #(G.terminalFrontier W) := by
  let f : W → G.terminalFrontier W := fun p ↦
    ⟨Classical.choose (hterminal p.1 p.2), p.1, p.2,
      Classical.choose_spec (hterminal p.1 p.2)⟩
  apply Cardinal.mk_le_of_injective (f := f)
  intro p q hpq
  apply Subtype.ext
  by_contra hpne
  have htermEq : (f p).1 = (f q).1 := congrArg Subtype.val hpq
  have hpterm := Classical.choose_spec (hterminal p.1 p.2)
  have hqterm := Classical.choose_spec (hterminal q.1 q.2)
  have hpSupport : (f p).1 ∈ p.1.support :=
    G.terminal_mem_support hpterm
  have hqSupport : (f p).1 ∈ q.1.support := by
    rw [htermEq]
    exact G.terminal_mem_support hqterm
  exact Set.disjoint_left.1 (hW p.2 q.2 hpne) hpSupport hqSupport

/-- Old components whose terminal starts a lower target component. -/
def targetOld (H : DWeb V) (R : Set H.DPath) (C : Set V)
    (P : Set (H.quotient C).DPath) : Set H.DPath :=
  {r | r ∈ R ∧ ∃ t, H.terminal? r = some t ∧
    t ∈ (H.quotient C).initialSet P}

/-- Old components whose terminal starts a lower pending component. -/
def pendingOld (H : DWeb V) (R : Set H.DPath) (C : Set V)
    (U : Set (H.quotient C).DPath) : Set H.DPath :=
  {r | r ∈ R ∧ ∃ t, H.terminal? r = some t ∧
    t ∈ (H.quotient C).initialSet U}

/-- Old-boundary terminals owned by a specified set of ambient sources. -/
def requestedTerminalSet (H : DWeb V) (R : Set H.DPath)
    (requested : Set V) : Set V :=
  {c | ∃ p ∈ R, p.initial ∈ requested ∧ H.terminal? p = some c}

/-- Compatibility with the established name for the requested old
frontier. -/
theorem requestedTerminalSet_eq_requestedFrontier
    (H : DWeb V) (R : Set H.DPath) (requested : Set V) :
    requestedTerminalSet H R requested =
      SingularBoundarySplit.requestedFrontier H R requested := by
  ext c
  change (∃ p, p ∈ R ∧ p.initial ∈ requested ∧
      H.terminal? p = some c) ↔
    ∃ p, (p ∈ R ∧ p.initial ∈ requested) ∧
      H.terminal? p = some c
  constructor
  · rintro ⟨p, hp, hpa, hpc⟩
    exact ⟨p, ⟨hp, hpa⟩, hpc⟩
  · rintro ⟨p, ⟨hp, hpa⟩, hpc⟩
    exact ⟨p, hp, hpa, hpc⟩

@[simp] theorem mem_targetOld {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {P : Set (H.quotient C).DPath} {r : H.DPath} :
    r ∈ targetOld H R C P ↔
      r ∈ R ∧ ∃ t, H.terminal? r = some t ∧
        t ∈ (H.quotient C).initialSet P :=
  Iff.rfl

@[simp] theorem mem_pendingOld {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {U : Set (H.quotient C).DPath} {r : H.DPath} :
    r ∈ pendingOld H R C U ↔
      r ∈ R ∧ ∃ t, H.terminal? r = some t ∧
        t ∈ (H.quotient C).initialSet U :=
  Iff.rfl

theorem targetOld_subset {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {P : Set (H.quotient C).DPath} :
    targetOld H R C P ⊆ R :=
  fun _ h ↦ h.1

theorem pendingOld_subset {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {U : Set (H.quotient C).DPath} :
    pendingOld H R C U ⊆ R :=
  fun _ h ↦ h.1

theorem targetOld_isWarp {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {P : Set (H.quotient C).DPath}
    (hR : H.IsWarp R) : H.IsWarp (targetOld H R C P) := by
  intro p hp q hq hpq
  exact hR hp.1 hq.1 hpq

theorem pendingOld_isWarp {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {U : Set (H.quotient C).DPath}
    (hR : H.IsWarp R) : H.IsWarp (pendingOld H R C U) := by
  intro p hp q hq hpq
  exact hR hp.1 hq.1 hpq

theorem targetOld_finiteCharacter {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {P : Set (H.quotient C).DPath}
    (hR : H.HasFiniteCharacter R) :
    H.HasFiniteCharacter (targetOld H R C P) := by
  intro p hp
  exact hR hp.1

theorem pendingOld_finiteCharacter {H : DWeb V} {R : Set H.DPath}
    {C : Set V} {U : Set (H.quotient C).DPath}
    (hR : H.HasFiniteCharacter R) :
    H.HasFiniteCharacter (pendingOld H R C U) := by
  intro p hp
  exact hR hp.1

/-- The lower protected split classifies every actual old terminal. -/
theorem targetOld_union_pendingOld
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    targetOld H R C D.targetPaths ∪
        pendingOld H R C D.remainder = R := by
  apply Set.Subset.antisymm
  · exact Set.union_subset targetOld_subset pendingOld_subset
  · intro r hr
    obtain ⟨f, rfl⟩ := hR.finiteCharacter hr
    have hfinishC : f.finish ∈ C :=
      hR.terminalFrontier_subset ⟨.inl f, hr, rfl⟩
    have hfinishSource : f.finish ∈ (H.quotient C).source := by
      rw [quotient_source_eq_stopover H hCsep hCtrim]
      exact hfinishC
    have hfinishUnion : f.finish ∈
        (H.quotient C).initialSet D.targetPaths ∪
          (H.quotient C).initialSet D.remainder := by
      rw [D.source_cover]
      exact hfinishSource
    rcases hfinishUnion with hP | hU
    · exact Or.inl ⟨hr, f.finish, rfl, hP⟩
    · exact Or.inr ⟨hr, f.finish, rfl, hU⟩

/-- The old tracks are disjoint even as sets: a common member would give
a common initial vertex to the two lower families. -/
theorem disjoint_targetOld_pendingOld
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    Disjoint (targetOld H R C D.targetPaths)
      (pendingOld H R C D.remainder) := by
  apply Set.disjoint_left.2
  intro r hrP hrU
  obtain ⟨t, hrt, htP⟩ := hrP.2
  obtain ⟨u, hru, huU⟩ := hrU.2
  have htu : t = u := Option.some.inj (hrt.symm.trans hru)
  obtain ⟨p, hpP, hpt⟩ := htP
  obtain ⟨q, hqU, hqu⟩ := huU
  have htps : t ∈ p.support := by
    rw [← hpt]
    exact p.initial_mem_support
  have htqs : t ∈ q.support := by
    rw [htu, ← hqu]
    exact q.initial_mem_support
  exact Set.disjoint_left.1 (D.families_disjoint p hpP q hqU)
    htps htqs

/-- The lower target track starts inside the old boundary after lifting. -/
theorem initialSet_liftTarget_subset_oldBoundary
    {H : DWeb V} {C : Set V} {A0 : Set V} {rho : Cardinal.{u}}
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.initialSet (liftedQuotientFamily H C D.targetPaths) ⊆ C := by
  intro x hx
  rw [H.initialSet_liftQuotientFamily] at hx
  rw [← quotient_source_eq_stopover H hCsep hCtrim]
  exact D.targetPaths_initial_subset_source hx

/-- The lower pending track starts inside the old boundary after lifting. -/
theorem initialSet_liftRemainder_subset_oldBoundary
    {H : DWeb V} {C : Set V} {A0 : Set V} {rho : Cardinal.{u}}
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.initialSet (liftedQuotientFamily H C D.remainder) ⊆ C := by
  intro x hx
  rw [H.initialSet_liftQuotientFamily] at hx
  rw [← quotient_source_eq_stopover H hCsep hCtrim]
  exact D.remainder_initial_subset_source hx

/-- Compatibility for the target half of the literal source-star. -/
theorem targetCompatible
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.StarCompatible (targetOld H R C D.targetPaths)
      (liftedQuotientFamily H C D.targetPaths) := by
  apply starCompatible_liftQuotientFamily_of_roof H
  · rintro x ⟨p, hp, hxp⟩
    exact linkage_vertexSet_subset_roof H hR hCsep hRclean
      ⟨p, hp.1, hxp⟩
  · exact hCtrim
  · intro p hp
    exact hRclean p hp.1
  · simpa only [H.initialSet_liftQuotientFamily] using
      (initialSet_liftTarget_subset_oldBoundary hCsep hCtrim D)

/-- Compatibility for the pending half of the literal source-star. -/
theorem pendingCompatible
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.StarCompatible (pendingOld H R C D.remainder)
      (liftedQuotientFamily H C D.remainder) := by
  apply starCompatible_liftQuotientFamily_of_roof H
  · rintro x ⟨p, hp, hxp⟩
    exact linkage_vertexSet_subset_roof H hR hCsep hRclean
      ⟨p, hp.1, hxp⟩
  · exact hCtrim
  · intro p hp
    exact hRclean p hp.1
  · simpa only [H.initialSet_liftQuotientFamily] using
      (initialSet_liftRemainder_subset_oldBoundary hCsep hCtrim D)

/-- Ambient concatenations using lower target components.  The range is
indexed only by actual old components, so unused lower paths are ignored. -/
noncomputable def targetSplice
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    Set H.DPath :=
  H.star (targetCompatible hR hCsep hCtrim hRclean D)

/-- Ambient concatenations using lower pending components. -/
noncomputable def pendingSplice
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    Set H.DPath :=
  H.star (pendingCompatible hR hCsep hCtrim hRclean D)

theorem targetSplice_isWarp
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.IsWarp (targetSplice hR hCsep hCtrim hRclean D) := by
  exact H.isWarp_star (targetOld_isWarp hR.isWarp)
    (DWeb.IsWarp.liftQuotientFamily H D.targetPaths_isWarp)
    (targetCompatible hR hCsep hCtrim hRclean D)

theorem pendingSplice_isWarp
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.IsWarp (pendingSplice hR hCsep hCtrim hRclean D) := by
  exact H.isWarp_star (pendingOld_isWarp hR.isWarp)
    (DWeb.IsWarp.liftQuotientFamily H D.remainder_isWarp)
    (pendingCompatible hR hCsep hCtrim hRclean D)

theorem targetSplice_finiteCharacter
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.HasFiniteCharacter (targetSplice hR hCsep hCtrim hRclean D) := by
  apply hasFiniteCharacter_star (targetOld_finiteCharacter hR.finiteCharacter)
  · rintro q ⟨q0, hq0, rfl⟩
    obtain ⟨f, rfl⟩ := D.targetPaths_finite hq0
    exact ⟨f.lift (fun {_ _} h ↦ H.quotient_adj_imp h), rfl⟩

theorem pendingSplice_finiteCharacter
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.HasFiniteCharacter (pendingSplice hR hCsep hCtrim hRclean D) := by
  apply hasFiniteCharacter_star (pendingOld_finiteCharacter hR.finiteCharacter)
  · rintro q ⟨q0, hq0, rfl⟩
    obtain ⟨f, rfl⟩ := D.remainder_finite hq0
    exact ⟨f.lift (fun {_ _} h ↦ H.quotient_adj_imp h), rfl⟩

theorem terminalFrontier_targetOld_subset_initialTarget
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {P : Set (H.quotient C).DPath} :
    H.terminalFrontier (targetOld H R C P) ⊆
      (H.quotient C).initialSet P := by
  rintro x ⟨r, hr, hrx⟩
  obtain ⟨t, hrt, htP⟩ := hr.2
  have hxt : x = t := Option.some.inj (hrx.symm.trans hrt)
  exact hxt ▸ htP

theorem terminalFrontier_pendingOld_subset_initialRemainder
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {U : Set (H.quotient C).DPath} :
    H.terminalFrontier (pendingOld H R C U) ⊆
      (H.quotient C).initialSet U := by
  rintro x ⟨r, hr, hrx⟩
  obtain ⟨t, hrt, htU⟩ := hr.2
  have hxt : x = t := Option.some.inj (hrx.symm.trans hrt)
  exact hxt ▸ htU

/-- Every target splice really terminates in the ambient target. -/
theorem targetSplice_terminalFrontier_subset_target
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.terminalFrontier (targetSplice hR hCsep hCtrim hRclean D) ⊆
      H.target := by
  have hcover : H.terminalFrontier (targetOld H R C D.targetPaths) ⊆
      H.initialSet (liftedQuotientFamily H C D.targetPaths) := by
    simpa only [H.initialSet_liftQuotientFamily] using
      (terminalFrontier_targetOld_subset_initialTarget
        (H := H) (R := R) (C := C) (P := D.targetPaths))
  have hfront := terminalFrontier_star_subset
    (targetOld_finiteCharacter hR.finiteCharacter)
    (targetCompatible hR hCsep hCtrim hRclean D) hcover
  intro x hx
  apply D.targetPaths_terminal_target
  rw [← H.terminalFrontier_liftQuotientFamily C D.targetPaths]
  exact hfront hx

theorem pendingSplice_terminalFrontier_subset_newBoundary
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.terminalFrontier (pendingSplice hR hCsep hCtrim hRclean D) ⊆
      D.stopover := by
  have hcover : H.terminalFrontier (pendingOld H R C D.remainder) ⊆
      H.initialSet (liftedQuotientFamily H C D.remainder) := by
    simpa only [H.initialSet_liftQuotientFamily] using
      (terminalFrontier_pendingOld_subset_initialRemainder
        (H := H) (R := R) (C := C) (U := D.remainder))
  have hfront := terminalFrontier_star_subset
    (pendingOld_finiteCharacter hR.finiteCharacter)
    (pendingCompatible hR hCsep hCtrim hRclean D) hcover
  intro x hx
  apply D.remainder_terminal_stopover
  rw [← H.terminalFrontier_liftQuotientFamily C D.remainder]
  exact hfront hx

/-- The old linkage meets the nested boundary only at its terminal. -/
theorem old_meetsOnlyAtTerminal_newBoundary
    {H : DWeb V} (hNorm : H.IsNormalized)
    {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    MeetsOnlyAtTerminal H R D.stopover := by
  have hNoEnter : H.NoEdgeEnters H.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  apply meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
    hCtrim (linkage_vertexSet_subset_roof H hR hCsep hRclean) hRclean
  simpa only [disjoint_comm] using
    (NestedProtectedSeparator.disjoint_new_strictRoof_old H
      hNoEnter hCsep D.stopover_separator D.stopover_trimmed)

/-- Lifting preserves the terminal-clean certificate of the lower
pending track. -/
theorem liftedRemainder_meetsOnlyAtTerminal
    {H : DWeb V} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    MeetsOnlyAtTerminal H
      (liftedQuotientFamily H C D.remainder) D.stopover := by
  intro p hp x hxp hxD
  obtain ⟨q, hq, rfl⟩ := hp
  have hxq : x ∈ q.support := by
    simpa only [H.support_liftQuotientPath] using hxp
  simpa only [H.terminal?_liftQuotientPath] using
    (D.remainder_terminalClean q hq x hxq hxD)

/-- The pending ambient splice remains terminal-clean at the new boundary.
The old prefix is clean there by nested strict-roof disjointness, and the
lower remainder is clean there by construction. -/
theorem pendingSplice_terminalClean
    {H : DWeb V} (hNorm : H.IsNormalized)
    {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    TerminalCleanAt H (pendingSplice hR hCsep hCtrim hRclean D)
      D.stopover := by
  have hcover : H.terminalFrontier (pendingOld H R C D.remainder) ⊆
      H.initialSet (liftedQuotientFamily H C D.remainder) := by
    simpa only [H.initialSet_liftQuotientFamily] using
      (terminalFrontier_pendingOld_subset_initialRemainder
        (H := H) (R := R) (C := C) (U := D.remainder))
  apply meetsOnlyAtTerminal_star
    (pendingOld_finiteCharacter hR.finiteCharacter)
  · intro p hp
    exact old_meetsOnlyAtTerminal_newBoundary hNorm hR hCsep hCtrim
      hRclean D p hp.1
  · exact liftedRemainder_meetsOnlyAtTerminal D
  · exact hcover

/-- The newly frozen target carrier is roofed by the nested boundary in
the original web. -/
theorem targetSplice_vertexSet_subset_newRoof
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.vertexSet (targetSplice hR hCsep hCtrim hRclean D) ⊆
      H.roof D.stopover := by
  apply vertexSet_star_subset_roof
    (targetCompatible hR hCsep hCtrim hRclean D)
  · exact NestedProtectedSeparator.old_subset_roof_new H
      hCsep hCtrim D.stopover_separator
  · rintro x ⟨p, hp, hxp⟩
    exact linkage_vertexSet_subset_roof H hR hCsep hRclean
      ⟨p, hp.1, hxp⟩
  · rintro x ⟨p, hp, hxp⟩
    obtain ⟨q, hq, rfl⟩ := hp
    apply NestedProtectedSeparator.quotient_roof_subset_original H
      hCsep hCtrim D.stopover_separator
    apply D.targetPaths_carrier_roof
    exact ⟨q, hq, by simpa only [H.support_liftQuotientPath] using hxp⟩

/-- The target and pending concatenations have disjoint carriers.  The four
possible old/new support cases reduce respectively to disjointness of the
old linkage, disjointness of the lower `P/U` tracks at their common start,
and disjointness of the lower tracks themselves. -/
theorem disjoint_vertexSet_targetSplice_pendingSplice
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    Disjoint
      (H.vertexSet (targetSplice hR hCsep hCtrim hRclean D))
      (H.vertexSet (pendingSplice hR hCsep hCtrim hRclean D)) := by
  let Lp := liftedQuotientFamily H C D.targetPaths
  let Lu := liftedQuotientFamily H C D.remainder
  let hcP := targetCompatible hR hCsep hCtrim hRclean D
  let hcU := pendingCompatible hR hCsep hCtrim hRclean D
  have hRroof : H.vertexSet R ⊆ H.roof C :=
    linkage_vertexSet_subset_roof H hR hCsep hRclean
  have hRP : H.StarCompatible R Lp := by
    apply starCompatible_liftQuotientFamily_of_roof H
      hRroof hCtrim hRclean
    simpa only [Lp, H.initialSet_liftQuotientFamily] using
      (initialSet_liftTarget_subset_oldBoundary hCsep hCtrim D)
  have hRU : H.StarCompatible R Lu := by
    apply starCompatible_liftQuotientFamily_of_roof H
      hRroof hCtrim hRclean
    simpa only [Lu, H.initialSet_liftQuotientFamily] using
      (initialSet_liftRemainder_subset_oldBoundary hCsep hCtrim D)
  apply Set.disjoint_left.2
  intro x hxTarget hxPending
  obtain ⟨rt, ⟨oldt, rfl⟩, hxTarget⟩ := hxTarget
  obtain ⟨ru, ⟨oldu, rfl⟩, hxPending⟩ := hxPending
  rcases H.mem_support_starPath_cases hcP oldt hxTarget with
      hxTargetOld | hxTargetNew
  · rcases H.mem_support_starPath_cases hcU oldu hxPending with
        hxPendingOld | hxPendingNew
    · have hne : oldt.1 ≠ oldu.1 := by
        intro heq
        have holdEq : oldt.1 = oldu.1 := heq
        have hmemU : oldt.1 ∈ pendingOld H R C D.remainder := by
          rw [holdEq]
          exact oldu.2
        exact Set.disjoint_left.1 (disjoint_targetOld_pendingOld D)
          oldt.2 hmemU
      exact Set.disjoint_left.1
        (hR.isWarp oldt.2.1 oldu.2.1 hne) hxTargetOld hxPendingOld
    · obtain ⟨_tu, qu, _huTerm, hquLu, _hquStart, hxqu⟩ := hxPendingNew
      have hmeet := hRU oldt.1 oldt.2.1 qu hquLu x hxTargetOld hxqu
      obtain ⟨t, htTerm, htP⟩ := oldt.2.2
      have htx : t = x := Option.some.inj (htTerm.symm.trans hmeet.1)
      obtain ⟨p0, hp0P, hp0Start⟩ := htP
      obtain ⟨u0, hu0U, rfl⟩ := hquLu
      have hxP : x ∈ p0.support := by
        rw [← htx, ← hp0Start]
        exact p0.initial_mem_support
      have hxU : x ∈ u0.support := by
        rw [← H.support_liftQuotientPath]
        exact hxqu
      exact Set.disjoint_left.1 (D.families_disjoint p0 hp0P u0 hu0U)
        hxP hxU
  · obtain ⟨_tt, pt, _htTerm, hptLp, _hptStart, hxpt⟩ := hxTargetNew
    rcases H.mem_support_starPath_cases hcU oldu hxPending with
        hxPendingOld | hxPendingNew
    · have hmeet := hRP oldu.1 oldu.2.1 pt hptLp x hxPendingOld hxpt
      obtain ⟨t, htTerm, htU⟩ := oldu.2.2
      have htx : t = x := Option.some.inj (htTerm.symm.trans hmeet.1)
      obtain ⟨u0, hu0U, hu0Start⟩ := htU
      obtain ⟨p0, hp0P, rfl⟩ := hptLp
      have hxP : x ∈ p0.support := by
        rw [← H.support_liftQuotientPath]
        exact hxpt
      have hxU : x ∈ u0.support := by
        rw [← htx, ← hu0Start]
        exact u0.initial_mem_support
      exact Set.disjoint_left.1 (D.families_disjoint p0 hp0P u0 hu0U)
        hxP hxU
    · obtain ⟨_tu, qu, _huTerm, hquLu, _hquStart, hxqu⟩ := hxPendingNew
      obtain ⟨p0, hp0P, rfl⟩ := hptLp
      obtain ⟨u0, hu0U, rfl⟩ := hquLu
      have hxP : x ∈ p0.support := by
        simpa only [H.support_liftQuotientPath] using hxpt
      have hxU : x ∈ u0.support := by
        simpa only [H.support_liftQuotientPath] using hxqu
      exact Set.disjoint_left.1 (D.families_disjoint p0 hp0P u0 hu0U)
        hxP hxU

theorem splice_union_isWarp
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.IsWarp
      (targetSplice hR hCsep hCtrim hRclean D ∪
        pendingSplice hR hCsep hCtrim hRclean D) :=
  isWarp_union_of_disjoint_vertexSet H
    (targetSplice_isWarp hR hCsep hCtrim hRclean D)
    (pendingSplice_isWarp hR hCsep hCtrim hRclean D)
    (disjoint_vertexSet_targetSplice_pendingSplice
      hR hCsep hCtrim hRclean D)

theorem splice_union_finiteCharacter
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.HasFiniteCharacter
      (targetSplice hR hCsep hCtrim hRclean D ∪
        pendingSplice hR hCsep hCtrim hRclean D) :=
  finiteCharacter_union H
    (targetSplice_finiteCharacter hR hCsep hCtrim hRclean D)
    (pendingSplice_finiteCharacter hR hCsep hCtrim hRclean D)

theorem splice_initialSet_cover
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.initialSet (targetSplice hR hCsep hCtrim hRclean D) ∪
      H.initialSet (pendingSplice hR hCsep hCtrim hRclean D) =
        H.source := by
  rw [targetSplice, pendingSplice,
    initialSet_star_eq, initialSet_star_eq,
    ← H.initialSet_union,
    targetOld_union_pendingOld hR hCsep hCtrim D,
    hR.initialSet_eq]

theorem targetSplice_initialSet_subset_source
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.initialSet (targetSplice hR hCsep hCtrim hRclean D) ⊆
      H.source := by
  intro x hx
  rw [← splice_initialSet_cover hR hCsep hCtrim hRclean D]
  exact Or.inl hx

theorem pendingSplice_initialSet_eq_compl
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    H.initialSet (pendingSplice hR hCsep hCtrim hRclean D) =
      H.source \ H.initialSet
        (targetSplice hR hCsep hCtrim hRclean D) := by
  let T := targetSplice hR hCsep hCtrim hRclean D
  let U := pendingSplice hR hCsep hCtrim hRclean D
  have hcover : H.initialSet T ∪ H.initialSet U = H.source :=
    splice_initialSet_cover hR hCsep hCtrim hRclean D
  have hdis : Disjoint (H.initialSet T) (H.initialSet U) := by
    apply Set.disjoint_left.2
    intro x hxT hxU
    obtain ⟨p, hpT, hpx⟩ := hxT
    obtain ⟨q, hqU, hqx⟩ := hxU
    exact Set.disjoint_left.1
      (disjoint_vertexSet_targetSplice_pendingSplice
        hR hCsep hCtrim hRclean D)
      ⟨p, hpT, hpx ▸ p.initial_mem_support⟩
      ⟨q, hqU, hqx ▸ q.initial_mem_support⟩
  apply Set.Subset.antisymm
  · intro x hxU
    refine ⟨?_, ?_⟩
    · rw [← hcover]
      exact Or.inr hxU
    · intro hxT
      exact Set.disjoint_left.1 hdis hxT hxU
  · rintro x ⟨hxSource, hxNotT⟩
    rw [← hcover] at hxSource
    exact hxSource.resolve_left hxNotT

/-- The target splice is an exact linkage from the newly completed owners
to the ambient target. -/
theorem targetSplice_isLinkageBetween
    {H : DWeb V} (hNorm : H.IsNormalized)
    {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    IsLinkageBetween H
      (H.initialSet (targetSplice hR hCsep hCtrim hRclean D))
      H.target (targetSplice hR hCsep hCtrim hRclean D) := by
  let T := targetSplice hR hCsep hCtrim hRclean D
  have hTwarp := targetSplice_isWarp hR hCsep hCtrim hRclean D
  have hTfinite : H.HasFiniteCharacter T := by
    intro p hp
    exact targetSplice_finiteCharacter
      hR hCsep hCtrim hRclean D hp
  have hTinitial : H.initialSet T ⊆ H.source :=
    targetSplice_initialSet_subset_source hR hCsep hCtrim hRclean D
  have hTterminal : H.terminalFrontier T ⊆ H.target :=
    targetSplice_terminalFrontier_subset_target
      hR hCsep hCtrim hRclean D
  refine ⟨hTwarp, hTfinite, rfl, hTterminal, ?_⟩
  intro p hp
  obtain ⟨f, rfl⟩ := hTfinite hp
  have hfInitial : f.start ∈ H.initialSet T := ⟨.inl f, hp, rfl⟩
  have hfTarget : f.finish ∈ H.target :=
    hTterminal ⟨.inl f, hp, rfl⟩
  have hsource : f.support ∩ H.initialSet T = {f.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxInitial⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path (.inl f) hxf
          (hTinitial hxInitial))
    · intro x hx
      have hxeq : x = f.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, hfInitial⟩
  have htarget : f.support ∩ H.target = {f.finish} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxTarget⟩
      exact Set.mem_singleton_iff.2
        (Option.some.inj (hNorm.terminal?_eq_of_mem_path
          (.inl f) hxf hxTarget)).symm
    · intro x hx
      have hxeq : x = f.finish := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.finish_mem_support, hfTarget⟩
  refine ⟨f, rfl, ?_, hsource⟩
  rw [Set.inter_union_distrib_left, hsource, htarget]
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]

/-- The pending splice is an exact linkage from the complementary source
set to the new boundary. -/
theorem pendingSplice_isLinkageBetween
    {H : DWeb V} (hNorm : H.IsNormalized)
    {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    IsLinkageBetween H
      (H.source \ H.initialSet
        (targetSplice hR hCsep hCtrim hRclean D))
      D.stopover (pendingSplice hR hCsep hCtrim hRclean D) := by
  let U := pendingSplice hR hCsep hCtrim hRclean D
  let A := H.source \ H.initialSet
    (targetSplice hR hCsep hCtrim hRclean D)
  have hUwarp := pendingSplice_isWarp hR hCsep hCtrim hRclean D
  have hUfinite : H.HasFiniteCharacter U := by
    intro p hp
    exact pendingSplice_finiteCharacter
      hR hCsep hCtrim hRclean D hp
  have hUinitial : H.initialSet U = A :=
    pendingSplice_initialSet_eq_compl hR hCsep hCtrim hRclean D
  have hUterminal : H.terminalFrontier U ⊆ D.stopover :=
    pendingSplice_terminalFrontier_subset_newBoundary
      hR hCsep hCtrim hRclean D
  have hUclean : TerminalCleanAt H U D.stopover :=
    pendingSplice_terminalClean hNorm hR hCsep hCtrim hRclean D
  refine ⟨hUwarp, hUfinite, hUinitial, hUterminal, ?_⟩
  intro p hp
  obtain ⟨f, rfl⟩ := hUfinite hp
  have hfInitial : f.start ∈ A := by
    rw [← hUinitial]
    exact ⟨.inl f, hp, rfl⟩
  have hfFinish : f.finish ∈ D.stopover :=
    hUterminal ⟨.inl f, hp, rfl⟩
  have hsource : f.support ∩ A = {f.start} := by
    apply Set.Subset.antisymm
    · rintro x ⟨hxf, hxA⟩
      exact Set.mem_singleton_iff.2
        (hNorm.eq_initial_of_mem_path (.inl f) hxf hxA.1)
    · intro x hx
      have hxeq : x = f.start := Set.mem_singleton_iff.1 hx
      subst x
      exact ⟨f.start_mem_support, hfInitial⟩
  refine ⟨f, rfl, ?_, hsource⟩
  apply Set.Subset.antisymm
  · rintro x ⟨hxf, hxA | hxD⟩
    · have hx : x ∈ ({f.start} : Set V) := by
        rw [← hsource]
        exact ⟨hxf, hxA⟩
      exact Set.mem_insert_iff.2 (Or.inl (Set.mem_singleton_iff.1 hx))
    · have hxTerm : H.terminal? (.inl f : H.DPath) = some x :=
        hUclean (.inl f) hp x hxf hxD
      exact Set.mem_insert_iff.2
        (Or.inr (Set.mem_singleton_iff.2
          (Option.some.inj hxTerm).symm))
  · rintro x (hxStart | hxFinish)
    · subst x
      exact ⟨f.start_mem_support, Or.inl hfInitial⟩
    · have hxeq : x = f.finish := Set.mem_singleton_iff.1 hxFinish
      subst x
      exact ⟨f.finish_mem_support, Or.inr hfFinish⟩

/-- The number of owners completed by this batch is bounded by the number
of lower target paths.  Extra lower paths based at unused points of `C`
only enlarge the right-hand side and never enter the splice. -/
theorem targetSplice_initialSet_card_le_targetPaths
    {H : DWeb V} {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    #(H.initialSet (targetSplice hR hCsep hCtrim hRclean D)) ≤
      #D.targetPaths := by
  calc
    #(H.initialSet (targetSplice hR hCsep hCtrim hRclean D)) =
        #(H.initialSet (targetOld H R C D.targetPaths)) := by
      rw [targetSplice, initialSet_star_eq]
    _ ≤ #(targetOld H R C D.targetPaths) :=
      mk_initialSet_le_family H _
    _ ≤ #(H.terminalFrontier (targetOld H R C D.targetPaths)) := by
      apply mk_family_le_terminalFrontier H
        (targetOld_isWarp hR.isWarp)
      intro p hp
      obtain ⟨t, hpt, _ht⟩ := hp.2
      exact ⟨t, hpt⟩
    _ ≤ #((H.quotient C).initialSet D.targetPaths) :=
      Cardinal.mk_subtype_mono
        (terminalFrontier_targetOld_subset_initialTarget
          (H := H) (R := R) (C := C) (P := D.targetPaths))
    _ ≤ #D.targetPaths := mk_initialSet_le_family (H.quotient C) _

/-- The nested lower boundary separates all ambient sources. -/
theorem newBoundary_separator
    {H : DWeb V} {C : Set V} {A0 : Set V} {rho : Cardinal.{u}}
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    IsSeparatorFrom H H.source D.stopover :=
  NestedProtectedSeparator.new_isSeparator H
    hCsep hCtrim D.stopover_separator

/-- Normalization transports trimmedness of the nested lower boundary to
the ambient web. -/
theorem newBoundary_trimmed
    {H : DWeb V} (hNorm : H.IsNormalized)
    {C : Set V} {A0 : Set V} {rho : Cardinal.{u}}
    (hCsep : IsSeparatorFrom H H.source C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    IsTrimmedSeparator H D.stopover := by
  have hNoEnter : H.NoEdgeEnters H.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  exact NestedProtectedSeparator.new_isTrimmed H hNoEnter hCsep
    D.stopover_separator D.stopover_trimmed

/-- The ambient quotient at the nested boundary is the lower iterated
quotient and is therefore unhindered. -/
theorem newBoundary_quotient_unhindered
    {H : DWeb V} (hNorm : H.IsNormalized)
    {C : Set V} {A0 : Set V} {rho : Cardinal.{u}}
    (hCsep : IsSeparatorFrom H H.source C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    (H.quotient D.stopover).IsUnhindered := by
  have hNoEnter : H.NoEdgeEnters H.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  rw [NestedProtectedSeparator.quotient_new_eq_iterated H hNoEnter hCsep
    D.stopover_separator D.stopover_trimmed]
  exact D.original_quotient_unhindered

/-- The complete protected source-star transaction.  Besides the two
linkages consumed by the completed-state successor, the record retains the
single-warp and full-source-cover facts of the literal split. -/
structure ProtectedSplitSpliceResult
    (H : DWeb V) (newOwnerBound : Cardinal.{u}) where
  sources : Set V
  sources_subset : sources ⊆ H.source
  targetPaths : Set H.DPath
  target_linkage : IsLinkageBetween H sources H.target targetPaths
  boundary : Set V
  pending : Set H.DPath
  pending_linkage :
    IsLinkageBetween H (H.source \ sources) boundary pending
  pending_clean : TerminalCleanAt H pending boundary
  families_disjoint :
    Disjoint (H.vertexSet pending) (H.vertexSet targetPaths)
  whole_isWarp : H.IsWarp (targetPaths ∪ pending)
  whole_finite : H.HasFiniteCharacter (targetPaths ∪ pending)
  source_cover :
    H.initialSet targetPaths ∪ H.initialSet pending = H.source
  boundary_separator : IsSeparatorFrom H H.source boundary
  boundary_trimmed : IsTrimmedSeparator H boundary
  quotient_unhindered : (H.quotient boundary).IsUnhindered
  target_carrier_roof : H.vertexSet targetPaths ⊆ H.roof boundary
  sources_card : #sources ≤ newOwnerBound

/-- Build the protected transaction from an old clean full-source linkage
and the checked lower protected geometry.  Its bound counts the entire
lower target family; only paths attached to actual old terminals appear in
the result. -/
noncomputable def protectedSplitSplice
    {H : DWeb V} (hNorm : H.IsNormalized)
    {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    ProtectedSplitSpliceResult H (#D.targetPaths) where
  sources := H.initialSet
    (targetSplice hR hCsep hCtrim hRclean D)
  sources_subset :=
    targetSplice_initialSet_subset_source hR hCsep hCtrim hRclean D
  targetPaths := targetSplice hR hCsep hCtrim hRclean D
  target_linkage :=
    targetSplice_isLinkageBetween hNorm hR hCsep hCtrim hRclean D
  boundary := D.stopover
  pending := pendingSplice hR hCsep hCtrim hRclean D
  pending_linkage :=
    pendingSplice_isLinkageBetween hNorm hR hCsep hCtrim hRclean D
  pending_clean :=
    pendingSplice_terminalClean hNorm hR hCsep hCtrim hRclean D
  families_disjoint :=
    (disjoint_vertexSet_targetSplice_pendingSplice
      hR hCsep hCtrim hRclean D).symm
  whole_isWarp := splice_union_isWarp hR hCsep hCtrim hRclean D
  whole_finite := splice_union_finiteCharacter hR hCsep hCtrim hRclean D
  source_cover := splice_initialSet_cover hR hCsep hCtrim hRclean D
  boundary_separator := newBoundary_separator hCsep hCtrim D
  boundary_trimmed := newBoundary_trimmed hNorm hCsep D
  quotient_unhindered := newBoundary_quotient_unhindered hNorm hCsep D
  target_carrier_roof :=
    targetSplice_vertexSet_subset_newRoof hR hCsep hCtrim hRclean D
  sources_card :=
    targetSplice_initialSet_card_le_targetPaths
      hR hCsep hCtrim hRclean D

/-- The lower protected cardinal estimate also bounds the actual newly
completed source set. -/
theorem protectedSplitSplice_sources_card_le
    {H : DWeb V} (hNorm : H.IsNormalized)
    {R : Set H.DPath} {C : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho) :
    #(protectedSplitSplice hNorm hR hCsep hCtrim hRclean D).sources ≤ rho :=
  (protectedSplitSplice hNorm hR hCsep hCtrim hRclean D).sources_card.trans
    D.targetPaths_card

/-- If every old terminal belonging to a requested source is designated
for the lower target track, then every requested source is completed by the
literal ambient splice.  No exact-frontier hypothesis is used: the old
full-source linkage supplies the unique actual owner, and unused lower
paths are ignored. -/
theorem requested_subset_protectedSplitSplice_sources
    {H : DWeb V} (hNorm : H.IsNormalized)
    {R : Set H.DPath} {C requested : Set V}
    {A0 : Set V} {rho : Cardinal.{u}}
    (hR : IsLinkageBetween H H.source C R)
    (hCsep : IsSeparatorFrom H H.source C)
    (hCtrim : IsTrimmedSeparator H C)
    (hRclean : TerminalCleanAt H R C)
    (D : LocalizedProtectedHalfwayGeometry (H.quotient C) A0 rho)
    (hrequested : requested ⊆ H.source)
    (hdesignated : requestedTerminalSet H R requested ⊆ A0) :
    requested ⊆
      (protectedSplitSplice hNorm hR hCsep hCtrim hRclean D).sources := by
  intro a ha
  have haInitial : a ∈ H.initialSet R := by
    rw [hR.initialSet_eq]
    exact hrequested ha
  obtain ⟨p, hp, hpa⟩ := haInitial
  obtain ⟨f, rfl⟩ := hR.finiteCharacter hp
  change f.start = a at hpa
  have hfRequested : f.start ∈ requested := by
    rw [hpa]
    exact ha
  have hfTerminal : H.terminal? (.inl f : H.DPath) = some f.finish :=
    H.terminal?_finite f
  have hfDesignated : f.finish ∈ A0 := hdesignated
    ⟨.inl f, hp, hfRequested, hfTerminal⟩
  have hfLowerInitial :
      f.finish ∈ (H.quotient C).initialSet D.targetPaths :=
    D.designated_initial hfDesignated
  change a ∈ H.initialSet
    (targetSplice hR hCsep hCtrim hRclean D)
  rw [targetSplice, initialSet_star_eq]
  exact ⟨.inl f, ⟨hp, f.finish, hfTerminal, hfLowerInitial⟩, hpa⟩

#print axioms protectedSplitSplice
#print axioms protectedSplitSplice_sources_card_le
#print axioms requested_subset_protectedSplitSplice_sources

end SingularProtectedSplitSplice
end CardinalInduction
end Erdos599
