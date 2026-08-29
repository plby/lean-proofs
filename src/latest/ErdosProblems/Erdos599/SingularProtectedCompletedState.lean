/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularCompletedDisplayEventualRows
import ErdosProblems.Erdos599.NestedProtectedSeparator
import ErdosProblems.Erdos599.SingularQuotientReentry

/-!
# The deleted-ambient state of the completed-only singular recursion

Only completed target paths persist literally. The still pending linkage
lives in the ambient web after deleting those paths. It is terminal-clean
at a trimmed separating boundary whose quotient is unhindered. There is
deliberately no unhinderedness field for the whole deleted ambient web.

The initial state is the empty completed packing and the trivial pending
linkage at the source. See the protected singular successor in `tex/599.tex`.
-/

noncomputable section

open Set Cardinal

namespace Erdos599.CardinalInduction.SingularProtectedCompletedState

open SingularCompletedDisplayEventualRows SingularContinuation

universe u

variable {V : Type u}

/-- The actual finite-stage protected invariant. -/
structure ProtectedCompletedState (G : DWeb V)
    extends CompletedDisplayState G where
  boundary : Set V
  pending : Set (G.delete (G.vertexSet completed)).DPath
  pending_linkage : IsLinkageBetween (G.delete (G.vertexSet completed))
    (G.delete (G.vertexSet completed)).source boundary pending
  pending_clean : TerminalCleanAt (G.delete (G.vertexSet completed))
    pending boundary
  boundary_separator : IsSeparatorFrom (G.delete (G.vertexSet completed))
    (G.delete (G.vertexSet completed)).source boundary
  boundary_trimmed : IsTrimmedSeparator (G.delete (G.vertexSet completed)) boundary
  quotient_unhindered :
    ((G.delete (G.vertexSet completed)).quotient boundary).IsUnhindered

namespace ProtectedCompletedState

variable {G : DWeb V}

/-- The ambient web for pending paths. -/
abbrev residual (S : ProtectedCompletedState G) : DWeb V :=
  G.delete (G.vertexSet S.completed)

/-- Every pending path lies below the current boundary. -/
theorem pending_roof (S : ProtectedCompletedState G) :
    S.residual.vertexSet S.pending ⊆ S.residual.roof S.boundary :=
  linkage_vertexSet_subset_roof S.residual S.pending_linkage
    S.boundary_separator S.pending_clean

/-- The pending quotient has exactly the recorded boundary as its source. -/
theorem quotient_source (S : ProtectedCompletedState G) :
    (S.residual.quotient S.boundary).source = S.boundary :=
  quotient_source_eq_stopover S.residual S.boundary_separator S.boundary_trimmed

/-- Deleting a normalized target packing removes precisely its initial
vertices from the original source. -/
theorem residual_source (hNorm : G.IsNormalized)
    (S : ProtectedCompletedState G) :
    S.residual.source = G.source \ S.sources := by
  ext a
  change (a ∈ G.source ∧ a ∉ G.vertexSet S.completed) ↔
    a ∈ G.source ∧ a ∉ S.sources
  constructor
  · rintro ⟨ha, haCarrier⟩
    refine ⟨ha, ?_⟩
    intro haS
    rw [← S.linkage.initialSet_eq] at haS
    obtain ⟨p, hp, hpa⟩ := haS
    exact haCarrier ⟨p, hp, hpa ▸ p.initial_mem_support⟩
  · rintro ⟨ha, haS⟩
    refine ⟨ha, ?_⟩
    rintro ⟨p, hp, hap⟩
    apply haS
    rw [← S.linkage.initialSet_eq]
    exact ⟨p, hp, (hNorm.eq_initial_of_mem_path p hap ha).symm⟩

/-- Normalization remains valid in the residual. -/
theorem residual_normalized (hNorm : G.IsNormalized)
    (S : ProtectedCompletedState G) : S.residual.IsNormalized :=
  SingularExtension.DWeb.IsNormalized.delete hNorm _

/-- Every auxiliary residual edge retains original adjacency. -/
theorem residual_adj_imp (S : ProtectedCompletedState G) {x y : V}
    (hxy : S.residual.graph.Adj x y) : G.graph.Adj x y := hxy.1

end ProtectedCompletedState

/-- Trivial paths give the clean linkage from a set to itself. -/
theorem trivial_self_linkage (G : DWeb V) (A : Set V) :
    IsLinkageBetween G A A (G.trivialPath '' A) := by
  refine ⟨G.isWarp_trivialPaths A, ?_, G.initialSet_trivialPaths A, ?_, ?_⟩
  · rintro _ ⟨a, _ha, rfl⟩
    exact ⟨DirectedPath.FinitePath.trivial G.graph a, rfl⟩
  · rw [G.terminalFrontier_trivialPaths]
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨DirectedPath.FinitePath.trivial G.graph a, rfl, ?_, ?_⟩ <;>
      simp [DirectedPath.FinitePath.support_trivial, ha]

/-- The trivial family is clean even if the boundary contains other points. -/
theorem trivial_terminalClean (G : DWeb V) (A C : Set V) :
    TerminalCleanAt G (G.trivialPath '' A) C := by
  rintro _ ⟨a, _ha, rfl⟩ x hx _hxC
  have hxa : x = a := by
    simpa only [G.support_trivialPath, Set.mem_singleton_iff] using hx
  subst x
  exact G.terminal?_trivialPath a

/-- The essential part of the trivial wave cannot omit a source in an
unhindered web. -/
theorem essential_source_eq (G : DWeb V) (hG : G.IsUnhindered) :
    G.essential G.source = G.source := by
  apply Set.Subset.antisymm (G.essential_subset G.source)
  intro a ha
  have hw : G.IsWave (G.essentialWarpPart G.trivialWave) :=
    G.isWave_trivialWave.essentialWarpPart
  have hi := G.isUnhindered_iff.mp hG _ hw
  have haInitial : a ∈ G.initialSet (G.essentialWarpPart G.trivialWave) :=
    hi.symm ▸ ha
  obtain ⟨p, hp, hpstart⟩ := haInitial
  rcases hp with ⟨⟨b, _hb, rfl⟩, t, hpterm, ht⟩
  have hba : b = a := by simpa using hpstart
  have hta : t = a := by
    have hbt : some b = some t := (G.terminal?_trivialPath b).trans hpterm
    exact (Option.some.inj hbt).symm.trans hba
  simpa only [G.terminalFrontier_trivialWave, hta] using ht

/-- Residual unhinderedness is sufficient to initialize a clean boundary,
but is not part of the invariant required by later protected states. -/
def ofUnhinderedResidual (G : DWeb V) (S : CompletedDisplayState G)
    (hNorm : (G.delete (G.vertexSet S.completed)).IsNormalized)
    (hH : (G.delete (G.vertexSet S.completed)).IsUnhindered) :
    ProtectedCompletedState G where
  toCompletedDisplayState := S
  boundary := (G.delete (G.vertexSet S.completed)).source
  pending := (G.delete (G.vertexSet S.completed)).trivialPath ''
    (G.delete (G.vertexSet S.completed)).source
  pending_linkage := trivial_self_linkage _ _
  pending_clean := trivial_terminalClean _ _ _
  boundary_separator := (G.delete (G.vertexSet S.completed)).subset_roof _
  boundary_trimmed := essential_source_eq _ hH
  quotient_unhindered := SingularQuotientReentry.quotient_source_isUnhindered _
    (fun {_ _} hxy hy ↦ (hNorm hxy).1 hy) hH

/-- Empty completed data needs no assumption on the web. -/
def emptyDisplay (G : DWeb V) : CompletedDisplayState G where
  sources := ∅
  sources_subset := Set.empty_subset _
  completed := ∅
  linkage := by simpa using empty_linkage G

/-- The initial protected state of the singular recursion. -/
def emptyState (G : DWeb V) (hNorm : G.IsNormalized) (hG : G.IsUnhindered) :
    ProtectedCompletedState G := by
  have hres : G.delete (G.vertexSet (emptyDisplay G).completed) = G := by
    have hempty : G.vertexSet ∅ = ∅ := by
      ext x
      simp [DWeb.vertexSet]
    change G.delete (G.vertexSet ∅) = G
    rw [hempty, G.delete_empty]
  exact ofUnhinderedResidual G (emptyDisplay G) (hres.symm ▸ hNorm) (hres.symm ▸ hG)

@[simp] theorem emptyState_sources (G : DWeb V)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered) :
    (emptyState G hNorm hG).sources = ∅ := rfl

@[simp] theorem emptyState_completed (G : DWeb V)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered) :
    (emptyState G hNorm hG).completed = ∅ := rfl

#print axioms ProtectedCompletedState.residual_source
#print axioms essential_source_eq
#print axioms emptyState

end Erdos599.CardinalInduction.SingularProtectedCompletedState
