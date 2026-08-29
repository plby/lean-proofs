/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BoundarySimultaneousAssignment

/-!
# A finite-character proxy for a reference warp containing rays

The simultaneous-assignment theorem in Section 4 is stated for a
finite-character reference warp.  At the Section 9 application the reference
is a limiting ladder warp and may contain rays.  For a boundary-aligned
assignment problem, a ray can be replaced by the singleton path at its
initial vertex: this preserves the reference initial set, while every genuine
backward link is still forced to use one of the retained finite members.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Keep a finite path unchanged and replace a ray by the singleton path at
its initial vertex. -/
def finiteProxyPath (p : Gamma.DPath) : Gamma.DPath :=
  match p with
  | .inl q => .inl q
  | .inr r => Gamma.trivialPath r.initial

@[simp] theorem finiteProxyPath_finite
    (p : FinitePath Gamma.graph) :
    finiteProxyPath (Gamma := Gamma) (.inl p) = .inl p := rfl

@[simp] theorem finiteProxyPath_ray
    (r : Ray Gamma.graph) :
    finiteProxyPath (Gamma := Gamma) (.inr r) =
      Gamma.trivialPath r.initial := rfl

/-- The image of a reference family under `finiteProxyPath`. -/
def finiteProxyReference (Y : Set Gamma.DPath) : Set Gamma.DPath :=
  finiteProxyPath '' Y

@[simp] theorem mem_finiteProxyReference {Y : Set Gamma.DPath}
    {q : Gamma.DPath} :
    q ∈ finiteProxyReference Y ↔
      ∃ p ∈ Y, finiteProxyPath p = q := by
  simp [finiteProxyReference]

theorem finiteProxyPath_support_subset (p : Gamma.DPath) :
    (finiteProxyPath p).support ⊆ p.support := by
  rcases p with p | r
  · exact Set.Subset.rfl
  · rw [finiteProxyPath_ray, Gamma.support_trivialPath]
    exact Set.singleton_subset_iff.mpr r.initial_mem_support

theorem finiteProxyPath_edgeSet_subset (p : Gamma.DPath) :
    (finiteProxyPath p).edgeSet ⊆ p.edgeSet := by
  rcases p with p | r
  · exact Set.Subset.rfl
  · change (FinitePath.trivial Gamma.graph r.initial).edgeSet ⊆ r.edgeSet
    simp [FinitePath.edgeSet]

@[simp] theorem finiteProxyPath_initial (p : Gamma.DPath) :
    (finiteProxyPath p).initial = p.initial := by
  rcases p with p | r
  · rfl
  · change r.initial = r.initial
    rfl

theorem finiteProxyReference_hasFiniteCharacter (Y : Set Gamma.DPath) :
    Gamma.HasFiniteCharacter (finiteProxyReference Y) := by
  rintro q ⟨p, _hpY, rfl⟩
  rcases p with p | r
  · exact ⟨p, rfl⟩
  · exact ⟨FinitePath.trivial Gamma.graph r.initial, rfl⟩

theorem finiteProxyReference_isWarp {Y : Set Gamma.DPath}
    (hY : Gamma.IsWarp Y) :
    Gamma.IsWarp (finiteProxyReference Y) := by
  rintro _ ⟨p, hpY, rfl⟩ _ ⟨q, hqY, rfl⟩ hpq
  have hpqOriginal : p ≠ q := by
    intro h
    subst q
    exact hpq rfl
  exact Disjoint.mono (finiteProxyPath_support_subset p)
    (finiteProxyPath_support_subset q) (hY hpY hqY hpqOriginal)

theorem initialSet_finiteProxyReference (Y : Set Gamma.DPath) :
    Gamma.initialSet (finiteProxyReference Y) = Gamma.initialSet Y := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, ⟨p, hpY, rfl⟩, hqx⟩
    exact ⟨p, hpY, (finiteProxyPath_initial p).symm.trans hqx⟩
  · rintro x ⟨p, hpY, hpx⟩
    exact ⟨finiteProxyPath p, ⟨p, hpY, rfl⟩,
      (finiteProxyPath_initial p).trans hpx⟩

theorem vertexSet_finiteProxyReference_subset (Y : Set Gamma.DPath) :
    Gamma.vertexSet (finiteProxyReference Y) ⊆ Gamma.vertexSet Y := by
  rintro x ⟨q, ⟨p, hpY, rfl⟩, hxq⟩
  exact ⟨p, hpY, finiteProxyPath_support_subset p hxq⟩

theorem familyEdges_finiteProxyReference_subset (Y : Set Gamma.DPath) :
    familyEdges (finiteProxyReference Y) ⊆ familyEdges Y := by
  intro e he
  simp only [familyEdges, Set.mem_iUnion] at he ⊢
  obtain ⟨q, ⟨p, hpY, rfl⟩, heq⟩ := he
  exact ⟨p, hpY, finiteProxyPath_edgeSet_subset p heq⟩

/-- A path having a finite terminal is itself finite and is therefore
retained unchanged by the proxy. -/
theorem terminalFrontier_subset_finiteProxyReference
    (Y : Set Gamma.DPath) :
    Gamma.terminalFrontier Y ⊆
      Gamma.terminalFrontier (finiteProxyReference Y) := by
  rintro x ⟨p, hpY, hpx⟩
  rcases p with p | r
  · exact ⟨.inl p, ⟨.inl p, hpY, rfl⟩, hpx⟩
  · simp [DWeb.terminal?, Path.terminal?] at hpx

/-- Boundary alignment survives ray-to-initial-singleton replacement. -/
theorem BoundaryAligned.finiteProxyReference
    {Z Y : Set Gamma.DPath} (h : BoundaryAligned Z Y) :
    BoundaryAligned Z (finiteProxyReference Y) := by
  constructor
  · intro x hx
    rw [initialSet_finiteProxyReference]
    apply h.1
    exact ⟨hx.1, vertexSet_finiteProxyReference_subset Y hx.2⟩
  · intro x hx
    apply terminalFrontier_subset_finiteProxyReference Y
    apply h.2
    exact ⟨hx.1, vertexSet_finiteProxyReference_subset Y hx.2⟩

/-- A terminal of the first family which is outside the proxy carrier is
already outside the whole reference carrier. -/
theorem terminalFrontier_sdiff_finiteProxyReference_subset
    {Z Y : Set Gamma.DPath} (h : BoundaryAligned Z Y) :
    Gamma.terminalFrontier Z \
        Gamma.vertexSet (finiteProxyReference Y) ⊆
      Gamma.terminalFrontier Z \ Gamma.vertexSet Y := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxY
  have hxTerminalY : x ∈ Gamma.terminalFrontier Y := h.2 ⟨hx.1, hxY⟩
  obtain ⟨p, hpProxy, hpTerm⟩ :=
    terminalFrontier_subset_finiteProxyReference Y hxTerminalY
  exact hx.2 ⟨p, hpProxy, Gamma.terminal_mem_support hpTerm⟩

#print axioms finiteProxyReference_isWarp
#print axioms BoundaryAligned.finiteProxyReference
#print axioms terminalFrontier_sdiff_finiteProxyReference_subset

end LinkageBlueprint
end Blueprint
end Erdos599
