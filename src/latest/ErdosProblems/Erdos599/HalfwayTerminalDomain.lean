/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayContinuationRepair
import ErdosProblems.Erdos599.GlobalAdvance931

/-!
# The source-faithful domain of the half-way terminal compiler

Aharoni--Berger Assertions 9.30 and 9.34 apply to every terminal of the
real part of a linkage blueprint.  Membership in the current ladder slice
is only the easy identity subcase of Assertion 9.30.  A full blueprint
terminal outside the slice is handled by its popularity and an infinity
hammock; a real terminal which is not a full blueprint terminal is the tail
of an imaginary blueprint edge.

This file records that exhaustive case split and exposes compiler interfaces
with the correct all-real-terminal domain.  The older `Stable934Compiler`
interface, which additionally asks for `u ∈ T`, is retained only as a
compatibility projection.  In particular, no false assertion that non-full
real terminals belong to `T` is introduced.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- The exhaustive source-level domain split for Assertion 9.30.

The last alternative deliberately retains the represented blueprint edge;
the imaginary-edge predicate alone is not enough to form the exact cut
`W^u`. -/
theorem realTerminal_mem_slice_or_infiniteHammock_or_imaginaryEdge
    {W : LinkageBlueprint Gamma Y kappa} {u : V}
    {T Z persistent : Set V}
    (hW : W.IsLinkageBlueprint T Z persistent)
    (hpersistent : persistent ⊆ T)
    (hu : u ∈ W.realPart.terminals) :
    u ∈ T ∨
      (u ∈ W.terminalSet ∧
        HasHammockCard Gamma Y u .infinity (succ kappa)) ∨
      ∃ v, (u, v) ∈ W.edgeSet ∧
        IsImaginaryEdge Gamma Y kappa u v := by
  by_cases huT : u ∈ T
  · exact Or.inl huT
  · right
    rcases real_terminal_is_terminal_or_has_imaginary_edge_mem hu with
      huterm | himaginary
    · exact Or.inl ⟨huterm,
        terminal_outside_slice_has_infinite_hammock
          hW hpersistent huterm huT⟩
    · exact Or.inr himaginary

/-- Assertion 9.30 with its published domain: every real terminal, not only
the real terminals already in the current slice. -/
def AllRealTerminalContinuation930Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        ∃ (cut V' : LinkageBlueprint Gamma Y kappa) (z : V),
          Continuation930 W cut V' u z T B

/-- Assertion 9.34 with its published domain: every real terminal. -/
def AllRealTerminalStable934Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          StableExtensionConclusion W U u T Z persistent B

/-- The source-faithful compiler implies the older scheduled-slice
interface by forgetting its larger domain. -/
theorem AllRealTerminalContinuation930Compiler.toScheduledSlice
    {T Z persistent B : Set V}
    (h : AllRealTerminalContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Continuation930Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B := by
  intro W u hW hpersistent hu _huT
  exact h W u hW hpersistent hu

/-- The source-faithful stable compiler implies the older scheduled-slice
interface by forgetting its larger domain. -/
theorem AllRealTerminalStable934Compiler.toScheduledSlice
    {T Z persistent B : Set V}
    (h : AllRealTerminalStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    Stable934Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B := by
  intro W u hW hpersistent hu _huT
  exact h W u hW hpersistent hu

/-- The honest coupled-replacement construction already handles the full
source domain.  The apparent scheduled-slice premise in the older wrapper
was unused: the proof itself separates the in-slice identity case from the
two hammock cases. -/
theorem allRealTerminalContinuation930Compiler_of_coupledHammockReplacement
    {T Z persistent B : Set V}
    (hkappa : aleph0 ≤ kappa)
    (hterminal : TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary : ImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent) :
    AllRealTerminalContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu
  have hWvertices : #W.vertexSet ≤ kappa :=
    W.mk_vertexSet_le_of_mk_paths_le hkappa hW.card_paths
  rcases real_terminal_is_terminal_or_has_imaginary_edge_mem hu with
      huterm | ⟨v, huv, himag⟩
  · by_cases huT : u ∈ T
    · exact ⟨W, W, u,
        continuation930_of_terminal_mem_slice hu huterm huT⟩
    · have hhammock :
          HasHammockCard Gamma Y u .infinity (succ kappa) :=
        terminal_outside_slice_has_infinite_hammock
          hW hpersistent huterm huT
      obtain ⟨Q, hQsafe, hQinitial, hQinfinite, hQdisjoint⟩ :=
        exists_safe_infinite_hammock_path_avoiding hhammock hWvertices
      obtain ⟨U, z, ⟨hreplacement⟩⟩ :=
        hterminal W u Q hW hpersistent hu huterm huT hQsafe hQinitial
          hQinfinite hQdisjoint
      exact ⟨W, U, z, hreplacement.continuation930⟩
  · obtain ⟨Q, hQsafe, hQinitial, hQend, hQdisjoint⟩ :=
      exists_hammock_path_disjoint_of_mk_le himag hWvertices
    obtain ⟨cut, U, z, hcut, ⟨hreplacement⟩⟩ :=
      himaginary W u v Q hW hpersistent hu huv himag hQsafe hQinitial
        hQend hQdisjoint
    exact ⟨cut, U, z,
      (show Continuation930 W cut U u z T B from
        hreplacement.continuation930)⟩

/-- Source-faithful 9.30 and 9.31 compilers compose to source-faithful
Assertion 9.34, without a slice-membership premise on the scheduled real
terminal. -/
theorem allRealTerminalStable934Compiler_of_930_931
    {T Z persistent B : Set V}
    (h30 : AllRealTerminalContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (h31 : Advance931Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B) :
    AllRealTerminalStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu
  apply exists_assertion934
  · exact h30 W u hW hpersistent hu
  · intro cut V' z hcontinuation
    exact h31 W cut V' u z hW hcontinuation

/-- The complete honest replacement interface supplies the all-terminal
successor consumed by the fair scheduler. -/
theorem allRealTerminalStable934Compiler_of_coupledHammockReplacement
    {T Z persistent B : Set V}
    (hkappa : aleph0 ≤ kappa)
    (hterminal : TerminalOutsideHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (himaginary : ImaginarySuccessorHammockReplacementCompiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent)
    (hadvance : Advance931Compiler
      (Γ := Gamma) (Y := Y) (κ := kappa) T Z persistent B) :
    AllRealTerminalStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B :=
  allRealTerminalStable934Compiler_of_930_931
    (allRealTerminalContinuation930Compiler_of_coupledHammockReplacement
      hkappa hterminal himaginary)
    hadvance

/-! ## Predecessor-preserving scheduler variants -/

/-- All-terminal 9.30 interface carrying the real-predecessor invariant
needed by the relation-limit construction. -/
def AllRealTerminalPredecessorPreservingContinuation930Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        ∃ (cut V' : LinkageBlueprint Gamma Y kappa) (z : V),
          Continuation930 W cut V' u z T B ∧
            W.NoNewRealPredecessorsTo V'

/-- All-terminal version of the real-predecessor-preserving successor
interface used by relation-limit scheduler chains. -/
def AllRealTerminalPredecessorPreservingStable934Compiler
    (T Z persistent B : Set V) : Prop :=
  ∀ (W : LinkageBlueprint Gamma Y kappa) (u : V),
    W.IsLinkageBlueprint T Z persistent → persistent ⊆ T →
      u ∈ W.realPart.terminals →
        ∃ U : LinkageBlueprint Gamma Y kappa,
          PredecessorPreservingStable934 W U u T Z persistent B

/-- The all-terminal predecessor-preserving 9.30 and 9.31 interfaces
compose without adding any slice-membership hypothesis. -/
theorem allRealTerminalPredecessorPreservingStable934Compiler_of_930_931
    {T Z persistent B : Set V}
    (h30 : AllRealTerminalPredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B)
    (h31 : PredecessorPreservingAdvance931Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    AllRealTerminalPredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu
  obtain ⟨cut, V', z, hcontinuation, hnoNew30⟩ :=
    h30 W u hW hpersistent hu
  obtain ⟨U, hadvance⟩ := h31 W cut V' u z hW hcontinuation
  refine ⟨U, assertion934_of_930_931 hcontinuation hadvance.advance, ?_⟩
  exact hnoNew30.trans hadvance.no_new_real_predecessors
    hcontinuation.real_extends_to_endpoint.1.1

/-- Compatibility projection for an existing scheduled-slice 9.30
consumer.  The converse is intentionally absent. -/
theorem AllRealTerminalPredecessorPreservingContinuation930Compiler.toScheduledSlice
    {T Z persistent B : Set V}
    (h : AllRealTerminalPredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingContinuation930Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu _huT
  exact h W u hW hpersistent hu

/-- Forget predecessor information but retain the all-terminal domain. -/
theorem AllRealTerminalPredecessorPreservingStable934Compiler.toStable
    {T Z persistent B : Set V}
    (h : AllRealTerminalPredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    AllRealTerminalStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu
  obtain ⟨U, hU⟩ := h W u hW hpersistent hu
  exact ⟨U, hU.conclusion⟩

/-- Compatibility projection to the older scheduled-slice predecessor
compiler. -/
theorem AllRealTerminalPredecessorPreservingStable934Compiler.toScheduledSlice
    {T Z persistent B : Set V}
    (h : AllRealTerminalPredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B) :
    PredecessorPreservingStable934Compiler
      (Gamma := Gamma) (Y := Y) (kappa := kappa) T Z persistent B := by
  intro W u hW hpersistent hu _huT
  exact h W u hW hpersistent hu

end LinkageBlueprint
end Blueprint
end Erdos599
