/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingForwardOrbit
import ErdosProblems.Erdos599.HalfwayInfiniteInputCoordinateInterval

/-!
# Projection of an internal infinite two-warp matching prefix

`InfinitePortPrefix` is the genuine infinite outcome of the forward orbit
started at an internal contact.  It has no unmatched-root or ambient-source
hypothesis.  This file performs identity contraction, chronological loop
erasure, and maximal-run compression directly on that prefix.

The output retains literal forward-`W` and backward-`Y` edge provenance,
the raw projected occurrence of every compiled vertex, and the no-return
property supplied by the orbit cut.  It deliberately does not assert full
reference-vertex contact coverage or switching safeness.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath
open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

namespace InfinitePortPrefix

variable {W Y : Set Gamma.DPath} {root : V}

/-- A simple port prefix cannot have two consecutive projected identity
steps. -/
theorem project_ne_or_next (P : InfinitePortPrefix W Y root) (n : Nat) :
    P.projectedVertex n ≠ P.projectedVertex (n + 1) ∨
      P.projectedVertex (n + 1) ≠ P.projectedVertex (n + 2) := by
  by_contra h
  push Not at h
  have hport := eq_of_two_project_stutters (P.steps n) (P.steps (n + 1))
    h.1 (by
      change projectPort (P.port (n + 1)) = projectPort (P.port (n + 2))
      exact h.2)
  exact (by omega : n ≠ n + 2) (P.injective hport)

/-- Raw indices of the literal matching steps after identity contraction. -/
noncomputable def actualIndex (P : InfinitePortPrefix W Y root) : Nat → Nat
  | 0 => 0
  | n + 1 =>
      let i := P.actualIndex n
      if P.projectedVertex (i + 1) ≠ P.projectedVertex (i + 2) then i + 1
      else i + 2

@[simp] theorem actualIndex_zero (P : InfinitePortPrefix W Y root) :
    P.actualIndex 0 = 0 := rfl

theorem actualIndex_succ (P : InfinitePortPrefix W Y root) (n : Nat) :
    P.actualIndex (n + 1) =
      if P.projectedVertex (P.actualIndex n + 1) ≠
          P.projectedVertex (P.actualIndex n + 2) then
        P.actualIndex n + 1 else P.actualIndex n + 2 := rfl

theorem actualIndex_lt_succ (P : InfinitePortPrefix W Y root) (n : Nat) :
    P.actualIndex n < P.actualIndex (n + 1) := by
  rw [P.actualIndex_succ]
  split <;> omega

theorem actualIndex_strictMono (P : InfinitePortPrefix W Y root) :
    StrictMono P.actualIndex :=
  strictMono_nat_of_lt_succ P.actualIndex_lt_succ

theorem actualIndex_is_actual (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat) :
    P.projectedVertex (P.actualIndex n) ≠
      P.projectedVertex (P.actualIndex n + 1) := by
  induction n with
  | zero => simpa using hfirst
  | succ n ih =>
      rw [P.actualIndex_succ]
      split_ifs with hnext
      · exact hnext
      · exact (P.project_ne_or_next (P.actualIndex n + 1)).resolve_left hnext

theorem actualIndex_join (P : InfinitePortPrefix W Y root) (n : Nat) :
    P.projectedVertex (P.actualIndex n + 1) =
      P.projectedVertex (P.actualIndex (n + 1)) := by
  rw [P.actualIndex_succ]
  split_ifs with hnext
  · rfl
  · exact Classical.not_not.mp hnext

/-- The identity-contracted raw vertex stream. -/
noncomputable def contractedVertex (P : InfinitePortPrefix W Y root) :
    Nat → V :=
  fun n ↦ P.projectedVertex (P.actualIndex n)

@[simp] theorem contractedVertex_zero (P : InfinitePortPrefix W Y root) :
    P.contractedVertex 0 = root := by
  simp [contractedVertex]

noncomputable def contractedColour (P : InfinitePortPrefix W Y root)
    (n : Nat) : Direction :=
  match P.port (P.actualIndex n) with
  | .inl _ => .forward
  | .inr _ => .backward

/-- Every contracted edge is still one literal matching step, including the
opposite-family exclusion on its forward orientation. -/
theorem contracted_edge (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat) :
    (P.contractedColour n = .forward ∧
      (P.contractedVertex n, P.contractedVertex (n + 1)) ∈ familyEdges W ∧
      (P.contractedVertex n, P.contractedVertex (n + 1)) ∉ familyEdges Y) ∨
    (P.contractedColour n = .backward ∧
      (P.contractedVertex (n + 1), P.contractedVertex n) ∈ familyEdges Y ∧
      (P.contractedVertex (n + 1), P.contractedVertex n) ∉ familyEdges W) := by
  have hstep := P.steps (P.actualIndex n)
  have hactual := P.actualIndex_is_actual hfirst n
  rcases step_of_project_ne hstep hactual with
    ⟨x, y, hleft, hright, hW, hY⟩ | ⟨x, y, hleft, hright, hY, hW⟩
  · left
    have hjoin := P.actualIndex_join n
    have hcur : P.projectedVertex (P.actualIndex n) = x := by
      simp [projectedVertex, hleft]
    refine ⟨?_, ?_, ?_⟩
    · simp [contractedColour, hleft]
    · simp only [contractedVertex]
      rw [hcur, ← hjoin]
      simpa [projectedVertex, hright] using hW
    · simp only [contractedVertex]
      rw [hcur, ← hjoin]
      simpa [projectedVertex, hright] using hY
  · right
    have hjoin := P.actualIndex_join n
    have hcur : P.projectedVertex (P.actualIndex n) = y := by
      simp [projectedVertex, hleft]
    refine ⟨?_, ?_, ?_⟩
    · simp [contractedColour, hleft]
    · simp only [contractedVertex]
      rw [hcur, ← hjoin]
      simpa [projectedVertex, hright] using hY
    · simp only [contractedVertex]
      rw [hcur, ← hjoin]
      simpa [projectedVertex, hright] using hW

theorem contracted_forward_mem (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat)
    (hdir : P.contractedColour n = .forward) :
    (P.contractedVertex n, P.contractedVertex (n + 1)) ∈ familyEdges W := by
  rcases P.contracted_edge hfirst n with h | h
  · exact h.2.1
  · exact False.elim (by simpa [h.1] using hdir)

theorem contracted_forward_not_mem_reference
    (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat)
    (hdir : P.contractedColour n = .forward) :
    (P.contractedVertex n, P.contractedVertex (n + 1)) ∉ familyEdges Y := by
  rcases P.contracted_edge hfirst n with h | h
  · exact h.2.2
  · exact False.elim (by simpa [h.1] using hdir)

theorem contracted_backward_mem (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat)
    (hdir : P.contractedColour n = .backward) :
    (P.contractedVertex (n + 1), P.contractedVertex n) ∈ familyEdges Y := by
  rcases P.contracted_edge hfirst n with h | h
  · exact False.elim (by simpa [h.1] using hdir)
  · exact h.2.1

/-- The projected stream is at most two-to-one, since the raw port stream is
injective and a vertex has only a sending and a receiving copy. -/
theorem contracted_occurrenceFiber_finite (P : InfinitePortPrefix W Y root)
    (n : Nat) :
    (occurrenceFiber P.contractedVertex n).Finite := by
  let g : Nat → Port V := fun k ↦ P.port (P.actualIndex k)
  have hg : Function.Injective g :=
    P.injective.comp P.actualIndex_strictMono.injective
  have hfinite : ({.inl (P.contractedVertex n),
      .inr (P.contractedVertex n)} : Set (Port V)).Finite :=
    (Set.finite_singleton (Sum.inr (P.contractedVertex n))).insert _
  have hpre := hfinite.preimage hg.injOn
  apply hpre.subset
  intro k hk
  change P.contractedVertex k = P.contractedVertex n at hk
  change g k ∈ ({.inl (P.contractedVertex n),
    .inr (P.contractedVertex n)} : Set (Port V))
  rcases hport : g k with x | x <;> simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, false_or, or_false]
  · simpa [contractedVertex, projectedVertex, g, hport] using hk
  · simpa [contractedVertex, projectedVertex, g, hport] using hk

/-- Chronological loop erasure of the contracted stream, with literal
matching colour retained on each raw edge. -/
noncomputable def compressorInput (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) :
    RunCompressor.InfiniteInput Gamma.graph := by
  let hf := P.contracted_occurrenceFiber_finite
  exact {
    vertex := fun n ↦ P.contractedVertex
      (loopErasedIndex P.contractedVertex hf n)
    vertex_injective := injective_loopErasedVertex P.contractedVertex hf
    colour := fun n ↦ P.contractedColour
      (loopErasedIndex P.contractedVertex hf n)
    forward_adj := by
      intro n hn
      rw [← loopErasedIndex_join P.contractedVertex hf n]
      exact familyEdges_subset_adj W
        (P.contracted_forward_mem hfirst _ hn)
    backward_adj := by
      intro n hn
      rw [← loopErasedIndex_join P.contractedVertex hf n]
      exact familyEdges_subset_adj Y
        (P.contracted_backward_mem hfirst _ hn) }

@[simp] theorem compressorInput_vertex (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat) :
    (P.compressorInput hfirst).vertex n =
      P.contractedVertex (loopErasedIndex P.contractedVertex
        P.contracted_occurrenceFiber_finite n) := rfl

@[simp] theorem compressorInput_colour (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat) :
    (P.compressorInput hfirst).colour n =
      P.contractedColour (loopErasedIndex P.contractedVertex
        P.contracted_occurrenceFiber_finite n) := rfl

/-- Every compressor coordinate exposes its exact raw port occurrence. -/
theorem compressorInput_vertex_rawOccurrence
    (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat) :
    (P.compressorInput hfirst).vertex n =
      P.projectedVertex
        (P.actualIndex (loopErasedIndex P.contractedVertex
          P.contracted_occurrenceFiber_finite n)) := rfl

theorem compressorInput_forward_mem (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat)
    (hdir : (P.compressorInput hfirst).colour n = .forward) :
    ((P.compressorInput hfirst).vertex n,
      (P.compressorInput hfirst).vertex (n + 1)) ∈ familyEdges W := by
  let hf := P.contracted_occurrenceFiber_finite
  change (P.contractedVertex (loopErasedIndex P.contractedVertex hf n),
      P.contractedVertex (loopErasedIndex P.contractedVertex hf (n + 1))) ∈
    familyEdges W
  rw [← loopErasedIndex_join P.contractedVertex hf n]
  exact P.contracted_forward_mem hfirst _ hdir

theorem compressorInput_forward_not_mem_reference
    (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat)
    (hdir : (P.compressorInput hfirst).colour n = .forward) :
    ((P.compressorInput hfirst).vertex n,
      (P.compressorInput hfirst).vertex (n + 1)) ∉ familyEdges Y := by
  let hf := P.contracted_occurrenceFiber_finite
  change (P.contractedVertex (loopErasedIndex P.contractedVertex hf n),
      P.contractedVertex (loopErasedIndex P.contractedVertex hf (n + 1))) ∉
    familyEdges Y
  rw [← loopErasedIndex_join P.contractedVertex hf n]
  exact P.contracted_forward_not_mem_reference hfirst _ hdir

theorem compressorInput_backward_mem (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1) (n : Nat)
    (hdir : (P.compressorInput hfirst).colour n = .backward) :
    ((P.compressorInput hfirst).vertex (n + 1),
      (P.compressorInput hfirst).vertex n) ∈ familyEdges Y := by
  let hf := P.contracted_occurrenceFiber_finite
  change (P.contractedVertex (loopErasedIndex P.contractedVertex hf (n + 1)),
      P.contractedVertex (loopErasedIndex P.contractedVertex hf n)) ∈
    familyEdges Y
  rw [← loopErasedIndex_join P.contractedVertex hf n]
  exact P.contracted_backward_mem hfirst _ hdir

/-- Finite-character forward paths and the absence of reverse rays in a
warp force infinitely many colour changes. -/
theorem compressorInput_changes (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ∀ n, ∃ m, n < m ∧
      (P.compressorInput hfirst).colour m ≠
        (P.compressorInput hfirst).colour n := by
  intro n
  by_contra hno
  push Not at hno
  let S := P.compressorInput hfirst
  have htail : ∀ k, S.colour (n + k) = S.colour n := by
    intro k
    cases k with
    | zero => simp
    | succ k => exact hno _ (by omega)
  cases hn : S.colour n with
  | forward =>
      apply familyEdges_not_containsDirectedRay_of_finite hW hWfinite
      let R : DirectedRay V := {
        vertex := fun k ↦ S.vertex (n + k)
        injective := by
          intro i j hij
          exact Nat.add_left_cancel (S.vertex_injective hij) }
      refine ⟨R, ?_⟩
      rintro e ⟨k, rfl⟩
      have hk : S.colour (n + k) = .forward := (htail k).trans hn
      simpa [R, S, Nat.add_assoc] using
        P.compressorInput_forward_mem hfirst (n + k) hk
  | backward =>
      apply familyEdges_not_containsReverseDirectedRay hY
      let R : DirectedRay V := {
        vertex := fun k ↦ S.vertex (n + k)
        injective := by
          intro i j hij
          exact Nat.add_left_cancel (S.vertex_injective hij) }
      refine ⟨R, ?_⟩
      intro k
      have hk : S.colour (n + k) = .backward := (htail k).trans hn
      simpa [R, S, Nat.add_assoc] using
        P.compressorInput_backward_mem hfirst (n + k) hk

noncomputable def runWalk (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (P.compressorInput hfirst).colour m ≠
        (P.compressorInput hfirst).colour n) :
    InfiniteRunWalk Gamma.graph :=
  (P.compressorInput hfirst).toInfiniteRunWalk hchange

noncomputable def compiledRunWalk (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) : InfiniteRunWalk Gamma.graph :=
  P.runWalk hfirst (P.compressorInput_changes hfirst hW hWfinite hY)

theorem runWalk_forward_edge_mem (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (P.compressorInput hfirst).colour m ≠
        (P.compressorInput hfirst).colour n)
    (i : Nat) (hdir : ((P.runWalk hfirst hchange).run i).link.direction =
      .forward) :
    ((P.runWalk hfirst hchange).run i).link.path.edgeSet ⊆ familyEdges W := by
  intro e he
  let S := P.compressorInput hfirst
  change (S.projectedRun hchange i).link.direction = .forward at hdir
  have hprov := S.projectedRun_edge_provenance hchange i he
  rcases hprov with ⟨_hforward, k, hklo, hkhi, rfl⟩ |
      ⟨hbackward, k, hklo, hkhi, rfl⟩
  · apply P.compressorInput_forward_mem hfirst k
    have hcolour := RunCompressor.colour_eq_on_run S.colour hchange hklo hkhi
    exact hcolour.trans (by
      rw [← S.projectedRun_direction hchange i]
      exact hdir)
  · rw [hdir] at hbackward
    contradiction

theorem runWalk_forward_edge_not_mem_reference
    (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (P.compressorInput hfirst).colour m ≠
        (P.compressorInput hfirst).colour n)
    (i : Nat) (hdir : ((P.runWalk hfirst hchange).run i).link.direction =
      .forward) :
    Disjoint ((P.runWalk hfirst hchange).run i).link.path.edgeSet
      (familyEdges Y) := by
  rw [Set.disjoint_left]
  intro e he hYedge
  let S := P.compressorInput hfirst
  change (S.projectedRun hchange i).link.direction = .forward at hdir
  have hprov := S.projectedRun_edge_provenance hchange i he
  rcases hprov with ⟨_hforward, k, hklo, hkhi, rfl⟩ |
      ⟨hbackward, k, hklo, hkhi, rfl⟩
  · apply P.compressorInput_forward_not_mem_reference hfirst k _ hYedge
    have hcolour := RunCompressor.colour_eq_on_run S.colour hchange hklo hkhi
    exact hcolour.trans (by
      rw [← S.projectedRun_direction hchange i]
      exact hdir)
  · rw [hdir] at hbackward
    contradiction

theorem runWalk_backward_edge_mem (P : InfinitePortPrefix W Y root)
    (hfirst : P.projectedVertex 0 ≠ P.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (P.compressorInput hfirst).colour m ≠
        (P.compressorInput hfirst).colour n)
    (i : Nat) (hdir : ((P.runWalk hfirst hchange).run i).link.direction =
      .backward) :
    ((P.runWalk hfirst hchange).run i).link.path.edgeSet ⊆ familyEdges Y := by
  intro e he
  let S := P.compressorInput hfirst
  change (S.projectedRun hchange i).link.direction = .backward at hdir
  have hprov := S.projectedRun_edge_provenance hchange i he
  rcases hprov with ⟨hforward, k, hklo, hkhi, rfl⟩ |
      ⟨_hbackward, k, hklo, hkhi, rfl⟩
  · rw [hdir] at hforward
    contradiction
  · apply P.compressorInput_backward_mem hfirst k
    have hcolour := RunCompressor.colour_eq_on_run S.colour hchange hklo hkhi
    exact hcolour.trans (by
      rw [← S.projectedRun_direction hchange i]
      exact hdir)

/-- The no-return orbit certificate makes the first port step literal. -/
theorem firstLiteral_of_positive_outside (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X) :
    P.projectedVertex 0 ≠ P.projectedVertex 1 := by
  intro h
  apply houtside 1 (by omega)
  rw [← h, P.projectedVertex_zero]
  exact hrootX

theorem projectedVertex_eq_root_index_zero_of_positive_outside
    (P : InfinitePortPrefix W Y root) {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    {n : Nat} (hn : P.projectedVertex n = root) : n = 0 := by
  by_contra hnzero
  exact houtside n (Nat.pos_of_ne_zero hnzero) (hn.symm ▸ hrootX)

theorem contractedVertex_eq_root_index_zero_of_positive_outside
    (P : InfinitePortPrefix W Y root) {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    {n : Nat} (hn : P.contractedVertex n = root) : n = 0 := by
  have hraw : P.actualIndex n = 0 :=
    P.projectedVertex_eq_root_index_zero_of_positive_outside
      hrootX houtside hn
  exact P.actualIndex_strictMono.injective
    (hraw.trans P.actualIndex_zero.symm)

theorem compressorInput_vertex_zero_of_positive_outside
    (P : InfinitePortPrefix W Y root) {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X) :
    (P.compressorInput (P.firstLiteral_of_positive_outside hrootX houtside)).vertex 0 =
      root := by
  let hf := P.contracted_occurrenceFiber_finite
  change P.contractedVertex
      (loopErasedIndex P.contractedVertex hf 0) = root
  rw [loopErasedIndex_zero_eq_zero_of_root_unique
    P.contractedVertex hf (fun m hm ↦
      P.contractedVertex_eq_root_index_zero_of_positive_outside
        hrootX houtside (hm.trans P.contractedVertex_zero))]
  exact P.contractedVertex_zero

theorem compressorInput_vertex_positive_outside
    (P : InfinitePortPrefix W Y root) {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    {n : Nat} (hn : 0 < n) :
    (P.compressorInput (P.firstLiteral_of_positive_outside hrootX houtside)).vertex n
      ∉ X := by
  let hf := P.contracted_occurrenceFiber_finite
  let q := loopErasedIndex P.contractedVertex hf n
  have hqpos : 0 < q := by
    have hlt := loopErasedIndex_strictMono P.contractedVertex hf hn
    exact (Nat.zero_le _).trans_lt hlt
  have hrawpos : 0 < P.actualIndex q := by
    simpa using P.actualIndex_strictMono hqpos
  change P.projectedVertex (P.actualIndex q) ∉ X
  exact houtside _ hrawpos

/-- Literal infinite alternating path compiled from the no-return prefix. -/
noncomputable def altPath (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) : AltPath Gamma.graph :=
  let hfirst := P.firstLiteral_of_positive_outside hrootX houtside
  .infinite (P.compiledRunWalk hfirst hW hWfinite hY).toInfiniteTrace

@[simp] theorem altPath_initial (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    (P.altPath hrootX houtside hW hWfinite hY).initial = root := by
  let hfirst := P.firstLiteral_of_positive_outside hrootX houtside
  change (P.compiledRunWalk hfirst hW hWfinite hY).toInfiniteTrace.initial = root
  rw [InfiniteRunWalk.toInfiniteTrace_initial]
  exact P.compressorInput_vertex_zero_of_positive_outside hrootX houtside

/-- Each compiled vertex is an actual projected occurrence of the original
port prefix. -/
theorem altPath_vertex_rawOccurrence (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) {x : V}
    (hx : x ∈ (P.altPath hrootX houtside hW hWfinite hY).vertexSet) :
    ∃ n, x = P.projectedVertex n := by
  let hfirst := P.firstLiteral_of_positive_outside hrootX houtside
  let hchange := P.compressorInput_changes hfirst hW hWfinite hY
  change x ∈ ((P.compressorInput hfirst).toInfiniteRunWalk hchange).toInfiniteTrace.vertexSet at hx
  rw [(P.compressorInput hfirst).toInfiniteTrace_vertexSet hchange] at hx
  obtain ⟨n, rfl⟩ := hx
  exact ⟨P.actualIndex (loopErasedIndex P.contractedVertex
    P.contracted_occurrenceFiber_finite n), rfl⟩

theorem altPath_vertexSet_subset_projectedRange
    (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    (P.altPath hrootX houtside hW hWfinite hY).vertexSet ⊆
      Set.range P.projectedVertex := by
  intro x hx
  obtain ⟨n, rfl⟩ :=
    P.altPath_vertex_rawOccurrence hrootX houtside hW hWfinite hY hx
  exact ⟨n, rfl⟩

theorem altPath_vertexSet_subset_of_projectedVertex
    (P : InfinitePortPrefix W Y root)
    {X Z : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (hprojected : ∀ n, P.projectedVertex n ∈ Z) :
    (P.altPath hrootX houtside hW hWfinite hY).vertexSet ⊆ Z := by
  intro x hx
  obtain ⟨n, rfl⟩ :=
    P.altPath_vertex_rawOccurrence hrootX houtside hW hWfinite hY hx
  exact hprojected n

/-- The compiled path has no return to `X`: its only possible `X` vertex is
the literal initial vertex. -/
theorem altPath_inter_X_subset_root (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    (P.altPath hrootX houtside hW hWfinite hY).vertexSet ∩ X ⊆ {root} := by
  rintro x ⟨hxPath, hxX⟩
  obtain ⟨n, rfl⟩ :=
    P.altPath_vertex_rawOccurrence hrootX houtside hW hWfinite hY hxPath
  by_cases hn : n = 0
  · subst n
    simp
  · exact False.elim (houtside n (Nat.pos_of_ne_zero hn) hxX)

theorem altPath_forward_edge_mem (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ∀ l ∈ (P.altPath hrootX houtside hW hWfinite hY).links,
      l.direction = .forward → l.path.edgeSet ⊆ familyEdges W := by
  intro l hl hdir
  let hfirst := P.firstLiteral_of_positive_outside hrootX houtside
  let hchange := P.compressorInput_changes hfirst hW hWfinite hY
  change l ∈ (P.runWalk hfirst hchange).toInfiniteTrace.links at hl
  rw [InfiniteRunWalk.toInfiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact P.runWalk_forward_edge_mem hfirst hchange i hdir

theorem altPath_forward_edge_not_mem_reference
    (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ForwardLinksOff Y (P.altPath hrootX houtside hW hWfinite hY) := by
  intro l hl hdir
  let hfirst := P.firstLiteral_of_positive_outside hrootX houtside
  let hchange := P.compressorInput_changes hfirst hW hWfinite hY
  change l ∈ (P.runWalk hfirst hchange).toInfiniteTrace.links at hl
  rw [InfiniteRunWalk.toInfiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact P.runWalk_forward_edge_not_mem_reference hfirst hchange i hdir

theorem altPath_backward_edge_mem (P : InfinitePortPrefix W Y root)
    {X : Set V} (hrootX : root ∈ X)
    (houtside : ∀ n, 0 < n → P.projectedVertex n ∉ X)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ∀ l ∈ (P.altPath hrootX houtside hW hWfinite hY).links,
      l.direction = .backward → l.path.edgeSet ⊆ familyEdges Y := by
  intro l hl hdir
  let hfirst := P.firstLiteral_of_positive_outside hrootX houtside
  let hchange := P.compressorInput_changes hfirst hW hWfinite hY
  change l ∈ (P.runWalk hfirst hchange).toInfiniteTrace.links at hl
  rw [InfiniteRunWalk.toInfiniteTrace_links] at hl
  rcases hl with ⟨i, rfl⟩
  exact P.runWalk_backward_edge_mem hfirst hchange i hdir

#print axioms firstLiteral_of_positive_outside
#print axioms altPath_initial
#print axioms altPath_vertex_rawOccurrence
#print axioms altPath_vertexSet_subset_projectedRange
#print axioms altPath_inter_X_subset_root
#print axioms altPath_forward_edge_not_mem_reference
#print axioms altPath_backward_edge_mem

end InfinitePortPrefix
end
end TwoWarpMatchingTraversal
end Erdos599
