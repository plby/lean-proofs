/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpMatchingTraversal
import ErdosProblems.Erdos599.FiniteChronologicalErasure
import ErdosProblems.Erdos599.RawAlternatingDichotomy

/-!
# Projecting the two-matching traversal

The bipartite matching traversal contains genuine warp edges and identity
matching edges.  The latter change from the sending copy of a vertex to its
receiving copy (or conversely), but do not contribute an edge to the
alternating path.  This file contracts those identity steps before the usual
chronological loop erasure and maximal-run compression.

The construction is deliberately tied to `TwoWarpMatchingTraversal`: every
retained raw edge still comes with its literal forward-`W` or backward-`Y`
membership.  It is not a projection of the older lazy macro orbit.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath
open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

noncomputable section

local instance : DecidableEq V := Classical.decEq V

/-- Forget whether a vertex is being used as a sending or receiving copy. -/
def projectPort : Port V -> V
  | .inl x => x
  | .inr x => x

@[simp] theorem projectPort_inl (x : V) : projectPort (.inl x) = x := rfl
@[simp] theorem projectPort_inr (x : V) : projectPort (.inr x) = x := rfl

/-- A non-stuttering matching step is a literal edge of exactly one of the
two path families, with its traversal direction recorded. -/
theorem step_of_project_ne {W Y : Set Gamma.DPath} {a b : Port V}
    (hstep : Step W Y a b) (hne : projectPort a ≠ projectPort b) :
    (∃ x y, a = .inl x ∧ b = .inr y ∧
      (x, y) ∈ familyEdges W ∧ (x, y) ∉ familyEdges Y) ∨
      ∃ x y, a = .inr y ∧ b = .inl x ∧
        (x, y) ∈ familyEdges Y ∧ (x, y) ∉ familyEdges W := by
  rcases step_cases hstep with
    ⟨x, y, rfl, rfl, hxy⟩ | ⟨x, y, rfl, rfl, hxy⟩
  · rcases hxy.1 with hW | hW
    · exact Or.inl ⟨x, y, rfl, rfl, hW,
        forward_actual_not_reference hxy hW⟩
    · exact False.elim (hne hW.1)
  · rcases hxy.1 with hY | hY
    · exact Or.inr ⟨x, y, rfl, rfl, hY,
        forward_actual_not_reference hxy hY⟩
    · exact False.elim (hne hY.1.symm)

/-- Two consecutive identity steps would revisit the same bipartite port. -/
theorem eq_of_two_project_stutters {W Y : Set Gamma.DPath}
    {a b c : Port V} (hab : Step W Y a b) (hbc : Step W Y b c)
    (habEq : projectPort a = projectPort b)
    (hbcEq : projectPort b = projectPort c) : a = c := by
  rcases a with x | x <;> rcases b with y | y <;> rcases c with z | z <;>
    simp only [Step] at hab hbc <;>
    simp only [projectPort] at habEq hbcEq <;>
    try contradiction
  · exact congrArg Sum.inl (habEq.trans hbcEq)
  · exact congrArg Sum.inr (habEq.trans hbcEq)

/-- A finite-character warp contains no forward directed ray in its union of
edges.  The warp property forces a hypothetical ray into one member. -/
theorem familyEdges_not_containsDirectedRay_of_finite
    {W : Set Gamma.DPath} (hW : Gamma.IsWarp W)
    (hfinite : Gamma.HasFiniteCharacter W) :
    ¬ ContainsDirectedRay (familyEdges W) := by
  rintro ⟨R, hR⟩
  obtain ⟨p0, hp0W, hp0edge⟩ :
      ∃ p0 ∈ W, (R.vertex 0, R.vertex 1) ∈ p0.edgeSet := by
    have hm := hR ⟨0, rfl⟩
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p0, hp0W, hp0edge⟩
    exact ⟨p0, hp0W, by simpa using hp0edge⟩
  have hedge : ∀ n, (R.vertex n, R.vertex (n + 1)) ∈ p0.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hp0edge
    | succ n ih =>
        have hm := hR ⟨n + 1, rfl⟩
        simp only [familyEdges, Set.mem_iUnion] at hm
        rcases hm with ⟨p, hpW, hpedge⟩
        have hp0shared : R.vertex (n + 1) ∈ p0.support :=
          (p0.edgeSet_subset_support_prod ih).2
        have hpshared : R.vertex (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).1
        have hp : p = p0 :=
          DWeb.IsWarp.eq_of_mem_support hW hpW hp0W hpshared hp0shared
        exact hp ▸ hpedge
  rcases hfinite hp0W with ⟨p, rfl⟩
  have hsupport : ∀ n, R.vertex n ∈ p.support := by
    intro n
    cases n with
    | zero => exact (p.edgeSet_subset_support_prod (hedge 0)).1
    | succ n => exact (p.edgeSet_subset_support_prod (hedge n)).2
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hsupport)

private theorem finitePath_not_containsReverseDirectedRay
    {D : Digraph V} (p : FinitePath D) :
    ¬ ContainsReverseDirectedRay p.edgeSet := by
  rintro ⟨R, hR⟩
  have hall : ∀ n, R.vertex n ∈ p.support := by
    intro n
    cases n with
    | zero => exact (p.edgeSet_subset_support_prod (hR 0)).2
    | succ n => exact (p.edgeSet_subset_support_prod (hR n)).1
  exact p.support_finite.not_infinite
    (Set.infinite_of_injective_forall_mem R.injective hall)

private theorem ray_not_containsReverseDirectedRay
    {D : Digraph V} (r : Ray D) :
    ¬ ContainsReverseDirectedRay r.edgeSet := by
  rintro ⟨R, hR⟩
  let f : Nat -> Nat := fun n => Classical.choose (hR n)
  have hf (n : Nat) :
      (R.vertex (n + 1), R.vertex n) = (r (f n), r (f n + 1)) :=
    Classical.choose_spec (hR n)
  have hstep (n : Nat) : f (n + 1) + 1 = f n := by
    apply r.injective
    exact (congrArg Prod.snd (hf (n + 1))).symm.trans
      (congrArg Prod.fst (hf n))
  have hsum : ∀ n, f n + n = f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          f (n + 1) + (n + 1) = (f (n + 1) + 1) + n := by omega
          _ = f n + n := by rw [hstep n]
          _ = f 0 := ih
  have := hsum (f 0 + 1)
  omega

private theorem path_not_containsReverseDirectedRay
    {D : Digraph V} (p : Path D) :
    ¬ ContainsReverseDirectedRay p.edgeSet := by
  rcases p with p | r
  · exact finitePath_not_containsReverseDirectedRay p
  · exact ray_not_containsReverseDirectedRay r

/-- A warp contains no ray traversed backwards, even when its members may be
forward rays.  Again, warp-disjointness puts the entire reverse ray in one
member. -/
theorem familyEdges_not_containsReverseDirectedRay
    {Y : Set Gamma.DPath} (hY : Gamma.IsWarp Y) :
    ¬ ContainsReverseDirectedRay (familyEdges Y) := by
  rintro ⟨R, hR⟩
  obtain ⟨p0, hp0Y, hp0edge⟩ :
      ∃ p0 ∈ Y, (R.vertex 1, R.vertex 0) ∈ p0.edgeSet := by
    have hm := hR 0
    simp only [familyEdges, Set.mem_iUnion] at hm
    rcases hm with ⟨p0, hp0Y, hp0edge⟩
    exact ⟨p0, hp0Y, by simpa using hp0edge⟩
  have hedge : ∀ n, (R.vertex (n + 1), R.vertex n) ∈ p0.edgeSet := by
    intro n
    induction n with
    | zero => simpa using hp0edge
    | succ n ih =>
        obtain ⟨p, hpY, hpedge⟩ : ∃ p ∈ Y,
            (R.vertex (n + 1 + 1), R.vertex (n + 1)) ∈ p.edgeSet := by
          have hm := hR (n + 1)
          simp only [familyEdges, Set.mem_iUnion] at hm
          rcases hm with ⟨p, hpY, hpedge⟩
          exact ⟨p, hpY, hpedge⟩
        have hp0shared : R.vertex (n + 1) ∈ p0.support :=
          (p0.edgeSet_subset_support_prod ih).1
        have hpshared : R.vertex (n + 1) ∈ p.support :=
          (p.edgeSet_subset_support_prod hpedge).2
        have hp : p = p0 :=
          DWeb.IsWarp.eq_of_mem_support hY hpY hp0Y hpshared hp0shared
        exact hp ▸ hpedge
  exact path_not_containsReverseDirectedRay p0 ⟨R, hedge⟩

namespace InfiniteTraversal

variable {W Y : Set Gamma.DPath} {root : V}

/-- The ambient vertex seen at a port of an infinite matching traversal. -/
def projectedVertex (T : InfiniteTraversal W Y root) (n : Nat) : V :=
  projectPort (T.port n)

/-- Contact label retained when identity steps are contracted.  It records
that one of the two copies of `x` lies on an actual reference-coloured step
of the matching component. -/
def ReferenceContact (T : InfiniteTraversal W Y root) (x : V) : Prop :=
  ∃ a : Port V, T.ReferenceCovered a ∧ projectPort a = x

/-- A traversal cannot stutter twice: the second alternative is the next
literal matching edge. -/
theorem project_ne_or_next (T : InfiniteTraversal W Y root) (n : Nat) :
    T.projectedVertex n ≠ T.projectedVertex (n + 1) ∨
      T.projectedVertex (n + 1) ≠ T.projectedVertex (n + 2) := by
  by_contra h
  push_neg at h
  have hport := eq_of_two_project_stutters (T.steps n) (T.steps (n + 1))
    h.1 (by
      change projectPort (T.port (n + 1)) = projectPort (T.port (n + 2))
      exact h.2)
  exact (by omega : n ≠ n + 2) (T.injective hport)

/-- Indices of the genuine matching edges after identity contraction.  Once
the current genuine edge starts at `i`, the next one starts at `i+1` unless
that step is an identity, in which case it starts at `i+2`. -/
noncomputable def actualIndex (T : InfiniteTraversal W Y root) : Nat -> Nat
  | 0 => 0
  | n + 1 =>
      let i := T.actualIndex n
      if T.projectedVertex (i + 1) ≠ T.projectedVertex (i + 2) then i + 1
      else i + 2

@[simp] theorem actualIndex_zero (T : InfiniteTraversal W Y root) :
    T.actualIndex 0 = 0 := rfl

theorem actualIndex_succ (T : InfiniteTraversal W Y root) (n : Nat) :
    T.actualIndex (n + 1) =
      if T.projectedVertex (T.actualIndex n + 1) ≠
          T.projectedVertex (T.actualIndex n + 2) then
        T.actualIndex n + 1 else T.actualIndex n + 2 := rfl

theorem actualIndex_lt_succ (T : InfiniteTraversal W Y root) (n : Nat) :
    T.actualIndex n < T.actualIndex (n + 1) := by
  rw [T.actualIndex_succ]
  split <;> omega

theorem actualIndex_strictMono (T : InfiniteTraversal W Y root) :
    StrictMono T.actualIndex :=
  strictMono_nat_of_lt_succ T.actualIndex_lt_succ

/-- If the first matching step is literal, every selected step is literal. -/
theorem actualIndex_is_actual (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat) :
    T.projectedVertex (T.actualIndex n) ≠
      T.projectedVertex (T.actualIndex n + 1) := by
  induction n with
  | zero => simpa using hfirst
  | succ n ih =>
      rw [T.actualIndex_succ]
      split_ifs with hnext
      · exact hnext
      · exact (T.project_ne_or_next (T.actualIndex n + 1)).resolve_left hnext

/-- The endpoint of a selected literal edge is the start of the next selected
literal edge; an intervening identity step projects to equality. -/
theorem actualIndex_join (T : InfiniteTraversal W Y root) (n : Nat) :
    T.projectedVertex (T.actualIndex n + 1) =
      T.projectedVertex (T.actualIndex (n + 1)) := by
  rw [T.actualIndex_succ]
  split_ifs with hnext
  · rfl
  · exact Classical.not_not.mp hnext

/-- The identity-contracted raw vertex stream. -/
noncomputable def contractedVertex (T : InfiniteTraversal W Y root) : Nat -> V :=
  fun n => T.projectedVertex (T.actualIndex n)

@[simp] theorem contractedVertex_zero (T : InfiniteTraversal W Y root) :
    T.contractedVertex 0 = root := by
  simp [contractedVertex, projectedVertex, T.starts]

/-- The colour of the selected matching edge is determined by the copy at
which it starts. -/
noncomputable def contractedColour (T : InfiniteTraversal W Y root)
    (n : Nat) : Direction :=
  match T.port (T.actualIndex n) with
  | .inl _ => .forward
  | .inr _ => .backward

theorem contracted_edge (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat) :
    (T.contractedColour n = .forward ∧
      (T.contractedVertex n, T.contractedVertex (n + 1)) ∈ familyEdges W ∧
      (T.contractedVertex n, T.contractedVertex (n + 1)) ∉ familyEdges Y) ∨
    (T.contractedColour n = .backward ∧
      (T.contractedVertex (n + 1), T.contractedVertex n) ∈ familyEdges Y ∧
      (T.contractedVertex (n + 1), T.contractedVertex n) ∉ familyEdges W) := by
  have hstep := T.steps (T.actualIndex n)
  have hactual := T.actualIndex_is_actual hfirst n
  rcases step_of_project_ne hstep hactual with
    ⟨x, y, hleft, hright, hW, hY⟩ | ⟨x, y, hleft, hright, hY, hW⟩
  · left
    have hjoin := T.actualIndex_join n
    have hcur : T.projectedVertex (T.actualIndex n) = x := by
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
    have hjoin := T.actualIndex_join n
    have hcur : T.projectedVertex (T.actualIndex n) = y := by
      simp [projectedVertex, hleft]
    refine ⟨?_, ?_, ?_⟩
    · simp [contractedColour, hleft]
    · simp only [contractedVertex]
      rw [hcur, ← hjoin]
      simpa [projectedVertex, hright] using hY
    · simp only [contractedVertex]
      rw [hcur, ← hjoin]
      simpa [projectedVertex, hright] using hW

theorem contracted_forward_mem (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat)
    (hdir : T.contractedColour n = .forward) :
    (T.contractedVertex n, T.contractedVertex (n + 1)) ∈ familyEdges W := by
  rcases T.contracted_edge hfirst n with h | h
  · exact h.2.1
  · exact False.elim (by simpa [h.1] using hdir)

theorem contracted_backward_mem (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat)
    (hdir : T.contractedColour n = .backward) :
    (T.contractedVertex (n + 1), T.contractedVertex n) ∈ familyEdges Y := by
  rcases T.contracted_edge hfirst n with h | h
  · exact False.elim (by simpa [h.1] using hdir)
  · exact h.2.1

/-- Contracting identities does not erase the reference-contact labels at
the endpoints of a literal forward matching edge. -/
theorem contracted_forward_contacts_marked
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat)
    (hdir : T.contractedColour n = .forward) :
    ((∃ z, Exclusive Y W (T.contractedVertex n) z) →
        T.ReferenceContact (T.contractedVertex n)) ∧
      ((∃ z, Exclusive Y W z (T.contractedVertex (n + 1))) →
        T.ReferenceContact (T.contractedVertex (n + 1))) := by
  have hstep := T.steps (T.actualIndex n)
  have hactual := T.actualIndex_is_actual hfirst n
  rcases step_of_project_ne hstep hactual with
    ⟨x, y, hleft, hright, _hW, _hY⟩ |
    ⟨x, y, hleft, _hright, _hY, _hW⟩
  · have hcovered := T.forward_contact_covered (T.actualIndex n) hleft hright
    have hjoin := T.actualIndex_join n
    constructor
    · intro hx
      have hx' : ∃ z, Exclusive Y W x z := by
        simpa [contractedVertex, projectedVertex, hleft] using hx
      refine ⟨.inl x, hcovered.1 hx', ?_⟩
      simp [contractedVertex, projectedVertex, hleft]
    · intro hy
      have hend : T.projectedVertex (T.actualIndex n + 1) = y := by
        simp [projectedVertex, hright]
      have hnext : T.projectedVertex (T.actualIndex (n + 1)) = y :=
        hjoin.symm.trans hend
      have hy' : ∃ z, Exclusive Y W z y := by
        simpa [contractedVertex, hnext] using hy
      refine ⟨.inr y, hcovered.2 hy', ?_⟩
      simpa [contractedVertex] using hnext.symm
  · exfalso
    change (match T.port (T.actualIndex n) with
      | .inl _ => Direction.forward
      | .inr _ => Direction.backward) = .forward at hdir
    rw [hleft] at hdir
    contradiction

/-- The projected stream is at most two-to-one: the matching traversal can
visit at most the sending and receiving copy of a fixed ambient vertex. -/
theorem contracted_occurrenceFiber_finite (T : InfiniteTraversal W Y root)
    (n : Nat) :
    (occurrenceFiber T.contractedVertex n).Finite := by
  let g : Nat -> Port V := fun k => T.port (T.actualIndex k)
  have hg : Function.Injective g :=
    T.injective.comp T.actualIndex_strictMono.injective
  have hfinite : ({.inl (T.contractedVertex n),
      .inr (T.contractedVertex n)} : Set (Port V)).Finite :=
    (Set.finite_singleton (Sum.inr (T.contractedVertex n))).insert _
  have hpre := hfinite.preimage hg.injOn
  apply hpre.subset
  intro k hk
  change T.contractedVertex k = T.contractedVertex n at hk
  change g k ∈ ({.inl (T.contractedVertex n),
    .inr (T.contractedVertex n)} : Set (Port V))
  rcases hport : g k with x | x <;> simp only [Set.mem_insert_iff,
    Set.mem_singleton_iff, Sum.inl.injEq, Sum.inr.injEq,
    Sum.inl_ne_inr, Sum.inr_ne_inl, false_or, or_false]
  · simpa [contractedVertex, projectedVertex, g, hport] using hk
  · simpa [contractedVertex, projectedVertex, g, hport] using hk

/-- The contracted stream, after chronological loop erasure, is a genuine
input to the existing maximal-run compressor. -/
noncomputable def compressorInput (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) :
    RunCompressor.InfiniteInput Gamma.graph := by
  let hf := T.contracted_occurrenceFiber_finite
  exact {
    vertex := fun n => T.contractedVertex
      (loopErasedIndex T.contractedVertex hf n)
    vertex_injective := injective_loopErasedVertex T.contractedVertex hf
    colour := fun n => T.contractedColour
      (loopErasedIndex T.contractedVertex hf n)
    forward_adj := by
      intro n hn
      rw [← loopErasedIndex_join T.contractedVertex hf n]
      exact familyEdges_subset_adj W
        (T.contracted_forward_mem hfirst _ hn)
    backward_adj := by
      intro n hn
      rw [← loopErasedIndex_join T.contractedVertex hf n]
      exact familyEdges_subset_adj Y
        (T.contracted_backward_mem hfirst _ hn) }

@[simp] theorem compressorInput_vertex (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat) :
    (T.compressorInput hfirst).vertex n =
      T.contractedVertex (loopErasedIndex T.contractedVertex
        T.contracted_occurrenceFiber_finite n) := rfl

@[simp] theorem compressorInput_colour (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat) :
    (T.compressorInput hfirst).colour n =
      T.contractedColour (loopErasedIndex T.contractedVertex
        T.contracted_occurrenceFiber_finite n) := rfl

theorem compressorInput_forward_mem (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat)
    (hdir : (T.compressorInput hfirst).colour n = .forward) :
    ((T.compressorInput hfirst).vertex n,
      (T.compressorInput hfirst).vertex (n + 1)) ∈ familyEdges W := by
  let hf := T.contracted_occurrenceFiber_finite
  change (T.contractedVertex (loopErasedIndex T.contractedVertex hf n),
      T.contractedVertex (loopErasedIndex T.contractedVertex hf (n + 1))) ∈
    familyEdges W
  rw [← loopErasedIndex_join T.contractedVertex hf n]
  exact T.contracted_forward_mem hfirst _ hdir

theorem compressorInput_forward_not_mem_reference
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat)
    (hdir : (T.compressorInput hfirst).colour n = .forward) :
    ((T.compressorInput hfirst).vertex n,
      (T.compressorInput hfirst).vertex (n + 1)) ∉ familyEdges Y := by
  let hf := T.contracted_occurrenceFiber_finite
  change (T.contractedVertex (loopErasedIndex T.contractedVertex hf n),
      T.contractedVertex (loopErasedIndex T.contractedVertex hf (n + 1))) ∉
    familyEdges Y
  rw [← loopErasedIndex_join T.contractedVertex hf n]
  rcases T.contracted_edge hfirst (loopErasedIndex T.contractedVertex hf n) with
    h | h
  · exact h.2.2
  · exact False.elim (by simpa [h.1] using hdir)

theorem compressorInput_backward_mem (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat)
    (hdir : (T.compressorInput hfirst).colour n = .backward) :
    ((T.compressorInput hfirst).vertex (n + 1),
      (T.compressorInput hfirst).vertex n) ∈ familyEdges Y := by
  let hf := T.contracted_occurrenceFiber_finite
  change (T.contractedVertex (loopErasedIndex T.contractedVertex hf (n + 1)),
      T.contractedVertex (loopErasedIndex T.contractedVertex hf n)) ∈
    familyEdges Y
  rw [← loopErasedIndex_join T.contractedVertex hf n]
  exact T.contracted_backward_mem hfirst _ hdir

theorem compressorInput_forward_contacts_marked
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1) (n : Nat)
    (hdir : (T.compressorInput hfirst).colour n = .forward) :
    ((∃ z, Exclusive Y W ((T.compressorInput hfirst).vertex n) z) →
        T.ReferenceContact ((T.compressorInput hfirst).vertex n)) ∧
      ((∃ z, Exclusive Y W z
          ((T.compressorInput hfirst).vertex (n + 1))) →
        T.ReferenceContact ((T.compressorInput hfirst).vertex (n + 1))) := by
  let hf := T.contracted_occurrenceFiber_finite
  let q := loopErasedIndex T.contractedVertex hf n
  have hc := T.contracted_forward_contacts_marked hfirst q hdir
  have hjoin := loopErasedIndex_join T.contractedVertex hf n
  constructor
  · intro h
    apply hc.1
    simpa [compressorInput, q] using h
  · intro h
    have h' : ∃ z, Exclusive Y W z (T.contractedVertex (q + 1)) := by
      change ∃ z, Exclusive Y W z
        (T.contractedVertex (loopErasedIndex T.contractedVertex hf (n + 1))) at h
      rw [← hjoin] at h
      simpa [q] using h
    have hm := hc.2 h'
    change T.ReferenceContact
      (T.contractedVertex (loopErasedIndex T.contractedVertex hf (n + 1)))
    rw [← hjoin]
    simpa [q] using hm

/-- Finite forward members and the intrinsic well-foundedness of backward
traversal on a path force infinitely many colour changes. -/
theorem compressorInput_changes (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) :
    ∀ n, ∃ m, n < m ∧
      (T.compressorInput hfirst).colour m ≠
        (T.compressorInput hfirst).colour n := by
  intro n
  by_contra hno
  push Not at hno
  let S := T.compressorInput hfirst
  have htail : ∀ k, S.colour (n + k) = S.colour n := by
    intro k
    cases k with
    | zero => simp
    | succ k => exact hno _ (by omega)
  cases hn : S.colour n with
  | forward =>
      apply familyEdges_not_containsDirectedRay_of_finite hW hWfinite
      let R : DirectedRay V := {
        vertex := fun k => S.vertex (n + k)
        injective := by
          intro i j hij
          exact Nat.add_left_cancel (S.vertex_injective hij) }
      refine ⟨R, ?_⟩
      rintro e ⟨k, rfl⟩
      have hk : S.colour (n + k) = .forward := (htail k).trans hn
      simpa [R, S, Nat.add_assoc] using
        T.compressorInput_forward_mem hfirst (n + k) hk
  | backward =>
      apply familyEdges_not_containsReverseDirectedRay hY
      let R : DirectedRay V := {
        vertex := fun k => S.vertex (n + k)
        injective := by
          intro i j hij
          exact Nat.add_left_cancel (S.vertex_injective hij) }
      refine ⟨R, ?_⟩
      intro k
      have hk : S.colour (n + k) = .backward := (htail k).trans hn
      simpa [R, S, Nat.add_assoc] using
        T.compressorInput_backward_mem hfirst (n + k) hk

/-- Maximal-run compression of the genuine, identity-contracted matching
component.  The change hypothesis is separated because its proof uses the
finite-character/well-foundedness hypotheses on the two concrete warps. -/
noncomputable def runWalk (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (T.compressorInput hfirst).colour m ≠
        (T.compressorInput hfirst).colour n) :
    InfiniteRunWalk Gamma.graph :=
  (T.compressorInput hfirst).toInfiniteRunWalk hchange

/-- The unconditional infinite run compiler for a finite-character forward
warp and an arbitrary reference warp. -/
noncomputable def compiledRunWalk (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) : InfiniteRunWalk Gamma.graph :=
  T.runWalk hfirst (T.compressorInput_changes hfirst hW hWfinite hY)

theorem runWalk_forward_edge_mem (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (T.compressorInput hfirst).colour m ≠
        (T.compressorInput hfirst).colour n)
    (i : Nat) (hdir : ((T.runWalk hfirst hchange).run i).link.direction =
      .forward) :
    ((T.runWalk hfirst hchange).run i).link.path.edgeSet ⊆ familyEdges W := by
  intro e he
  let S := T.compressorInput hfirst
  change (S.projectedRun hchange i).link.direction = .forward at hdir
  have hprov := S.projectedRun_edge_provenance hchange i he
  rcases hprov with ⟨_hforward, k, hklo, hkhi, rfl⟩ |
      ⟨hbackward, k, hklo, hkhi, rfl⟩
  · apply T.compressorInput_forward_mem hfirst k
    have hcolour := RunCompressor.colour_eq_on_run S.colour hchange hklo hkhi
    exact hcolour.trans (by
      rw [← S.projectedRun_direction hchange i]
      exact hdir)
  · rw [hdir] at hbackward
    contradiction

theorem runWalk_forward_edge_not_mem_reference
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (T.compressorInput hfirst).colour m ≠
        (T.compressorInput hfirst).colour n)
    (i : Nat) (hdir : ((T.runWalk hfirst hchange).run i).link.direction =
      .forward) :
    Disjoint (((T.runWalk hfirst hchange).run i).link.path.edgeSet)
      (familyEdges Y) := by
  rw [Set.disjoint_left]
  intro e he hY
  let S := T.compressorInput hfirst
  change (S.projectedRun hchange i).link.direction = .forward at hdir
  have hprov := S.projectedRun_edge_provenance hchange i he
  rcases hprov with ⟨_hforward, k, hklo, hkhi, rfl⟩ |
      ⟨hbackward, k, hklo, hkhi, rfl⟩
  · apply T.compressorInput_forward_not_mem_reference hfirst k _ hY
    have hcolour := RunCompressor.colour_eq_on_run S.colour hchange hklo hkhi
    exact hcolour.trans (by
      rw [← S.projectedRun_direction hchange i]
      exact hdir)
  · rw [hdir] at hbackward
    contradiction

theorem runWalk_backward_edge_mem (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (T.compressorInput hfirst).colour m ≠
        (T.compressorInput hfirst).colour n)
    (i : Nat) (hdir : ((T.runWalk hfirst hchange).run i).link.direction =
      .backward) :
    ((T.runWalk hfirst hchange).run i).link.path.edgeSet ⊆ familyEdges Y := by
  intro e he
  let S := T.compressorInput hfirst
  change (S.projectedRun hchange i).link.direction = .backward at hdir
  have hprov := S.projectedRun_edge_provenance hchange i he
  rcases hprov with ⟨hforward, k, hklo, hkhi, rfl⟩ |
      ⟨_hbackward, k, hklo, hkhi, rfl⟩
  · rw [hdir] at hforward
    contradiction
  · apply T.compressorInput_backward_mem hfirst k
    have hcolour := RunCompressor.colour_eq_on_run S.colour hchange hklo hkhi
    exact hcolour.trans (by
      rw [← S.projectedRun_direction hchange i]
      exact hdir)

theorem compiledRunWalk_forward_edge_not_mem_reference
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hW : Gamma.IsWarp W) (hWfinite : Gamma.HasFiniteCharacter W)
    (hY : Gamma.IsWarp Y) (i : Nat)
    (hdir : ((T.compiledRunWalk hfirst hW hWfinite hY).run i).link.direction =
      .forward) :
    Disjoint
      (((T.compiledRunWalk hfirst hW hWfinite hY).run i).link.path.edgeSet)
      (familyEdges Y) :=
  T.runWalk_forward_edge_not_mem_reference hfirst
    (T.compressorInput_changes hfirst hW hWfinite hY) i hdir

/-- The normalization assumption makes the projected source occurrence
unique: neither an actual edge nor an identity matching edge can enter the
receiving copy of a source. -/
theorem projectedVertex_eq_root_index_zero (T : InfiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    {n : Nat} (hn : T.projectedVertex n = root) : n = 0 := by
  rcases hport : T.port n with x | x
  · have hx : x = root := by
      simpa [projectedVertex, hport] using hn
    subst x
    apply T.injective
    simpa [hport] using T.starts.symm
  · have hx : x = root := by
      simpa [projectedVertex, hport] using hn
    subst x
    by_contra hn0
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hstep := T.steps m
    rw [hport] at hstep
    rcases hprev : T.port m with y | y
    · rw [hprev] at hstep
      rcases hstep.1 with hedge | hid
      · exact (hGamma (familyEdges_subset_adj W hedge)).1 hsource
      · apply hid.2.2.1
        rw [hid.1]
        exact hsource
    · rw [hprev] at hstep
      exact False.elim hstep

theorem contractedVertex_eq_root_index_zero
    (T : InfiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    {n : Nat} (hn : T.contractedVertex n = root) : n = 0 := by
  have hraw : T.actualIndex n = 0 :=
    T.projectedVertex_eq_root_index_zero hGamma hsource hn
  exact T.actualIndex_strictMono.injective
    (hraw.trans T.actualIndex_zero.symm)

@[simp] theorem compressorInput_vertex_zero_of_source
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source) :
    (T.compressorInput hfirst).vertex 0 = root := by
  let hf := T.contracted_occurrenceFiber_finite
  change T.contractedVertex
      (loopErasedIndex T.contractedVertex hf 0) = root
  rw [loopErasedIndex_zero_eq_zero_of_root_unique
    T.contractedVertex hf (fun m hm =>
      T.contractedVertex_eq_root_index_zero hGamma hsource
        (hm.trans T.contractedVertex_zero))]
  exact T.contractedVertex_zero

@[simp] theorem runWalk_initial_of_source
    (T : InfiniteTraversal W Y root)
    (hfirst : T.projectedVertex 0 ≠ T.projectedVertex 1)
    (hchange : ∀ n, ∃ m, n < m ∧
      (T.compressorInput hfirst).colour m ≠
        (T.compressorInput hfirst).colour n)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source) :
    (T.runWalk hfirst hchange).vertex 0 = root := by
  exact T.compressorInput_vertex_zero_of_source hfirst hGamma hsource

end InfiniteTraversal

namespace FiniteTraversal

variable {W Y : Set Gamma.DPath} {root : V}

/-- Ambient projection of a bounded matching-component traversal. -/
def projectedVertex (T : FiniteTraversal W Y root)
    (i : Fin (T.lastIndex + 1)) : V :=
  projectPort (T.port i)

def ReferenceContact (T : FiniteTraversal W Y root) (x : V) : Prop :=
  ∃ a : Port V, T.ReferenceCovered a ∧ projectPort a = x

@[simp] theorem projectedVertex_zero (T : FiniteTraversal W Y root) :
    T.projectedVertex 0 = root := by
  simp [projectedVertex, T.starts]

/-- In a normalized web the source is unique even after the sending and
receiving copies are identified. -/
theorem projectedVertex_eq_root_index_zero (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    {i : Fin (T.lastIndex + 1)} (hi : T.projectedVertex i = root) : i.1 = 0 := by
  rcases hport : T.port i with x | x
  · have hx : x = root := by
      simpa [projectedVertex, hport] using hi
    subst x
    have heq : i = 0 := T.injective (by simpa [hport] using T.starts.symm)
    exact congrArg Fin.val heq
  · have hx : x = root := by
      simpa [projectedVertex, hport] using hi
    subst x
    by_contra hi0
    let j : Fin T.lastIndex := ⟨i.1 - 1, by omega⟩
    have hjsucc : j.succ = i := by
      apply Fin.ext
      dsimp [j]
      omega
    have hstep := T.steps j
    rw [hjsucc, hport] at hstep
    rcases hprev : T.port j.castSucc with y | y
    · rw [hprev] at hstep
      rcases hstep.1 with hedge | hid
      · exact (hGamma (familyEdges_subset_adj W hedge)).1 hsource
      · apply hid.2.2.1
        rw [hid.1]
        exact hsource
    · rw [hprev] at hstep
      exact False.elim hstep

/-- A chronological-erasure position cannot retain an identity step: its
endpoint would be a strictly later occurrence of the same projected vertex. -/
theorem finiteLoopIndex_is_actual (T : FiniteTraversal W Y root)
    {k : Nat} (hk : k < finiteLoopLength T.projectedVertex) :
    T.projectedVertex (finiteLoopIndex T.projectedVertex k) ≠
      T.projectedVertex ⟨(finiteLoopIndex T.projectedVertex k).1 + 1, by
        have := finiteLoopIndex_lt_top_of_lt_length T.projectedVertex hk
        omega⟩ := by
  intro heq
  have hlast := finiteLoopIndex_is_last T.projectedVertex k
    (j := ⟨(finiteLoopIndex T.projectedVertex k).1 + 1, by
      have := finiteLoopIndex_lt_top_of_lt_length T.projectedVertex hk
      omega⟩) heq.symm
  have hle := Fin.mk_le_mk.mp hlast
  omega

noncomputable def retainedColour (T : FiniteTraversal W Y root)
    (k : Fin (finiteLoopLength T.projectedVertex)) : Direction :=
  match T.port (finiteLoopIndex T.projectedVertex k.1) with
  | .inl _ => .forward
  | .inr _ => .backward

/-- Bounded chronological erasure simultaneously removes ambient loops and
all identity matching steps.  The exact essential hypothesis is uniqueness
of the projected root occurrence; genuine normalized sources are one way to
supply it, while a first-return cut supplies it for internal occurrences. -/
noncomputable def compressorInputOfRootUnique
    (T : FiniteTraversal W Y root)
    (hrootUnique : ∀ i, T.projectedVertex i = T.projectedVertex 0 → i.1 = 0) :
    RunCompressor.FiniteInput Gamma.graph where
  lastEdge := finiteLoopLength T.projectedVertex
  lastEdge_pos := finiteLoopLength_pos T.positive T.projectedVertex
    hrootUnique
  vertex := finiteLoopVertex T.projectedVertex
  vertex_injective_on := fun hi hj h =>
    finiteLoopVertex_injective_on T.projectedVertex hi hj h
  colour := T.retainedColour
  forward_adj := by
    intro k hdir
    let i := finiteLoopIndex T.projectedVertex k.1
    have hi : i.1 < T.lastIndex :=
      finiteLoopIndex_lt_top_of_lt_length T.projectedVertex k.2
    have hactual := T.finiteLoopIndex_is_actual k.2
    let j : Fin T.lastIndex := ⟨i.1, hi⟩
    have hcast : j.castSucc = i := Fin.ext rfl
    have hsucc : j.succ =
        (⟨i.1 + 1, by omega⟩ : Fin (T.lastIndex + 1)) := Fin.ext rfl
    have hstep := T.steps j
    rcases step_of_project_ne hstep hactual with
      ⟨x, y, hleft, hright, hW, _hY⟩ |
      ⟨x, y, hleft, hright, _hY, _hW⟩
    · rw [hcast] at hleft
      rw [hsucc] at hright
      dsimp [i] at hleft hright
      rcases finiteLoopVertex_succ T.projectedVertex k.2 with ⟨hcur, hnext⟩
      rw [hcur, hnext]
      have hadj := familyEdges_subset_adj W hW
      simpa [projectedVertex, hleft, hright] using hadj
    · exfalso
      rw [hcast] at hleft
      change (match T.port i with
        | .inl _ => Direction.forward
        | .inr _ => Direction.backward) = .forward at hdir
      rw [hleft] at hdir
      contradiction
  backward_adj := by
    intro k hdir
    let i := finiteLoopIndex T.projectedVertex k.1
    have hi : i.1 < T.lastIndex :=
      finiteLoopIndex_lt_top_of_lt_length T.projectedVertex k.2
    have hactual := T.finiteLoopIndex_is_actual k.2
    let j : Fin T.lastIndex := ⟨i.1, hi⟩
    have hcast : j.castSucc = i := Fin.ext rfl
    have hsucc : j.succ =
        (⟨i.1 + 1, by omega⟩ : Fin (T.lastIndex + 1)) := Fin.ext rfl
    have hstep := T.steps j
    rcases step_of_project_ne hstep hactual with
      ⟨x, y, hleft, hright, _hW, _hY⟩ |
      ⟨x, y, hleft, hright, hY, _hW⟩
    · exfalso
      rw [hcast] at hleft
      change (match T.port i with
        | .inl _ => Direction.forward
        | .inr _ => Direction.backward) = .backward at hdir
      rw [hleft] at hdir
      contradiction
    · rw [hcast] at hleft
      rw [hsucc] at hright
      dsimp [i] at hleft hright
      rcases finiteLoopVertex_succ T.projectedVertex k.2 with ⟨hcur, hnext⟩
      rw [hcur, hnext]
      have hadj := familyEdges_subset_adj Y hY
      simpa [projectedVertex, hleft, hright] using hadj

/-- Normalized web sources have a unique projected occurrence, yielding the
original source-specialized compressor interface. -/
noncomputable def compressorInput (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source) :
    RunCompressor.FiniteInput Gamma.graph :=
  T.compressorInputOfRootUnique (fun i hi =>
    T.projectedVertex_eq_root_index_zero hGamma hsource
      (hi.trans T.projectedVertex_zero))

/-- The finite identity-contracted, loop-erased, maximal-run compressed
matching component. -/
noncomputable def compiledRunWalk (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source) :
    FiniteRunWalk Gamma.graph :=
  (T.compressorInput hGamma hsource).toFiniteRunWalk

theorem compressorInputOfRootUnique_edge (T : FiniteTraversal W Y root)
    (hrootUnique : ∀ i,
      T.projectedVertex i = T.projectedVertex 0 → i.1 = 0)
    (k : Fin (T.compressorInputOfRootUnique hrootUnique).lastEdge) :
    ((T.compressorInputOfRootUnique hrootUnique).colour k = .forward ∧
      ((T.compressorInputOfRootUnique hrootUnique).vertex k,
        (T.compressorInputOfRootUnique hrootUnique).vertex (k.1 + 1)) ∈
          familyEdges W ∧
      ((T.compressorInputOfRootUnique hrootUnique).vertex k,
        (T.compressorInputOfRootUnique hrootUnique).vertex (k.1 + 1)) ∉
          familyEdges Y) ∨
    ((T.compressorInputOfRootUnique hrootUnique).colour k = .backward ∧
      ((T.compressorInputOfRootUnique hrootUnique).vertex (k.1 + 1),
        (T.compressorInputOfRootUnique hrootUnique).vertex k) ∈ familyEdges Y ∧
      ((T.compressorInputOfRootUnique hrootUnique).vertex (k.1 + 1),
        (T.compressorInputOfRootUnique hrootUnique).vertex k) ∉ familyEdges W) := by
  let i := finiteLoopIndex T.projectedVertex k.1
  have hi : i.1 < T.lastIndex :=
    finiteLoopIndex_lt_top_of_lt_length T.projectedVertex k.2
  have hactual := T.finiteLoopIndex_is_actual k.2
  let j : Fin T.lastIndex := ⟨i.1, hi⟩
  have hcast : j.castSucc = i := Fin.ext rfl
  have hsucc : j.succ =
      (⟨i.1 + 1, by omega⟩ : Fin (T.lastIndex + 1)) := Fin.ext rfl
  have hstep := T.steps j
  rcases step_of_project_ne hstep hactual with
    ⟨x, y, hleft, hright, hW, hY⟩ |
    ⟨x, y, hleft, hright, hY, hW⟩
  · left
    rw [hcast] at hleft
    rw [hsucc] at hright
    dsimp [i] at hleft hright
    rcases finiteLoopVertex_succ T.projectedVertex k.2 with ⟨hcur, hnext⟩
    refine ⟨?_, ?_, ?_⟩
    · change T.retainedColour k = .forward
      simp [retainedColour, hleft]
    · change (finiteLoopVertex T.projectedVertex k.1,
          finiteLoopVertex T.projectedVertex (k.1 + 1)) ∈ familyEdges W
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hW
    · change (finiteLoopVertex T.projectedVertex k.1,
          finiteLoopVertex T.projectedVertex (k.1 + 1)) ∉ familyEdges Y
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hY
  · right
    rw [hcast] at hleft
    rw [hsucc] at hright
    dsimp [i] at hleft hright
    rcases finiteLoopVertex_succ T.projectedVertex k.2 with ⟨hcur, hnext⟩
    refine ⟨?_, ?_, ?_⟩
    · change T.retainedColour k = .backward
      simp [retainedColour, hleft]
    · change (finiteLoopVertex T.projectedVertex (k.1 + 1),
          finiteLoopVertex T.projectedVertex k.1) ∈ familyEdges Y
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hY
    · change (finiteLoopVertex T.projectedVertex (k.1 + 1),
          finiteLoopVertex T.projectedVertex k.1) ∉ familyEdges W
      rw [hcur, hnext]
      simpa [projectedVertex, hleft, hright] using hW

theorem compressorInput_edge (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (k : Fin (T.compressorInput hGamma hsource).lastEdge) :
    ((T.compressorInput hGamma hsource).colour k = .forward ∧
      ((T.compressorInput hGamma hsource).vertex k,
        (T.compressorInput hGamma hsource).vertex (k.1 + 1)) ∈ familyEdges W ∧
      ((T.compressorInput hGamma hsource).vertex k,
        (T.compressorInput hGamma hsource).vertex (k.1 + 1)) ∉ familyEdges Y) ∨
    ((T.compressorInput hGamma hsource).colour k = .backward ∧
      ((T.compressorInput hGamma hsource).vertex (k.1 + 1),
        (T.compressorInput hGamma hsource).vertex k) ∈ familyEdges Y ∧
      ((T.compressorInput hGamma hsource).vertex (k.1 + 1),
        (T.compressorInput hGamma hsource).vertex k) ∉ familyEdges W) :=
  T.compressorInputOfRootUnique_edge
    (fun i hi => T.projectedVertex_eq_root_index_zero hGamma hsource
      (hi.trans T.projectedVertex_zero)) k

/-- Finite chronological erasure preserves the reference-contact labels at
the endpoints of every retained forward matching edge. -/
theorem compressorInputOfRootUnique_forward_contacts_marked
    (T : FiniteTraversal W Y root)
    (hrootUnique : ∀ i,
      T.projectedVertex i = T.projectedVertex 0 → i.1 = 0)
    (k : Fin (T.compressorInputOfRootUnique hrootUnique).lastEdge)
    (hdir : (T.compressorInputOfRootUnique hrootUnique).colour k = .forward) :
    ((∃ z, Exclusive Y W
        ((T.compressorInputOfRootUnique hrootUnique).vertex k) z) →
        T.ReferenceContact
          ((T.compressorInputOfRootUnique hrootUnique).vertex k)) ∧
      ((∃ z, Exclusive Y W z
          ((T.compressorInputOfRootUnique hrootUnique).vertex (k.1 + 1))) →
        T.ReferenceContact
          ((T.compressorInputOfRootUnique hrootUnique).vertex (k.1 + 1))) := by
  let i := finiteLoopIndex T.projectedVertex k.1
  have hi : i.1 < T.lastIndex :=
    finiteLoopIndex_lt_top_of_lt_length T.projectedVertex k.2
  have hactual := T.finiteLoopIndex_is_actual k.2
  let j : Fin T.lastIndex := ⟨i.1, hi⟩
  have hcast : j.castSucc = i := Fin.ext rfl
  have hsucc : j.succ =
      (⟨i.1 + 1, by omega⟩ : Fin (T.lastIndex + 1)) := Fin.ext rfl
  have hstep := T.steps j
  rcases step_of_project_ne hstep hactual with
    ⟨x, y, hleft, hright, _hW, _hY⟩ |
    ⟨x, y, hleft, _hright, _hY, _hW⟩
  · rw [hcast] at hleft
    rw [hsucc] at hright
    dsimp [i] at hleft hright
    have hleftj : T.port j.castSucc = .inl x := by
      rw [hcast]
      exact hleft
    have hrightj : T.port j.succ = .inr y := by
      rw [hsucc]
      exact hright
    have hcovered := T.forward_contact_covered j hleftj hrightj
    rcases finiteLoopVertex_succ T.projectedVertex k.2 with ⟨hcur, hnext⟩
    have hcurx : finiteLoopVertex T.projectedVertex k.1 = x :=
      hcur.trans (by simp [projectedVertex, hleft])
    have hnexty : finiteLoopVertex T.projectedVertex (k.1 + 1) = y :=
      hnext.trans (by simp [projectedVertex, hright])
    constructor
    · intro hx
      have hx' : ∃ z, Exclusive Y W x z := by
        simpa [compressorInputOfRootUnique, hcurx] using hx
      refine ⟨.inl x, hcovered.1 hx', ?_⟩
      simpa [compressorInputOfRootUnique, hcurx]
    · intro hy
      have hy' : ∃ z, Exclusive Y W z y := by
        simpa [compressorInputOfRootUnique, hnexty] using hy
      refine ⟨.inr y, hcovered.2 hy', ?_⟩
      simpa [compressorInputOfRootUnique, hnexty]
  · exfalso
    rw [hcast] at hleft
    change (match T.port i with
      | .inl _ => Direction.forward
      | .inr _ => Direction.backward) = .forward at hdir
    rw [hleft] at hdir
    contradiction

theorem compressorInput_forward_contacts_marked
    (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (k : Fin (T.compressorInput hGamma hsource).lastEdge)
    (hdir : (T.compressorInput hGamma hsource).colour k = .forward) :
    ((∃ z, Exclusive Y W ((T.compressorInput hGamma hsource).vertex k) z) →
        T.ReferenceContact ((T.compressorInput hGamma hsource).vertex k)) ∧
      ((∃ z, Exclusive Y W z
          ((T.compressorInput hGamma hsource).vertex (k.1 + 1))) →
        T.ReferenceContact
          ((T.compressorInput hGamma hsource).vertex (k.1 + 1))) :=
  T.compressorInputOfRootUnique_forward_contacts_marked
    (fun i hi => T.projectedVertex_eq_root_index_zero hGamma hsource
      (hi.trans T.projectedVertex_zero)) k hdir

theorem compiledRunWalk_forward_edge_not_mem_reference
    (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (i : Fin ((T.compiledRunWalk hGamma hsource).lastIndex + 1))
    (hdir : ((T.compiledRunWalk hGamma hsource).run i).link.direction =
      .forward) :
    Disjoint (((T.compiledRunWalk hGamma hsource).run i).link.path.edgeSet)
      (familyEdges Y) := by
  let S := T.compressorInput hGamma hsource
  change Disjoint ((S.projectedRun (S.runIndex i)).link.path.edgeSet)
    (familyEdges Y)
  change (S.projectedRun (S.runIndex i)).link.direction = .forward at hdir
  rw [Set.disjoint_left]
  intro e he hYmem
  have hprov := S.projectedRun_edge_provenance (S.runIndex i) he
  rcases hprov with ⟨_hforward, k, hk, rfl⟩ |
      ⟨hbackward, k, hk, rfl⟩
  · have hcolour : S.colour ⟨RunCompressor.runLower S.runs (S.runIndex i) + k,
        by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩ = .forward := by
      exact (S.colour_run_offset (S.runIndex i) hk).trans
        ((S.projectedRun_direction (S.runIndex i)).symm.trans hdir)
    let r : Fin (T.compressorInput hGamma hsource).lastEdge :=
      ⟨RunCompressor.runLower S.runs (S.runIndex i) + k, by
        change RunCompressor.runLower S.runs (S.runIndex i) + k < S.lastEdge
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
          (S.runUpper_le_lastEdge (S.runIndex i))⟩
    rcases T.compressorInput_edge hGamma hsource r with h | h
    · apply h.2.2
      simpa [S, r] using hYmem
    · rw [h.1] at hcolour
      contradiction
  · rw [hdir] at hbackward
    contradiction

theorem compiledRunWalk_backward_edge_mem
    (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source)
    (i : Fin ((T.compiledRunWalk hGamma hsource).lastIndex + 1))
    (hdir : ((T.compiledRunWalk hGamma hsource).run i).link.direction =
      .backward) :
    ((T.compiledRunWalk hGamma hsource).run i).link.path.edgeSet ⊆
      familyEdges Y := by
  let S := T.compressorInput hGamma hsource
  change (S.projectedRun (S.runIndex i)).link.path.edgeSet ⊆ familyEdges Y
  change (S.projectedRun (S.runIndex i)).link.direction = .backward at hdir
  intro e he
  have hprov := S.projectedRun_edge_provenance (S.runIndex i) he
  rcases hprov with ⟨hforward, k, hk, rfl⟩ |
      ⟨_hbackward, k, hk, rfl⟩
  · rw [hdir] at hforward
    contradiction
  · have hcolour : S.colour ⟨RunCompressor.runLower S.runs (S.runIndex i) + k,
        by
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩ = .backward := by
      exact (S.colour_run_offset (S.runIndex i) hk).trans
        ((S.projectedRun_direction (S.runIndex i)).symm.trans hdir)
    let r : Fin (T.compressorInput hGamma hsource).lastEdge :=
      ⟨RunCompressor.runLower S.runs (S.runIndex i) + k, by
        change RunCompressor.runLower S.runs (S.runIndex i) + k < S.lastEdge
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
          (S.runUpper_le_lastEdge (S.runIndex i))⟩
    rcases T.compressorInput_edge hGamma hsource r with h | h
    · rw [h.1] at hcolour
      contradiction
    · simpa [S, r] using h.2.1

@[simp] theorem compiledRunWalk_initial (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source) :
    (T.compiledRunWalk hGamma hsource).vertex 0 = root := by
  change finiteLoopVertex T.projectedVertex 0 = root
  rw [finiteLoopVertex_zero_of_root_unique T.projectedVertex
    (fun i hi => T.projectedVertex_eq_root_index_zero hGamma hsource
      (hi.trans T.projectedVertex_zero))]
  exact T.projectedVertex_zero

@[simp] theorem compiledRunWalk_terminal (T : FiniteTraversal W Y root)
    (hGamma : Gamma.IsNormalized) (hsource : root ∈ Gamma.source) :
    let Q := T.compiledRunWalk hGamma hsource
    Q.vertex (Q.run Q.lastRunIndex).last =
      T.projectedVertex ⟨T.lastIndex, Nat.lt_succ_self _⟩ := by
  let S := T.compressorInput hGamma hsource
  change S.vertex ((S.toFiniteRunWalk).run
      S.toFiniteRunWalk.lastRunIndex).last = _
  rw [S.toFiniteRunWalk_final_last]
  change finiteLoopVertex T.projectedVertex
      (finiteLoopLength T.projectedVertex) = _
  exact finiteLoopVertex_last T.projectedVertex

end FiniteTraversal

end

end TwoWarpMatchingTraversal
end Erdos599
