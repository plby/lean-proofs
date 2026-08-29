/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.TwoWarpOwnerComponentSwitch

/-!
# Whole-component switching need not preserve a distinguished pair

Closing the gaps of a nonconvex reference deletion can force an entire
two-warp owner component to be switched simultaneously.  The operation is
sound, but it need not leave a route between the two endpoints which first
generated the component.

The example below is the finite obstruction

* `W = {u-c-a, b-d-v, z-t}`;
* `Y = {b-a, z-c-d-t}`.

The alternating augmentation path from `u` to `v` uses the two separated
edges `z-c` and `d-t` of the second `Y`-member.  Filling the missing middle
of that owner adds the companion alternating cycle.  Whole-owner closure
then selects every `W`-member and every `Y`-member, so the component switch
is exactly `W`; `u` and `v` lie on distinct members and are no longer joined.
-/

namespace Erdos599
namespace TwoWarpOwnerComponentPairObstruction

open Set
open _root_.Erdos599.DirectedPath
open Alternating
open TwoWarpOwnerComponentSwitch

inductive Vertex
  | u | c | a | b | d | v | z | t
  deriving DecidableEq

open Vertex

def graph : Digraph Vertex where
  Adj x y :=
    (x = u ∧ y = c) ∨ (x = c ∧ y = a) ∨
    (x = b ∧ y = d) ∨ (x = d ∧ y = v) ∨
    (x = z ∧ y = t) ∨ (x = b ∧ y = a) ∨
    (x = z ∧ y = c) ∨ (x = c ∧ y = d) ∨ (x = d ∧ y = t)

def uca : FinitePath graph where
  start := u
  finish := a
  walk := Walk.cons (u := u) (v := c) (w := a) (by simp [graph])
    (Walk.cons (u := c) (v := a) (w := a) (by simp [graph]) Walk.nil)
  isPath := by
    change [u, c, a].Nodup
    simp

def bdv : FinitePath graph where
  start := b
  finish := v
  walk := Walk.cons (u := b) (v := d) (w := v) (by simp [graph])
    (Walk.cons (u := d) (v := v) (w := v) (by simp [graph]) Walk.nil)
  isPath := by
    change [b, d, v].Nodup
    simp

def zt : FinitePath graph where
  start := z
  finish := t
  walk := .cons (by simp [graph]) .nil
  isPath := by simp [Walk.IsPath, Walk.support]

def ba : FinitePath graph where
  start := b
  finish := a
  walk := .cons (by simp [graph]) .nil
  isPath := by simp [Walk.IsPath, Walk.support]

def zcdt : FinitePath graph where
  start := z
  finish := t
  walk := Walk.cons (u := z) (v := c) (w := t) (by simp [graph])
    (Walk.cons (u := c) (v := d) (w := t) (by simp [graph])
      (Walk.cons (u := d) (v := t) (w := t) (by simp [graph]) Walk.nil))
  isPath := by
    change [z, c, d, t].Nodup
    simp

@[simp] theorem uca_support : uca.support = {u, c, a} := by
  ext x
  simp [FinitePath.support, uca, Walk.support]

@[simp] theorem bdv_support : bdv.support = {b, d, v} := by
  ext x
  simp [FinitePath.support, bdv, Walk.support]

@[simp] theorem zt_support : zt.support = {z, t} := by
  ext x
  simp [FinitePath.support, zt, Walk.support]

@[simp] theorem ba_support : ba.support = {b, a} := by
  ext x
  simp [FinitePath.support, ba, Walk.support]

@[simp] theorem zcdt_support : zcdt.support = {z, c, d, t} := by
  ext x
  simp [FinitePath.support, zcdt, Walk.support]

abbrev web : DWeb Vertex where
  graph := graph
  source := {u, b, z}
  target := {a, v, t}

def W : Set web.DPath := {Sum.inl uca, Sum.inl bdv, Sum.inl zt}

def Y : Set web.DPath := {Sum.inl ba, Sum.inl zcdt}

theorem W_isWarp : web.IsWarp W := by
  intro p hp q hq hpq
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint uca.support bdv.support
    rw [uca_support, bdv_support]
    simp [Set.disjoint_left]
  · change Disjoint uca.support zt.support
    rw [uca_support, zt_support]
    simp [Set.disjoint_left]
  · change Disjoint bdv.support uca.support
    rw [bdv_support, uca_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim
  · change Disjoint bdv.support zt.support
    rw [bdv_support, zt_support]
    simp [Set.disjoint_left]
  · change Disjoint zt.support uca.support
    rw [zt_support, uca_support]
    simp [Set.disjoint_left]
  · change Disjoint zt.support bdv.support
    rw [zt_support, bdv_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim

theorem Y_isWarp : web.IsWarp Y := by
  intro p hp q hq hpq
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hpq rfl).elim
  · change Disjoint ba.support zcdt.support
    rw [ba_support, zcdt_support]
    simp [Set.disjoint_left]
  · change Disjoint zcdt.support ba.support
    rw [zcdt_support, ba_support]
    simp [Set.disjoint_left]
  · exact (hpq rfl).elim

theorem b_mem_ownerComponent : b ∈ ownerComponent W Y u := by
  have hu : u ∈ ownerComponent W Y u := mem_ownerComponent_self W Y u
  have huca := support_subset_ownerComponent_left
    (p := (.inl uca : web.DPath)) hu
    (show (.inl uca : web.DPath) ∈ W by simp [W])
    (show u ∈ DirectedPath.Path.support (.inl uca : web.DPath) by
      change u ∈ uca.support
      simp)
  have ha : a ∈ ownerComponent W Y u := huca (by
    change a ∈ uca.support
    simp)
  have hba := support_subset_ownerComponent_right
    (p := (.inl ba : web.DPath)) ha
    (show (.inl ba : web.DPath) ∈ Y by simp [Y])
    (show a ∈ DirectedPath.Path.support (.inl ba : web.DPath) by
      change a ∈ ba.support
      simp)
  exact hba (by
    change b ∈ ba.support
    simp)

theorem z_mem_ownerComponent : z ∈ ownerComponent W Y u := by
  have hu : u ∈ ownerComponent W Y u := mem_ownerComponent_self W Y u
  have huca := support_subset_ownerComponent_left
    (p := (.inl uca : web.DPath)) hu
    (show (.inl uca : web.DPath) ∈ W by simp [W])
    (show u ∈ DirectedPath.Path.support (.inl uca : web.DPath) by
      change u ∈ uca.support
      simp)
  have hc : c ∈ ownerComponent W Y u := huca (by
    change c ∈ uca.support
    simp)
  have hzcdt := support_subset_ownerComponent_right
    (p := (.inl zcdt : web.DPath)) hc
    (show (.inl zcdt : web.DPath) ∈ Y by simp [Y])
    (show c ∈ DirectedPath.Path.support (.inl zcdt : web.DPath) by
      change c ∈ zcdt.support
      simp)
  exact hzcdt (by
    change z ∈ zcdt.support
    simp)

theorem v_mem_ownerComponent : v ∈ ownerComponent W Y u := by
  have hbdv := support_subset_ownerComponent_left
    (p := (.inl bdv : web.DPath)) b_mem_ownerComponent
    (show (.inl bdv : web.DPath) ∈ W by simp [W])
    (show b ∈ DirectedPath.Path.support (.inl bdv : web.DPath) by
      change b ∈ bdv.support
      simp)
  exact hbdv (by
    change v ∈ bdv.support
    simp)

theorem selectedForward_eq_W : selectedForward W Y u = W := by
  apply Set.Subset.antisymm
  · exact fun _ hp ↦ hp.1
  · intro p hp
    simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨by simp [W], mem_ownerComponent_self W Y u⟩
    · exact ⟨by simp [W], b_mem_ownerComponent⟩
    · exact ⟨by simp [W], z_mem_ownerComponent⟩

theorem retainedReference_eq_empty : retainedReference W Y u = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  simp only [Y, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp.1 with rfl | rfl
  · exact hp.2 b_mem_ownerComponent
  · exact hp.2 z_mem_ownerComponent

theorem switchedFamily_eq_W : switchedFamily W Y u = W := by
  rw [switchedFamily, selectedForward_eq_W, retainedReference_eq_empty,
    Set.union_empty]

theorem no_W_member_contains_u_and_v :
    ¬ ∃ p ∈ W, u ∈ p.support ∧ v ∈ p.support := by
  rintro ⟨p, hp, hup, hvp⟩
  simp only [W, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · change v ∈ uca.support at hvp
    simpa using hvp
  · change u ∈ bdv.support at hup
    simpa using hup
  · change u ∈ zt.support at hup
    simpa using hup

/-- The two marked vertices belong to the same owner component, but the
whole-component switch contains no directed path from `u` to `v`. -/
theorem same_component_but_no_switched_path :
    v ∈ ownerComponent W Y u ∧
      ¬ ∃ p : FinitePath web.graph,
        p.start = u ∧ p.finish = v ∧
          p.edgeSet ⊆ familyEdges (switchedFamily W Y u) := by
  refine ⟨v_mem_ownerComponent, ?_⟩
  rintro ⟨p, hstart, hfinish, hpE⟩
  have hpne : p.start ≠ p.finish := by
    rw [hstart, hfinish]
    decide
  have hstartC : p.start ∈ ownerComponent W Y u := by
    rw [hstart]
    exact mem_ownerComponent_self W Y u
  obtain ⟨q, hqW, hsupport, _hedges⟩ :=
    finitePath_isFragmentOf_left_of_start_mem_ownerComponent
      W_isWarp p hpne hstartC hpE
  apply no_W_member_contains_u_and_v
  refine ⟨q, hqW, hsupport ?_, hsupport ?_⟩
  · change u ∈ DirectedPath.Path.support (Sum.inl p : web.DPath)
    change u ∈ p.support
    simpa [hstart] using p.start_mem_support
  · change v ∈ DirectedPath.Path.support (Sum.inl p : web.DPath)
    change v ∈ p.support
    simpa [hfinish] using p.finish_mem_support

#print axioms W_isWarp
#print axioms Y_isWarp
#print axioms switchedFamily_eq_W
#print axioms same_component_but_no_switched_path

end TwoWarpOwnerComponentPairObstruction
end Erdos599
