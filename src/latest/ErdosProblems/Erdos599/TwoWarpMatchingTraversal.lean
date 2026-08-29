/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingMacroChain
import ErdosProblems.Erdos599.SafeSwitching

/-!
# Contact-marked traversal of two warp matchings

The bipartite conversion of a warp replaces an ambient vertex by a sending
and a receiving copy.  A warp edge `x -> y` matches the sending copy of `x`
to the receiving copy of `y`; a vertex incident with no warp edge gets the
identity matching edge.  The union of the two matchings belonging to two
warps has components of degree at most two.

This file constructs the maximal component traversal rooted at an unmatched
sending copy.  It deliberately stays in the bipartite conversion: common
ambient edges remain distinguishable by their matching colour until the
symmetric difference removes them.  The final lemmas record the exact
pre-projection contact property: every endpoint of a forward matching edge
which is incident with a reference-only matching edge is covered by the
adjacent backward step of the same component.

No alternating-path projection is asserted here.  Identity matching edges
still have to be contracted and maximal monochromatic runs compressed before
the result can be fed to `FiniteRunWalk` or `InfiniteRunWalk`.
-/

namespace Erdos599
namespace TwoWarpMatchingTraversal

open Set DirectedPath
open Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- Vertices incident with an actual edge of a path family. -/
def edgeCarrier (W : Set Gamma.DPath) : Set V :=
  {x | (∃ y, (x, y) ∈ familyEdges W) ∨
    ∃ y, (y, x) ∈ familyEdges W}

/-- The matching `J(W)` in the bipartite conversion.  Its left endpoint is
the sending copy and its right endpoint is the receiving copy. -/
def matchingEdge (W : Set Gamma.DPath) (x y : V) : Prop :=
  (x, y) ∈ familyEdges W ∨
    (x = y ∧ x ∉ edgeCarrier W ∧
      x ∉ Gamma.source ∧ x ∉ Gamma.target)

theorem matchingEdge_actual {W : Set Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges W) : matchingEdge W x y :=
  Or.inl hxy

theorem matchingEdge_identity {W : Set Gamma.DPath} {x : V}
    (hx : x ∉ edgeCarrier W) (hsource : x ∉ Gamma.source)
    (htarget : x ∉ Gamma.target) : matchingEdge W x x :=
  Or.inr ⟨rfl, hx, hsource, htarget⟩

theorem matchingEdge_biUnique {W : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) :
    Relator.BiUnique (matchingEdge W) := by
  have hfamily := IsWarp.familyEdges_biUnique hW
  constructor
  · intro x y z hxz hyz
    rcases hxz with hxz | hxz
    · rcases hyz with hyz | hyz
      · exact hfamily.1 hxz hyz
      · exfalso
        apply hyz.2.1
        exact Or.inr ⟨x, by simpa [hyz.1] using hxz⟩
    · rcases hyz with hyz | hyz
      · exfalso
        apply hxz.2.1
        exact Or.inr ⟨y, by simpa [hxz.1] using hyz⟩
      · exact hxz.1.trans hyz.1.symm
  · intro x y z hxy hxz
    rcases hxy with hxy | hxy
    · rcases hxz with hxz | hxz
      · exact hfamily.2 hxy hxz
      · exfalso
        apply hxz.2.1
        exact Or.inl ⟨y, hxy⟩
    · rcases hxz with hxz | hxz
      · exfalso
        apply hxy.2.1
        exact Or.inl ⟨z, hxz⟩
      · exact hxy.1.symm.trans hxz.1

/-- A matching occurrence present only in the first matching. -/
def Exclusive (W Y : Set Gamma.DPath) (x y : V) : Prop :=
  matchingEdge W x y ∧ ¬ matchingEdge Y x y

/-- Sending and receiving copies in the bipartite conversion. -/
abbrev Port (V : Type u) := Sum V V

/-- Traverse a forward-only matching edge from sending to receiving, then a
reference-only matching edge backwards from receiving to sending. -/
def Step (W Y : Set Gamma.DPath) : Port V -> Port V -> Prop
  | .inl x, .inr y => Exclusive W Y x y
  | .inr y, .inl x => Exclusive Y W x y
  | _, _ => False

theorem step_cases {W Y : Set Gamma.DPath} {a b : Port V}
    (h : Step W Y a b) :
    (∃ x y, a = .inl x ∧ b = .inr y ∧ Exclusive W Y x y) ∨
      ∃ x y, a = .inr y ∧ b = .inl x ∧ Exclusive Y W x y := by
  rcases a with x | y
  · rcases b with x' | y'
    · exact False.elim h
    · exact Or.inl ⟨x, y', rfl, rfl, h⟩
  · rcases b with x' | y'
    · exact Or.inr ⟨x', y, rfl, rfl, h⟩
    · exact False.elim h

theorem step_biUnique {W Y : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) :
    Relator.BiUnique (Step W Y) := by
  have hWM := matchingEdge_biUnique hW
  have hYM := matchingEdge_biUnique hY
  constructor
  · intro a b c hac hbc
    rcases step_cases hac with
      ⟨x, y, rfl, hc, hxy⟩ | ⟨x, y, rfl, hc, hxy⟩
    · rcases step_cases hbc with
        ⟨x', y', rfl, hc', hx'y'⟩ | ⟨x', y', rfl, hc', hx'y'⟩
      · have hyy' : y = y' := Sum.inr.inj (hc.symm.trans hc')
        subst y'
        exact congrArg Sum.inl (hWM.1 hxy.1 hx'y'.1)
      · exact False.elim (Sum.inr_ne_inl (hc.symm.trans hc'))
    · rcases step_cases hbc with
        ⟨x', y', rfl, hc', hx'y'⟩ | ⟨x', y', rfl, hc', hx'y'⟩
      · exact False.elim (Sum.inl_ne_inr (hc.symm.trans hc'))
      · have hxx' : x = x' := Sum.inl.inj (hc.symm.trans hc')
        subst x'
        exact congrArg Sum.inr (hYM.2 hxy.1 hx'y'.1)
  · intro a b c hab hac
    rcases step_cases hab with
      ⟨x, y, ha, rfl, hxy⟩ | ⟨x, y, ha, rfl, hxy⟩
    · rcases step_cases hac with
        ⟨x', y', ha', rfl, hx'y'⟩ | ⟨x', y', ha', rfl, hx'y'⟩
      · have hxx' : x = x' := Sum.inl.inj (ha.symm.trans ha')
        subst x'
        exact congrArg Sum.inr (hWM.2 hxy.1 hx'y'.1)
      · exact False.elim (Sum.inl_ne_inr (ha.symm.trans ha'))
    · rcases step_cases hac with
        ⟨x', y', ha', rfl, hx'y'⟩ | ⟨x', y', ha', rfl, hx'y'⟩
      · exact False.elim (Sum.inr_ne_inl (ha.symm.trans ha'))
      · have hyy' : y = y' := Sum.inr.inj (ha.symm.trans ha')
        subst y'
        exact congrArg Sum.inl (hYM.1 hxy.1 hx'y'.1)

theorem forward_actual_not_reference {W Y : Set Gamma.DPath} {x y : V}
    (h : Exclusive W Y x y) (_hxy : (x, y) ∈ familyEdges W) :
    (x, y) ∉ familyEdges Y := by
  intro hY
  exact h.2 (matchingEdge_actual hY)

/-- A finite maximal traversal of a symmetric-difference component. -/
structure FiniteTraversal (W Y : Set Gamma.DPath) (root : V) where
  lastIndex : Nat
  positive : 0 < lastIndex
  port : Fin (lastIndex + 1) -> Port V
  starts : port 0 = .inl root
  steps : forall i : Fin lastIndex, Step W Y (port i.castSucc) (port i.succ)
  injective : Function.Injective port
  root_unmatched : ¬ ∃ y, Exclusive Y W root y
  terminal : ¬ ∃ b, Step W Y (port ⟨ lastIndex, Nat.lt_succ_self _⟩) b

/-- A one-way infinite traversal of a symmetric-difference component. -/
structure InfiniteTraversal (W Y : Set Gamma.DPath) (root : V) where
  port : Nat -> Port V
  starts : port 0 = .inl root
  steps : forall n, Step W Y (port n) (port (n + 1))
  injective : Function.Injective port
  root_unmatched : ¬ ∃ y, Exclusive Y W root y

/-- The two possible maximal rooted component shapes. -/
inductive Traversal (W Y : Set Gamma.DPath) (root : V)
  | finite (T : FiniteTraversal W Y root)
  | infinite (T : InfiniteTraversal W Y root)

noncomputable def nextPort (W Y : Set Gamma.DPath) (a : Port V) : Port V := by
  classical
  exact if h : ∃ b, Step W Y a b then Classical.choose h else a

theorem step_nextPort_of_exists {W Y : Set Gamma.DPath} {a : Port V}
    (h : ∃ b, Step W Y a b) : Step W Y a (nextPort W Y a) := by
  rw [nextPort, dif_pos h]
  exact Classical.choose_spec h

noncomputable def orbit (W Y : Set Gamma.DPath) (root : V) : Nat -> Port V
  | 0 => .inl root
  | n + 1 => nextPort W Y (orbit W Y root n)

@[simp] theorem orbit_zero (W Y : Set Gamma.DPath) (root : V) :
    orbit W Y root 0 = .inl root := rfl

@[simp] theorem orbit_succ (W Y : Set Gamma.DPath) (root : V) (n : Nat) :
    orbit W Y root (n + 1) = nextPort W Y (orbit W Y root n) := rfl

private theorem chain_ne_of_lt
    {A : Type*} {R : A -> A -> Prop} (hleft : Relator.LeftUnique R)
    {f : Nat -> A} {N : Nat}
    (hstep : forall k, k < N -> R (f k) (f (k + 1)))
    (hroot : ¬ ∃ a, R a (f 0)) :
    forall i j, i < j -> j <= N -> f i ≠ f j := by
  intro i
  induction i with
  | zero =>
      intro j hij hjN heq
      obtain ⟨ k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      apply hroot
      exact ⟨ f k, by simpa [heq] using hstep k (by omega)⟩
  | succ i ih =>
      intro j hij hjN heq
      obtain ⟨ k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hprev : f i = f k := hleft
        (hstep i (by omega)) (by simpa [heq] using hstep k (by omega))
      exact ih k (by omega) (by omega) hprev

/-- Starting at a forward-only matching edge and at a sending copy with no
reference-only predecessor, the complete symmetric-difference component is
either a finite simple path or a one-way infinite simple path. -/
theorem exists_traversal {W Y : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) (root : V)
    (hforward : ∃ y, Exclusive W Y root y)
    (hroot : ¬ ∃ y, Exclusive Y W root y) :
    Nonempty (Traversal W Y root) := by
  classical
  let f := orbit W Y root
  have hf0 : f 0 = .inl root := rfl
  have hrootRange : ¬ ∃ a, Step W Y a (f 0) := by
    rintro ⟨ a, ha⟩
    rw [hf0] at ha
    rcases a with x | y <;> simp only [Step] at ha
    exact hroot ⟨ y, ha⟩
  by_cases hstop : ∃ n, ¬ ∃ b, Step W Y (f n) b
  · let N := Nat.find hstop
    have hNstop : ¬ ∃ b, Step W Y (f N) b := Nat.find_spec hstop
    have hbefore : forall k, k < N -> ∃ b, Step W Y (f k) b := by
      intro k hk
      by_contra hkstop
      have hle := Nat.find_min' hstop hkstop
      omega
    have hNpos : 0 < N := by
      by_contra hN
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      apply hNstop
      rw [hN0, hf0]
      rcases hforward with ⟨ y, hy⟩
      exact ⟨ .inr y, hy⟩
    have hsteps : forall k, k < N -> Step W Y (f k) (f (k + 1)) := by
      intro k hk
      change Step W Y (f k) (nextPort W Y (f k))
      exact step_nextPort_of_exists (hbefore k hk)
    have hne := chain_ne_of_lt (step_biUnique hW hY).1 hsteps hrootRange
    let T : FiniteTraversal W Y root := {
      lastIndex := N
      positive := hNpos
      port := fun i => f i.1
      starts := hf0
      steps := by
        intro i
        exact hsteps i.1 i.2
      injective := by
        intro i j hij
        apply Fin.ext
        by_contra hneij
        rcases lt_or_gt_of_ne hneij with hij' | hji'
        · exact hne i.1 j.1 hij' (Nat.le_of_lt_succ j.2) hij
        · exact hne j.1 i.1 hji' (Nat.le_of_lt_succ i.2) hij.symm
      root_unmatched := hroot
      terminal := hNstop }
    exact ⟨ .finite T⟩
  · have hall : forall n, ∃ b, Step W Y (f n) b := by
      intro n
      by_contra hn
      exact hstop ⟨ n, hn⟩
    have hsteps : forall n, Step W Y (f n) (f (n + 1)) := by
      intro n
      change Step W Y (f n) (nextPort W Y (f n))
      exact step_nextPort_of_exists (hall n)
    have hinj := Alternating.injective_chain_of_leftUnique_of_root_not_range
      (step_biUnique hW hY).1 hsteps hrootRange
    exact ⟨ .infinite {
      port := f
      starts := hf0
      steps := hsteps
      injective := hinj
      root_unmatched := hroot }⟩

/-- The source endpoint of the bipartite conversion has only its sending
copy.  Hence an actual forward warp edge from a source outside the reference
warp starts a genuine symmetric-difference component; no artificial
identity edge can enter it from the reference matching. -/
theorem exists_traversal_of_source {W Y : Set Gamma.DPath}
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {root y : V} (hsource : root ∈ Gamma.source)
    (hrootY : root ∉ Gamma.vertexSet Y)
    (hforward : (root, y) ∈ familyEdges W) :
    Nonempty (Traversal W Y root) := by
  apply exists_traversal hW hY root
  · refine ⟨y, matchingEdge_actual hforward, ?_⟩
    rintro (hy | hy)
    · apply hrootY
      rw [DWeb.mem_vertexSet]
      simp only [familyEdges, Set.mem_iUnion] at hy
      rcases hy with ⟨p, hpY, hp⟩
      exact ⟨p, hpY, (p.edgeSet_subset_support_prod hp).1⟩
    · exact hy.2.2.1 hsource
  · rintro ⟨z, hz, _hzW⟩
    rcases hz with hz | hz
    · apply hrootY
      rw [DWeb.mem_vertexSet]
      simp only [familyEdges, Set.mem_iUnion] at hz
      rcases hz with ⟨p, hpY, hp⟩
      exact ⟨p, hpY, (p.edgeSet_subset_support_prod hp).1⟩
    · exact hz.2.2.1 hsource

/-- A port is covered by a reference step of the traversal. -/
def FiniteTraversal.ReferenceCovered {W Y : Set Gamma.DPath} {root : V}
    (T : FiniteTraversal W Y root) (a : Port V) : Prop :=
  ∃ i : Fin T.lastIndex,
    (∃ x y, T.port i.castSucc = .inr y ∧ T.port i.succ = .inl x ∧
      Exclusive Y W x y) ∧
    (a = T.port i.castSucc ∨ a = T.port i.succ)

def InfiniteTraversal.ReferenceCovered {W Y : Set Gamma.DPath} {root : V}
    (T : InfiniteTraversal W Y root) (a : Port V) : Prop :=
  ∃ i,
    (∃ x y, T.port i = .inr y ∧ T.port (i + 1) = .inl x ∧
      Exclusive Y W x y) ∧
    (a = T.port i ∨ a = T.port (i + 1))

/-- Every reference-only incidence at either endpoint of a forward step in
a finite maximal component is represented by an adjacent backward step. -/
theorem FiniteTraversal.forward_contact_covered
    {W Y : Set Gamma.DPath} {root : V}
    (T : FiniteTraversal W Y root) (i : Fin T.lastIndex)
    {x y : V} (hleft : T.port i.castSucc = .inl x)
    (hright : T.port i.succ = .inr y) :
    ((∃ z, Exclusive Y W x z) -> T.ReferenceCovered (.inl x)) ∧
      ((∃ z, Exclusive Y W z y) -> T.ReferenceCovered (.inr y)) := by
  constructor
  · rintro ⟨ z, hz⟩
    by_cases hi0 : i.1 = 0
    · have hip : i.castSucc = (0 : Fin (T.lastIndex + 1)) := Fin.ext hi0
      have hxr : x = root := Sum.inl.inj (hleft.symm.trans (hip ▸ T.starts))
      subst x
      exact False.elim (T.root_unmatched ⟨ z, hz⟩)
    · let j : Fin T.lastIndex := ⟨ i.1 - 1, by omega⟩
      have hjsucc : j.succ = i.castSucc := by
        apply Fin.ext
        change i.1 - 1 + 1 = i.1
        omega
      have hj := T.steps j
      rw [hjsucc, hleft] at hj
      rcases hprev : T.port j.castSucc with a | b
      · rw [hprev] at hj
        exact False.elim hj
      · rw [hprev] at hj
        have htarget : T.port j.succ = .inl x := by
          rw [hjsucc]
          exact hleft
        refine ⟨j, ⟨x, b, hprev, htarget, hj⟩, Or.inr htarget.symm⟩
  · rintro ⟨ z, hz⟩
    by_cases hilast : i.1 + 1 = T.lastIndex
    · have hisucc : i.succ =
          (⟨ T.lastIndex, Nat.lt_succ_self _⟩ : Fin (T.lastIndex + 1)) := by
        apply Fin.ext
        exact hilast
      apply False.elim
      apply T.terminal
      refine ⟨ .inl z, ?_⟩
      rw [← hisucc, hright]
      exact hz
    · let j : Fin T.lastIndex := ⟨ i.1 + 1, by omega⟩
      have hjcast : j.castSucc = i.succ := by
        apply Fin.ext
        rfl
      have hj := T.steps j
      rw [hjcast, hright] at hj
      rcases hnext : T.port j.succ with a | b
      · rw [hnext] at hj
        have hsource : T.port j.castSucc = .inr y := by
          rw [hjcast]
          exact hright
        refine ⟨j, ⟨a, y, hsource, hnext, hj⟩, Or.inl hsource.symm⟩
      · rw [hnext] at hj
        exact False.elim hj

/-- Infinite analogue of `FiniteTraversal.forward_contact_covered`. -/
theorem InfiniteTraversal.forward_contact_covered
    {W Y : Set Gamma.DPath} {root : V}
    (T : InfiniteTraversal W Y root) (i : Nat)
    {x y : V} (hleft : T.port i = .inl x)
    (hright : T.port (i + 1) = .inr y) :
    ((∃ z, Exclusive Y W x z) -> T.ReferenceCovered (.inl x)) ∧
      ((∃ z, Exclusive Y W z y) -> T.ReferenceCovered (.inr y)) := by
  constructor
  · rintro ⟨ z, hz⟩
    cases i with
    | zero =>
        have hxr : x = root := Sum.inl.inj (hleft.symm.trans T.starts)
        subst x
        exact False.elim (T.root_unmatched ⟨ z, hz⟩)
    | succ i =>
        have hj := T.steps i
        rw [hleft] at hj
        rcases hprev : T.port i with a | b
        · rw [hprev] at hj
          exact False.elim hj
        · rw [hprev] at hj
          refine ⟨i, ⟨x, b, hprev, hleft, hj⟩, Or.inr hleft.symm⟩
  · rintro ⟨ z, hz⟩
    have hj := T.steps (i + 1)
    rw [hright] at hj
    rcases hnext : T.port (i + 1 + 1) with a | b
    · rw [hnext] at hj
      refine ⟨ i + 1, ⟨ a, y, hright, hnext, hj⟩,
        Or.inl hright.symm⟩
    · rw [hnext] at hj
      exact False.elim hj

end TwoWarpMatchingTraversal
end Erdos599
