/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import Mathlib.Data.List.Chain

/-!
# The simple-path search tree used by the alternating-path construction

This file isolates a small generic search lemma.  A node of the search tree
is a finite `R`-path, starting at a fixed root, whose projected vertices are
pairwise distinct.  A child is obtained by appending a fresh successor of the
current endpoint.

The usual locally-finite application says that either this tree has a leaf or
it has an infinite branch.  For this particular tree a stronger statement is
available: finite branching is unnecessary.  If there is no leaf, classical
dependent choice can append a fresh successor at every finite stage.  Since
each node remembers all vertices already used, the endpoint sequence of the
resulting branch is injective.  Thus the theorem applies directly to a
two-mode search graph even when it is more convenient to prove local
finiteness only later.
-/

namespace Erdos599
namespace AlternatingSearchTree

open Set

universe u

variable {A : Type u} (R : A → A → Prop) (root : A)

/-- A chronological finite simple `R`-path with prescribed first vertex.
The root itself is not stored in `tail`, so the represented vertex list is
always nonempty. -/
structure RootedSimplePath where
  tail : List A
  nodup : (root :: tail).Nodup
  isChain : (root :: tail).IsChain R

namespace RootedSimplePath

/-- The chronological list of projected vertices of a search node. -/
def vertices (p : RootedSimplePath R root) : List A :=
  root :: p.tail

/-- The current projected vertex of a search node. -/
def endpoint (p : RootedSimplePath R root) : A :=
  p.vertices.getLast (by simp [vertices])

/-- The root-only search node. -/
def nil : RootedSimplePath R root where
  tail := []
  nodup := by simp
  isChain := List.isChain_singleton root

@[simp]
theorem vertices_nil : (nil R root).vertices = [root] :=
  rfl

@[simp]
theorem endpoint_nil : (nil R root).endpoint = root := by
  simp [endpoint, vertices, nil]

theorem endpoint_mem_vertices (p : RootedSimplePath R root) :
    p.endpoint ∈ p.vertices := by
  exact List.getLast_mem _

/-- Append a fresh successor to a finite simple path. -/
def extend (p : RootedSimplePath R root) (x : A)
    (hrel : R p.endpoint x) (hfresh : x ∉ p.vertices) :
    RootedSimplePath R root where
  tail := p.tail ++ [x]
  nodup := by
    change (p.vertices ++ [x]).Nodup
    apply List.nodup_append.2
    refine ⟨p.nodup, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst b
    intro hax
    exact hfresh (hax ▸ ha)
  isChain := by
    change (p.vertices ++ [x]).IsChain R
    apply p.isChain.append (List.isChain_singleton x)
    intro a ha b hb
    have ha' : a = p.endpoint := by
      change (root :: p.tail).getLast? = some a at ha
      rw [List.getLast?_eq_getLast_of_ne_nil (by simp)] at ha
      change a = (root :: p.tail).getLast (by simp)
      exact (Option.some.inj ha).symm
    have hb' : b = x := by simpa using hb.symm
    simpa [ha', hb'] using hrel

@[simp]
theorem vertices_extend (p : RootedSimplePath R root) (x : A)
    (hrel : R p.endpoint x) (hfresh : x ∉ p.vertices) :
    (p.extend (R := R) (root := root) x hrel hfresh).vertices =
      p.vertices ++ [x] := by
  rfl

@[simp]
theorem endpoint_extend (p : RootedSimplePath R root) (x : A)
    (hrel : R p.endpoint x) (hfresh : x ∉ p.vertices) :
    (p.extend (R := R) (root := root) x hrel hfresh).endpoint = x := by
  simp [endpoint, vertices, extend]

/-- A leaf of the simple-path search tree: every successor of its endpoint
has already appeared in the projected path. -/
def IsMaximal (p : RootedSimplePath R root) : Prop :=
  ∀ x, R p.endpoint x → x ∈ p.vertices

/-- Every simple-path search either stops at a finite leaf or produces an
injective infinite `R`-path from the root.

This is the precise search principle needed when a state records its complete
finite projected history.  In a locally finite state graph it is Kőnig's
lemma for the tree of such histories; remembering the history makes the
slightly stronger dependent-choice proof possible. -/
theorem exists_maximal_or_infinite :
    (∃ p : RootedSimplePath R root, p.IsMaximal) ∨
      ∃ f : ℕ → A,
        f 0 = root ∧ Function.Injective f ∧ ∀ n, R (f n) (f (n + 1)) := by
  classical
  by_cases hmax : ∃ p : RootedSimplePath R root, p.IsMaximal
  · exact Or.inl hmax
  · right
    have hfresh : ∀ p : RootedSimplePath R root,
        ∃ x, R p.endpoint x ∧ x ∉ p.vertices := by
      intro p
      have hp : ¬ p.IsMaximal := fun hp ↦ hmax ⟨p, hp⟩
      rw [IsMaximal, Classical.not_forall] at hp
      obtain ⟨x, hx⟩ := hp
      rw [Classical.not_imp] at hx
      exact ⟨x, hx⟩
    let chosen : RootedSimplePath R root → A :=
      fun p ↦ Classical.choose (hfresh p)
    have chosen_spec (p : RootedSimplePath R root) :
        R p.endpoint (chosen p) ∧ chosen p ∉ p.vertices :=
      Classical.choose_spec (hfresh p)
    let next : RootedSimplePath R root → RootedSimplePath R root :=
      fun p ↦ p.extend (R := R) (root := root)
        (chosen p) (chosen_spec p).1 (chosen_spec p).2
    have next_vertices (p : RootedSimplePath R root) :
        (next p).vertices = p.vertices ++ [chosen p] := by
      simp [next]
    have next_endpoint (p : RootedSimplePath R root) :
        (next p).endpoint = chosen p := by
      simp [next]
    let paths : ℕ → RootedSimplePath R root :=
      fun n ↦ Nat.rec (nil R root) (fun _ p ↦ next p) n
    have paths_zero : paths 0 = nil R root := by
      rfl
    have paths_succ (n : ℕ) : paths (n + 1) = next (paths n) := by
      simp [paths]
    let f : ℕ → A := fun n ↦ (paths n).endpoint
    have f_zero : f 0 = root := by
      simp [f, paths_zero]
    have f_rel (n : ℕ) : R (f n) (f (n + 1)) := by
      rw [show f (n + 1) = chosen (paths n) by
        simp only [f, paths_succ, next_endpoint]]
      exact (chosen_spec (paths n)).1
    have f_succ_fresh (n : ℕ) : f (n + 1) ∉ (paths n).vertices := by
      rw [show f (n + 1) = chosen (paths n) by
        simp only [f, paths_succ, next_endpoint]]
      exact (chosen_spec (paths n)).2
    have earlier_mem (n : ℕ) : ∀ i ≤ n, f i ∈ (paths n).vertices := by
      induction n with
      | zero =>
          intro i hi
          have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
          subst i
          exact endpoint_mem_vertices (R := R) (root := root) (paths 0)
      | succ n ih =>
          intro i hi
          rcases Nat.eq_or_lt_of_le hi with rfl | hi
          · exact endpoint_mem_vertices (R := R) (root := root) (paths (n + 1))
          · rw [paths_succ, next_vertices]
            exact List.mem_append_left _ (ih i (Nat.lt_succ_iff.mp hi))
    have f_ne_of_lt {i j : ℕ} (hij : i < j) : f i ≠ f j := by
      cases j with
      | zero => exact (Nat.not_lt_zero _ hij).elim
      | succ n =>
          intro heq
          apply f_succ_fresh n
          rw [← heq]
          exact earlier_mem n i (Nat.lt_succ_iff.mp hij)
    have f_injective : Function.Injective f := by
      intro i j hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (f_ne_of_lt hlt) hij
      · exact (f_ne_of_lt hgt) hij.symm
    exact ⟨f, f_zero, f_injective, f_rel⟩

/-- A useful corollary: if every finite leaf satisfies a designated terminal
predicate, the finite alternative already ends at such a terminal. -/
theorem exists_terminal_or_infinite (terminal : A → Prop)
    (hleaf : ∀ p : RootedSimplePath R root, p.IsMaximal → terminal p.endpoint) :
    (∃ p : RootedSimplePath R root, terminal p.endpoint) ∨
      ∃ f : ℕ → A,
        f 0 = root ∧ Function.Injective f ∧ ∀ n, R (f n) (f (n + 1)) := by
  rcases exists_maximal_or_infinite R root with h | h
  · left
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hleaf p hp⟩
  · exact Or.inr h

end RootedSimplePath

end AlternatingSearchTree
end Erdos599
