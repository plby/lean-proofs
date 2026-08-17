/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos752.Erdos752Parent
import Mathlib.Tactic

/-!
# Rooted branch selection for Erdős Problem 752

This file isolates the finite rooted-tree argument used to close a long path
in two consecutive breadth-first layers.  A family of root paths ending at a
common depth has a deepest common level.  At the following level the endpoints
split into at least two branches, so one branch contains at most half of the
endpoints.  The complementary branch therefore contains at least half.

The final lemmas package the equal-length detours supplied by coherent
geodesic root paths.  Keeping this argument separate makes the later cycle
assembly independent of the representation chosen for the breadth-first tree.
-/

open Function Set SimpleGraph

namespace Erdos752

noncomputable section

attribute [local instance] Classical.propDecidable

universe u w

variable {V : Type u}

/-! ## A small fiber of a nonconstant finite partition -/

/--
If a map is nonconstant on a finite set, one of its nonempty fibers contains
at most half the set.  The complement of that fiber consequently contains at
least half.  This is the exact counting statement needed for child branches
of a rooted tree.
-/
theorem exists_small_fiber_of_nonconstant {α : Type u} {β : Type w}
    (S : Finset α) (f : α → β)
    (hnconst : ∃ x ∈ S, ∃ y ∈ S, f x ≠ f y) :
    ∃ c : β, ∃ A B : Finset α,
      A.Nonempty ∧ A ⊆ S ∧ B = S \ A ∧
      2 * A.card ≤ S.card ∧ S.card ≤ 2 * B.card ∧
      (∀ x ∈ A, f x = c) ∧ (∀ y ∈ B, f y ≠ c) := by
  classical
  obtain ⟨x, hxS, y, hyS, hxy⟩ := hnconst
  let X := S.filter fun z ↦ f z = f x
  let Y := S.filter fun z ↦ f z = f y
  have hxX : x ∈ X := by simp [X, hxS]
  have hyY : y ∈ Y := by simp [Y, hyS]
  have hXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    have hzx : f z = f x := (Finset.mem_filter.mp hzX).2
    have hzy : f z = f y := (Finset.mem_filter.mp hzY).2
    exact hxy (hzx.symm.trans hzy)
  have hunion : X ∪ Y ⊆ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzY
    · exact (Finset.mem_filter.mp hzX).1
    · exact (Finset.mem_filter.mp hzY).1
  have hsum : X.card + Y.card ≤ S.card := by
    rw [← Finset.card_union_of_disjoint hXY]
    exact Finset.card_le_card hunion
  by_cases hsmall : X.card ≤ Y.card
  · refine ⟨f x, X, S \ X, ⟨x, hxX⟩, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact (Finset.mem_filter.mp hz).1
    · omega
    · have hcard : (S \ X).card = S.card - X.card := by
        rw [Finset.card_sdiff_of_subset (by
          intro z hz
          exact (Finset.mem_filter.mp hz).1 : X ⊆ S)]
      omega
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z hz
      have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
      have hzX : z ∉ X := (Finset.mem_sdiff.mp hz).2
      simpa [X, hzS] using hzX
  · have hsmall' : Y.card ≤ X.card := Nat.le_of_lt (Nat.lt_of_not_ge hsmall)
    refine ⟨f y, Y, S \ Y, ⟨y, hyY⟩, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact (Finset.mem_filter.mp hz).1
    · omega
    · have hcard : (S \ Y).card = S.card - Y.card := by
        rw [Finset.card_sdiff_of_subset (by
          intro z hz
          exact (Finset.mem_filter.mp hz).1 : Y ⊆ S)]
      omega
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z hz
      have hzS : z ∈ S := (Finset.mem_sdiff.mp hz).1
      have hzY : z ∉ Y := (Finset.mem_sdiff.mp hz).2
      simpa [Y, hzS] using hzY

/-! ## Deepest common ancestors -/

/-- The root paths in `p` agree at depth `d`. -/
def RootPathsAgreeAt {G : SimpleGraph V} {root : V} (S : Finset V)
    (p : ∀ x : V, G.Walk root x) (d : ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, (p x).getVert d = (p y).getVert d

/--
For at least two endpoints at common path depth `i`, there is a deepest
common level `j < i`.  At level `j+1`, a nonempty child branch `A` contains
at most half the endpoints, while its complement `B` contains at least half.

No graph-theoretic uniqueness is needed for this selection step: it only uses
the chosen root paths.  Prefix coherence is used later to prove that paths in
different selected branches have disjoint tails.
-/
theorem exists_deepest_common_branch {G : SimpleGraph V} {root : V}
    (S : Finset V) (hS : 2 ≤ S.card) (i : ℕ)
    (p : ∀ x : V, G.Walk root x)
    (hpLength : ∀ x ∈ S, (p x).length = i) :
    ∃ j < i, ∃ z c : V, ∃ A B : Finset V,
      A.Nonempty ∧ A ⊆ S ∧ B = S \ A ∧
      2 * A.card ≤ S.card ∧ S.card ≤ 2 * B.card ∧
      RootPathsAgreeAt S p j ∧
      (∀ x ∈ S, (p x).getVert j = z) ∧
      (∀ x ∈ A, (p x).getVert (j + 1) = c) ∧
      (∀ y ∈ B, (p y).getVert (j + 1) ≠ c) := by
  classical
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by omega) hS)
  let C : Finset ℕ := (Finset.range (i + 1)).filter (RootPathsAgreeAt S p)
  have hzero : 0 ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_range, Nat.zero_lt_succ, true_and]
    intro x hx y hy
    simp
  have hC : C.Nonempty := ⟨0, hzero⟩
  let j : ℕ := C.max' hC
  have hjC : j ∈ C := C.max'_mem hC
  have hjle : j ≤ i := by
    have := (Finset.mem_filter.mp hjC).1
    simp only [Finset.mem_range] at this
    omega
  have hnoti : ¬ RootPathsAgreeAt S p i := by
    obtain ⟨x, hxS, y, hyS, hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    intro hagree
    have hget := hagree x hxS y hyS
    have hxend : (p x).getVert i = x := by
      rw [← hpLength x hxS]
      simp
    have hyend : (p y).getVert i = y := by
      rw [← hpLength y hyS]
      simp
    exact hxy (hxend.symm.trans (hget.trans hyend))
  have hjagree : RootPathsAgreeAt S p j := (Finset.mem_filter.mp hjC).2
  have hjlt : j < i := by
    exact lt_of_le_of_ne hjle (fun h ↦ hnoti (h ▸ hjagree))
  have hnotnext : ¬ RootPathsAgreeAt S p (j + 1) := by
    intro hnext
    have hjnextRange : j + 1 ∈ Finset.range (i + 1) := by
      simp only [Finset.mem_range]
      omega
    have hjnextC : j + 1 ∈ C := Finset.mem_filter.mpr ⟨hjnextRange, hnext⟩
    have := C.le_max' (j + 1) hjnextC
    omega
  have hnconst : ∃ x ∈ S, ∃ y ∈ S,
      (p x).getVert (j + 1) ≠ (p y).getVert (j + 1) := by
    rw [RootPathsAgreeAt] at hnotnext
    push_neg at hnotnext
    obtain ⟨x, hx, y, hy, hxy⟩ := hnotnext
    exact ⟨x, hx, y, hy, hxy⟩
  let f : V → V := fun x ↦ (p x).getVert (j + 1)
  have hnconst' : ∃ x ∈ S, ∃ y ∈ S, f x ≠ f y := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hnconst
    exact ⟨x, hx, y, hy, by simpa [f] using hxy⟩
  obtain ⟨c, A, B, hAne, hAS, hB, hAhalf, hBhalf, hAf, hBf⟩ :=
    exists_small_fiber_of_nonconstant S f hnconst'
  obtain ⟨x₀, hx₀⟩ := hSnonempty
  let z := (p x₀).getVert j
  refine ⟨j, hjlt, z, c, A, B, hAne, hAS, hB, hAhalf, hBhalf,
    hjagree, ?_, ?_, ?_⟩
  · intro x hxS
    exact hjagree x hxS x₀ hx₀
  · intro x hxA
    have hxS : x ∈ S := hAS hxA
    simpa [f] using hAf x hxA
  · intro y hyB
    have hyS : y ∈ S := by
      rw [hB] at hyB
      exact (Finset.mem_sdiff.mp hyB).1
    simpa [f] using hBf y hyB

/-! ## Canonical BFS-tree wrapper -/

/--
Canonical BFS parent walks turn the abstract deepest-branch selection into a
uniform family of actual detours.  This is the complete rooted-tree output
needed by the long-path cycle assembly: `A` is a nonempty branch of size at
most half of `S`, `B` is its complement, and one fixed `a ∈ A` has a simple
detour of length `2 * (i-j)` to every `b ∈ B`, with all internal vertices
strictly below layer `i`.
-/
theorem exists_bfs_branch_uniform_detours {G : SimpleGraph V}
    (hconn : G.Connected) (root : V) (S : Finset V)
    (hS : 2 ≤ S.card) (i : ℕ)
    (hlevel : ∀ x ∈ S, G.dist root x = i) :
    ∃ j < i, ∃ z : V, ∃ A B : Finset V, ∃ a : V,
      a ∈ A ∧ A.Nonempty ∧ A ⊆ S ∧ B = S \ A ∧
      2 * A.card ≤ S.card ∧ S.card ≤ 2 * B.card ∧
      ∀ b ∈ B, ∃ q : G.Walk a b,
        q.IsPath ∧ q.length = 2 * (i - j) ∧
          ∀ x ∈ q.support, x ≠ a → x ≠ b → G.dist root x < i := by
  classical
  let p : ∀ x : V, G.Walk root x := fun x ↦ bfsParentWalk G hconn root x
  have hpLength : ∀ x ∈ S, (p x).length = i := by
    intro x hx
    change (bfsParentWalk G hconn root x).length = i
    rw [bfsParentWalk_length G hconn root x, hlevel x hx]
  obtain ⟨j, hji, z, c, A, B, hAne, hAS, hB, hAhalf, hBhalf,
      _hjagree, hjcommon, hAchild, hBchild⟩ :=
    exists_deepest_common_branch S hS i p hpLength
  obtain ⟨a, haA⟩ := hAne
  refine ⟨j, hji, z, A, B, a, haA, ⟨a, haA⟩, hAS, hB, hAhalf, hBhalf, ?_⟩
  intro b hbB
  have haS : a ∈ S := hAS haA
  have hbS : b ∈ S := by
    rw [hB] at hbB
    exact (Finset.mem_sdiff.mp hbB).1
  have hsplit : (bfsParentWalk G hconn root a).getVert (j + 1) ≠
      (bfsParentWalk G hconn root b).getVert (j + 1) := by
    intro hab
    have hac : (p a).getVert (j + 1) = c := hAchild a haA
    have hbc : (p b).getVert (j + 1) ≠ c := hBchild b hbB
    exact hbc (by
      rw [← hab]
      simpa [p] using hac)
  exact exists_bfsParent_detour_of_split G hconn root a b z i j
    (hlevel a haS) (hlevel b hbS) hji
    (by simpa [p] using hjcommon a haS)
    (by simpa [p] using hjcommon b hbS) hsplit

end

end Erdos752
