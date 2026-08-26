/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.GraphPaths
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# An elementary path-or-high-degree bound

This supplies the connected-column ingredient of the qualitative grill
bound in `tex/73.tex`. It uses finite closed walk balls, not a spanning
tree with a maximum number of leaves.
-/

namespace Erdos73

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The closed walk ball of radius `n`, built by adjoining neighbors. -/
def walkBall (root : V) : ℕ → Finset V
  | 0 => {root}
  | n + 1 => walkBall root n ∪ (walkBall root n).biUnion (fun v ↦ G.neighborFinset v)

theorem walkBall_mono (root : V) : Monotone (walkBall G root) :=
  monotone_nat_of_le_succ fun _ ↦ Finset.subset_union_left

theorem adj_mem_walkBall_succ (root : V) {u v : V} {n : ℕ}
    (hu : u ∈ walkBall G root n) (huv : G.Adj u v) :
    v ∈ walkBall G root (n + 1) := by
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
    ⟨u, hu, (G.mem_neighborFinset _ _).mpr huv⟩))

theorem walk_endpoint_mem_walkBall (root : V) {u v : V} (P : G.Walk u v)
    (n : ℕ) (hu : u ∈ walkBall G root n) :
    v ∈ walkBall G root (n + P.length) := by
  induction P generalizing n with
  | nil => simpa using hu
  | @cons u w v huw P ih =>
    have hw := adj_mem_walkBall_succ G root hu huw
    simpa only [SimpleGraph.Walk.length_cons, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using ih (n + 1) hw

theorem walk_endpoint_mem_walkBall_length {u v : V} (P : G.Walk u v) :
    v ∈ walkBall G u P.length := by
  simpa using walk_endpoint_mem_walkBall G u P 0 (by simp [walkBall])

theorem walkBall_card_le (root : V) (d : ℕ)
    (hdeg : ∀ v, G.degree v ≤ d) (n : ℕ) :
    (walkBall G root n).card ≤ (d + 1) ^ n := by
  induction n with
  | zero => simp [walkBall]
  | succ n ih =>
    let S := walkBall G root n
    have hN : (S.biUnion (fun v ↦ G.neighborFinset v)).card ≤ S.card * d := by
      apply le_trans Finset.card_biUnion_le
      calc
        ∑ v ∈ S, (G.neighborFinset v).card ≤ ∑ _v ∈ S, d :=
          Finset.sum_le_sum fun v _ ↦ hdeg v
        _ = S.card * d := by simp
    calc
      (walkBall G root (n + 1)).card ≤ S.card + (S.biUnion (fun v ↦ G.neighborFinset v)).card :=
        Finset.card_union_le _ _
      _ ≤ S.card + S.card * d := Nat.add_le_add_left hN _
      _ = S.card * (d + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      _ ≤ (d + 1) ^ n * (d + 1) := Nat.mul_le_mul_right _ ih
      _ = (d + 1) ^ (n + 1) := (pow_succ _ _).symm

/-- If all simple paths have bounded length and all degrees are bounded,
a connected graph has a uniform finite order bound. -/
theorem card_le_pow_of_connected_degree_path_bound
    (hconn : G.Connected) (d r : ℕ)
    (hdeg : ∀ v, G.degree v ≤ d)
    (hpath : ∀ {u v : V} (P : G.Walk u v), P.IsPath → P.length ≤ r) :
    Fintype.card V ≤ (d + 1) ^ r := by
  let root : V := Classical.choice hconn.nonempty
  have hfull : walkBall G root r = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro v
    obtain ⟨W⟩ := hconn.preconnected root v
    let P := W.toPath
    exact walkBall_mono G root (hpath P.val P.property)
      (walk_endpoint_mem_walkBall_length G P.val)
  simpa [hfull] using walkBall_card_le G root d hdeg r

/-- A sufficiently large connected graph has either a long ordinary
simple path or a vertex with more than the prescribed degree bound. -/
theorem exists_longPath_or_large_degree
    (hconn : G.Connected) (d r : ℕ)
    (hsize : (d + 1) ^ r < Fintype.card V) :
    (∃ u v : V, ∃ P : G.Walk u v, P.IsPath ∧ r < P.length) ∨
      ∃ v, d < G.degree v := by
  by_cases hdeg : ∀ v, G.degree v ≤ d
  · left
    by_contra h
    have hpath {u v : V} (P : G.Walk u v) (hP : P.IsPath) : P.length ≤ r := by
      by_contra hlen
      exact h ⟨u, v, P, hP, lt_of_not_ge hlen⟩
    exact (card_le_pow_of_connected_degree_path_bound G hconn d r hdeg hpath).not_gt hsize
  · right
    push Not at hdeg
    exact hdeg

end
end Erdos73
