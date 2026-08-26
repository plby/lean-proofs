/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.QuadraticRootAlgebra

/-!
# Quadratic root sets modulo a prime

The domain lemma is converted into the finite statement actually used by a
CRT argument: a monic quadratic has at most two roots in `ZMod p` for prime
`p`.
-/

namespace Erdos822

/-- Roots in a prime residue ring of `T^2 + u = v*T`. -/
def quadraticRootsZMod (n : ℕ) [NeZero n]
    (u v : ZMod n) : Finset (ZMod n) :=
  Finset.univ.filter fun t => t ^ 2 + u = v * t

@[simp]
theorem mem_quadraticRootsZMod_iff
    {n : ℕ} [NeZero n] {u v t : ZMod n} :
    t ∈ quadraticRootsZMod n u v ↔ t ^ 2 + u = v * t := by
  simp [quadraticRootsZMod]

/-- Once one root is fixed over a domain, every other root is either that
root or its complementary root `v-a`. -/
theorem quadraticRootsZMod_subset_pair_of_mem
    {p : ℕ} [NeZero p] (hp : p.Prime) {u v a : ZMod p}
    (ha : a ∈ quadraticRootsZMod p u v) :
    quadraticRootsZMod p u v ⊆ ({a, v - a} : Finset (ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro b hb
  have ha' : a ^ 2 + u = v * a := mem_quadraticRootsZMod_iff.mp ha
  have hb' : b ^ 2 + u = v * b := mem_quadraticRootsZMod_iff.mp hb
  rcases quadratic_roots_eq_or_add_eq ha' hb' with hab | hadd
  · simp [hab]
  · have hbEq : b = v - a := by
      apply eq_sub_of_add_eq'
      simpa [add_comm] using hadd
    simp [hbEq]

/-- A monic quadratic has at most two roots modulo a prime. -/
theorem quadraticRootsZMod_card_le_two
    {p : ℕ} [NeZero p] (hp : p.Prime) (u v : ZMod p) :
    (quadraticRootsZMod p u v).card ≤ 2 := by
  by_cases hne : (quadraticRootsZMod p u v).Nonempty
  · obtain ⟨a, ha⟩ := hne
    calc
      (quadraticRootsZMod p u v).card ≤
          ({a, v - a} : Finset (ZMod p)).card :=
        Finset.card_le_card (quadraticRootsZMod_subset_pair_of_mem hp ha)
      _ ≤ ({v - a} : Finset (ZMod p)).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

end Erdos822
