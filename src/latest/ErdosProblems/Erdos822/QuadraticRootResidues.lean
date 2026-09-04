/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.QuadraticRootsPrime

/-!
# Natural residue representatives of quadratic roots

The medium-range variables are natural residue classes.  This file transfers
the prime-field two-root theorem to representatives in `[0,p)`.
-/

namespace Erdos822

/-- Natural representatives of roots of `T^2 + u = v*T` modulo `n`. -/
def quadraticRootResidues (n u v : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun t => t ^ 2 + u ≡ v * t [MOD n]

@[simp]
theorem mem_quadraticRootResidues_iff {n u v t : ℕ} :
    t ∈ quadraticRootResidues n u v ↔
      t < n ∧ t ^ 2 + u ≡ v * t [MOD n] := by
  simp [quadraticRootResidues]

/-- Casting a natural root representative gives a root in `ZMod p`. -/
theorem natCast_mem_quadraticRootsZMod_of_mem
    {p u v t : ℕ} [NeZero p]
    (ht : t ∈ quadraticRootResidues p u v) :
    (t : ZMod p) ∈ quadraticRootsZMod p (u : ZMod p) (v : ZMod p) := by
  rw [mem_quadraticRootsZMod_iff]
  have hmod := (mem_quadraticRootResidues_iff.mp ht).2
  have hz : ((t ^ 2 + u : ℕ) : ZMod p) = ((v * t : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul] using hz

/-- Casting is injective on the chosen representatives. -/
theorem natCast_injOn_quadraticRootResidues
    {p u v : ℕ} [NeZero p] :
    Set.InjOn (fun t : ℕ => (t : ZMod p))
      (quadraticRootResidues p u v) := by
  intro a ha b hb hab
  have hmod : a ≡ b [MOD p] :=
    (ZMod.natCast_eq_natCast_iff a b p).mp hab
  exact hmod.eq_of_lt_of_lt
    (mem_quadraticRootResidues_iff.mp ha).1
    (mem_quadraticRootResidues_iff.mp hb).1

/-- The natural residue representatives inherit the prime-modulus
two-root bound. -/
theorem quadraticRootResidues_card_le_two_of_prime
    {p : ℕ} (hp : p.Prime) (u v : ℕ) :
    (quadraticRootResidues p u v).card ≤ 2 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hinj := natCast_injOn_quadraticRootResidues (p := p) (u := u) (v := v)
  have hsubset :
      (quadraticRootResidues p u v).image (fun t : ℕ => (t : ZMod p)) ⊆
        quadraticRootsZMod p (u : ZMod p) (v : ZMod p) := by
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨t, ht, rfl⟩ := ha
    exact natCast_mem_quadraticRootsZMod_of_mem ht
  calc
    (quadraticRootResidues p u v).card =
        ((quadraticRootResidues p u v).image
          (fun t : ℕ => (t : ZMod p))).card := by
      rw [Finset.card_image_of_injOn hinj]
    _ ≤ (quadraticRootsZMod p (u : ZMod p) (v : ZMod p)).card :=
      Finset.card_le_card hsubset
    _ ≤ 2 := quadraticRootsZMod_card_le_two hp _ _

end Erdos822
