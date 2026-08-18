/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic

/-!
# Uniform bounds for finitely many tuples of constants

Several CFP inputs retain a rank only after preprocessing, while the final
theorem must choose all numerical constants beforehand.  This elementary
finite selector replaces five rank-dependent natural constants by five
uniform positive upper bounds without changing the rank-dependent witness.
-/

namespace Erdos186.CFP

open scoped BigOperators

noncomputable section

/-- Five families of natural constants indexed by `Fin D` have simultaneous
positive upper bounds.  The predicate retaining the actual witnesses is
completely arbitrary. -/
theorem exists_uniform_five_bounds
    {D : ℕ} (P : Fin D → ℕ → ℕ → ℕ → ℕ → ℕ → Prop)
    (h : ∀ i, ∃ a b c e f, P i a b c e f) :
    ∃ A B C E F : ℕ,
      0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < E ∧ 0 < F ∧
      ∀ i, ∃ a b c e f,
        P i a b c e f ∧ a ≤ A ∧ b ≤ B ∧ c ≤ C ∧ e ≤ E ∧ f ≤ F := by
  classical
  choose a b c e f hP using h
  refine ⟨1 + ∑ i, a i, 1 + ∑ i, b i, 1 + ∑ i, c i,
    1 + ∑ i, e i, 1 + ∑ i, f i, by omega, by omega, by omega,
    by omega, by omega, ?_⟩
  intro i
  refine ⟨a i, b i, c i, e i, f i, hP i, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ 1)
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ 1)
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ 1)
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ 1)
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans
      (Nat.le_add_left _ 1)

end

end Erdos186.CFP

#print axioms Erdos186.CFP.exists_uniform_five_bounds
