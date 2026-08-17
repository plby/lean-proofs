/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.FiniteProbability
import ErdosProblems.Erdos543.Rank

/-!
# Exact probabilities of finite linear systems

This file packages the finite-linear-algebra calculation used in the
factorial-moment argument for Erdős Problem 543.  If a matrix over the prime
field `ZMod p` has rank `d`, every nonempty affine fiber has `p ^ (k - d)`
points.  Consequently a uniformly random vector in `(ZMod p)^k` belongs to
such a fiber with probability exactly `1 / p ^ d`.  A matrix of full row rank
is surjective, so in that case every right-hand side gives a nonempty fiber.
-/

namespace Erdos543

open FiniteProbability

noncomputable section

attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]

local instance : NeZero p :=
  ⟨Nat.Prime.ne_zero (show p.Prime from Fact.out)⟩

/-! ## Consistency and full row rank -/

section GeneralIndices

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A matrix whose rank is the dimension of its codomain defines a
surjective linear map. -/
theorem mulVecLin_surjective_of_rank_eq_card_height
    (M : Matrix m n (ZMod p))
    (hrank : M.rank = Fintype.card m) :
    Function.Surjective M.mulVecLin := by
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank, hrank, Module.finrank_fintype_fun_eq_card]

/-- Full row rank makes every right-hand side consistent. -/
theorem rhs_mem_range_of_rank_eq_card_height
    (M : Matrix m n (ZMod p))
    (hrank : M.rank = Fintype.card m) (y : m → ZMod p) :
    y ∈ Set.range M.mulVecLin :=
  mulVecLin_surjective_of_rank_eq_card_height M hrank y

/-- Any two consistent affine systems for the same matrix have equally many
solutions. -/
theorem card_matrixFiber_eq_of_consistent
    (M : Matrix m n (ZMod p)) {y z : m → ZMod p}
    (hy : y ∈ Set.range M.mulVecLin) (hz : z ∈ Set.range M.mulVecLin) :
    (matrixFiber M y).card = (matrixFiber M z).card := by
  rw [card_matrixFiber M hy, card_matrixFiber M hz]

end GeneralIndices

section FiniteMatrices

variable {r k d : ℕ}

/-- Finite event that the random column vector `x` solves `M x = y`. -/
def matrixSystemEvent (M : Matrix (Fin r) (Fin k) (ZMod p))
    (y : Fin r → ZMod p) : Set (Fin k → ZMod p) :=
  {x | M.mulVec x = y}

@[simp] theorem mem_matrixSystemEvent
    (M : Matrix (Fin r) (Fin k) (ZMod p)) (y : Fin r → ZMod p)
    (x : Fin k → ZMod p) :
    x ∈ matrixSystemEvent M y ↔ M.mulVec x = y :=
  Iff.rfl

/-- The event cardinality is the cardinality of the corresponding matrix
fiber. -/
theorem card_filter_matrixSystemEvent
    (M : Matrix (Fin r) (Fin k) (ZMod p)) (y : Fin r → ZMod p) :
    (Finset.univ.filter fun x ↦ x ∈ matrixSystemEvent M y).card =
      (matrixFiber M y).card := by
  classical
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_matrixFiber, mem_matrixSystemEvent]

/-- A consistent rank-`d` system in `k` variables has exactly
`p ^ (k - d)` solutions. -/
theorem card_matrixFiber_of_rank_eq
    (M : Matrix (Fin r) (Fin k) (ZMod p)) {y : Fin r → ZMod p}
    (hrank : M.rank = d) (hy : y ∈ Set.range M.mulVecLin) :
    (matrixFiber M y).card = p ^ (k - d) := by
  simpa [hrank] using card_matrixFiber M hy

/-- A full-row-rank matrix is surjective. -/
theorem mulVecLin_surjective_of_full_row_rank
    (M : Matrix (Fin r) (Fin k) (ZMod p)) (hrank : M.rank = r) :
    Function.Surjective M.mulVecLin := by
  apply mulVecLin_surjective_of_rank_eq_card_height M
  simpa using hrank

/-- Every right-hand side of a full-row-rank system is consistent. -/
theorem rhs_mem_range_of_full_row_rank
    (M : Matrix (Fin r) (Fin k) (ZMod p)) (hrank : M.rank = r)
    (y : Fin r → ZMod p) :
    y ∈ Set.range M.mulVecLin :=
  mulVecLin_surjective_of_full_row_rank M hrank y

/-- A full-row-rank system in `k` variables has exactly `p ^ (k - r)`
solutions for every right-hand side. -/
theorem card_matrixFiber_of_full_row_rank
    (M : Matrix (Fin r) (Fin k) (ZMod p)) (hrank : M.rank = r)
    (y : Fin r → ZMod p) :
    (matrixFiber M y).card = p ^ (k - r) :=
  card_matrixFiber_of_rank_eq M hrank
    (rhs_mem_range_of_full_row_rank M hrank y)

/-! ## Exact finite-uniform probabilities -/

/-- A convenient real-valued form of cancellation of powers. -/
private theorem pow_sub_div_pow_eq_inv_pow (hdk : d ≤ k) :
    (p : ℝ) ^ (k - d) / (p : ℝ) ^ k =
      (((p : ℝ) ^ d)⁻¹) := by
  have hp : (p : ℝ) ≠ 0 := by
    exact_mod_cast Nat.Prime.ne_zero (show p.Prime from Fact.out)
  rw [show k = (k - d) + d by omega, pow_add]
  field_simp
  congr 1
  omega

/-- The exact probability of any consistent rank-`d` affine system is
`p⁻ᵈ`. -/
theorem prob_matrixSystemEvent_of_rank_eq
    (M : Matrix (Fin r) (Fin k) (ZMod p)) {y : Fin r → ZMod p}
    (hrank : M.rank = d) (hy : y ∈ Set.range M.mulVecLin) :
    prob (matrixSystemEvent M y) = (((p : ℝ) ^ d)⁻¹) := by
  have hdk : d ≤ k := by
    rw [← hrank]
    exact Matrix.rank_le_width M
  rw [prob, card_filter_matrixSystemEvent,
    card_matrixFiber_of_rank_eq M hrank hy]
  simp only [Fintype.card_pi, ZMod.card, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, Nat.cast_pow]
  exact pow_sub_div_pow_eq_inv_pow (p := p) (d := d) (k := k) hdk

/-- All consistent right-hand sides for a fixed matrix have the same exact
finite-uniform probability. -/
theorem prob_matrixSystemEvent_eq_of_consistent
    (M : Matrix (Fin r) (Fin k) (ZMod p)) {y z : Fin r → ZMod p}
    (hy : y ∈ Set.range M.mulVecLin) (hz : z ∈ Set.range M.mulVecLin) :
    prob (matrixSystemEvent M y) = prob (matrixSystemEvent M z) := by
  rw [prob, prob, card_filter_matrixSystemEvent,
    card_filter_matrixSystemEvent, card_matrixFiber_eq_of_consistent M hy hz]

/-- For a full-row-rank system, every prescribed right-hand side occurs with
probability exactly `p⁻ʳ`. -/
theorem prob_matrixSystemEvent_of_full_row_rank
    (M : Matrix (Fin r) (Fin k) (ZMod p)) (hrank : M.rank = r)
    (y : Fin r → ZMod p) :
    prob (matrixSystemEvent M y) = (((p : ℝ) ^ r)⁻¹) :=
  prob_matrixSystemEvent_of_rank_eq M hrank
    (rhs_mem_range_of_full_row_rank M hrank y)

end FiniteMatrices

end

end Erdos543
