import ErdosProblems.Erdos1188.SparsePrimeCapacity
import ErdosProblems.Erdos1188.BinomialBounds

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Quantitative counting for indexed-prime sparse support profiles
-/

namespace Erdos1188

open scoped BigOperators

/-- Sum of the nonzero-residue counts over late coordinates. -/
noncomputable def sparsePrimeExponent (m : ℕ) : ℕ :=
  (Finset.univ.filter fun i : Fin m => sparseSeed ≤ i.val).sum
    (fun i => nthPrime i.val - 1)

/-- The product of all pool-range binomial coefficients dominates an
exponential whose exponent is the total late-coordinate demand. -/
theorem two_pow_sparsePrimeExponent_le_profile_count (m : ℕ) :
    2 ^ sparsePrimeExponent m ≤
      ∏ i : Fin m,
        (Fintype.card (PrimeSparsePool m i)).choose (nthPrime i.val - 1) := by
  classical
  let k : Fin m → ℕ := fun i => nthPrime i.val - 1
  calc
    2 ^ sparsePrimeExponent m =
        ∏ i : Fin m with sparseSeed ≤ i.val, 2 ^ k i := by
      rw [sparsePrimeExponent]
      convert (Finset.prod_pow_eq_pow_sum
        (Finset.univ.filter fun i : Fin m => sparseSeed ≤ i.val) k 2).symm using 1 <;>
        simp [k]
    _ = ∏ i : Fin m, if sparseSeed ≤ i.val then 2 ^ k i else 1 := by
      rw [Finset.prod_filter]
    _ ≤ ∏ i : Fin m,
        (Fintype.card (PrimeSparsePool m i)).choose (k i) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      split_ifs with hi
      · apply two_pow_le_choose_of_two_mul_le
        · have hp := index_add_two_le_nthPrime i.val
          unfold sparseSeed at hi
          dsimp [k]
          omega
        · simpa [k] using primeSparsePool_late_capacity i hi
      · simpa [k, primeSparsePool_early_card i hi] using Nat.choose_self (k i)

/-- Data needed by the closing coordinate are available at every late
dimension. -/
theorem sparseClosing_numeric_data {m : ℕ} (hm : sparseSeed ≤ m) :
    m + 1 ≤ nthPrime m ∧
    nthPrime m - (m + 1) ≤ sparseHeight m * (m - sparseHeight m) := by
  have hlo := index_add_two_le_nthPrime m
  have hcap := twice_nthPrime_sub_one_le_crossCapacity hm
  constructor
  · omega
  · omega

/-- Canonical closing support map for the prime construction. -/
noncomputable def primeSparseClosingFixed (m : ℕ) (hm : sparseSeed ≤ m) :
    ZMod (nthPrime m) → Finset (Fin m) :=
  sparseClosingFixed (sparseHeight_lt hm).le
    (sparseClosing_numeric_data hm).1 (sparseClosing_numeric_data hm).2

/-- Canonical reserved escape values. -/
noncomputable def primeSparseClosingEscape (m : ℕ) (hm : sparseSeed ≤ m) :
    Fin m → ZMod (nthPrime m) :=
  sparseClosingEscape (sparseClosing_numeric_data hm).1
    (sparseClosing_numeric_data hm).2

/-- The canonical closing supports are injective. -/
theorem primeSparseClosingFixed_injective {m : ℕ} (hm : sparseSeed ≤ m) :
    Function.Injective (primeSparseClosingFixed m hm) := by
  unfold primeSparseClosingFixed
  exact sparseClosingFixed_injective (sparseHeight_pos m) (sparseHeight_lt hm)
    (sparseClosing_numeric_data hm).1 (sparseClosing_numeric_data hm).2

/-- They protect every base coordinate. -/
theorem primeSparseClosing_protects {m : ℕ} (hm : sparseSeed ≤ m) :
    ClosingProtects (ZMod (nthPrime m))
      (primeSparseClosingFixed m hm) (primeSparseClosingEscape m hm) := by
  unfold primeSparseClosingFixed primeSparseClosingEscape
  exact sparseClosing_protects (sparseHeight_lt hm).le
    (sparseClosing_numeric_data hm).1 (sparseClosing_numeric_data hm).2

end Erdos1188
