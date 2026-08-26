import ErdosProblems.Erdos486.Skeleton

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A biased-colouring arithmetic skeleton for Erdős Problem 486

This is a formalization-friendly strengthening of the finite arithmetic
block.  The endpoint interval is deterministic.  A later finite-colouring
argument chooses, for each endpoint, a subset of the auxiliary primes; this
file supplies a distinct modulus for every such subset and proves all of the
geometric estimates needed by the global construction.
-/

open scoped BigOperators

namespace Erdos486

/-- The square-root scale used by the biased-colouring block. -/
def biasedRadius (j : ℕ) : ℕ :=
  Nat.sqrt j / 20

/-- There are six auxiliary primes per square-root unit. -/
def biasedK (j : ℕ) : ℕ :=
  6 * biasedRadius j

theorem biasedRadius_pos {j : ℕ} (hj : 400 ≤ j) :
    0 < biasedRadius j := by
  have hsqrt : 20 ≤ Nat.sqrt j := by
    have hsqrt400 : Nat.sqrt 400 = 20 := by norm_num
    rw [← hsqrt400]
    exact Nat.sqrt_le_sqrt hj
  simp only [biasedRadius]
  omega

theorem twenty_mul_biasedRadius_le_sqrt (j : ℕ) :
    20 * biasedRadius j ≤ Nat.sqrt j := by
  simpa [biasedRadius, Nat.mul_comm] using
    Nat.div_mul_le_self (Nat.sqrt j) 20

theorem biased_exponent_add_five_le {j : ℕ} (hj : 400 ≤ j) :
    3 * biasedK j ^ 2 + 2 * biasedK j + 5 ≤ j := by
  have hr : 1 ≤ biasedRadius j := biasedRadius_pos hj
  have htwenty := twenty_mul_biasedRadius_le_sqrt j
  have hsqrt := Nat.sqrt_le j
  simp only [biasedK] at ⊢
  nlinarith

/-- The product of the auxiliary primes is at most one thirty-second of
the dyadic scale. -/
theorem thirtyTwo_mul_biasedProduct_le (j : ℕ) (hj : 400 ≤ j) :
    32 * skeletonProduct (biasedK j) ≤ 2 ^ j := by
  have hP := skeletonProduct_le (biasedK j)
  have hexp := biased_exponent_add_five_le hj
  calc
    32 * skeletonProduct (biasedK j) ≤
        2 ^ 5 * 2 ^ (3 * biasedK j ^ 2 + 2 * biasedK j) :=
      Nat.mul_le_mul (by norm_num) hP
    _ = 2 ^ (5 + (3 * biasedK j ^ 2 + 2 * biasedK j)) :=
      (pow_add 2 5 (3 * biasedK j ^ 2 + 2 * biasedK j)).symm
    _ = 2 ^ (3 * biasedK j ^ 2 + 2 * biasedK j + 5) := by
      congr 1
      omega
    _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hexp

/-- The largest multiple of the prime product not exceeding `2^j`. -/
noncomputable def biasedBase (j : ℕ) : ℕ :=
  skeletonProduct (biasedK j) *
    (2 ^ j / skeletonProduct (biasedK j))

/-- The modulus indexed by a subset of the auxiliary primes. -/
noncomputable def biasedModulus (j : ℕ)
    (S : Finset (Fin (biasedK j))) : ℕ :=
  biasedBase j + skeletonSubsetProduct (biasedK j) S

theorem biasedBase_le (j : ℕ) : biasedBase j ≤ 2 ^ j := by
  simpa [biasedBase, Nat.mul_comm] using
    Nat.div_mul_le_self (2 ^ j) (skeletonProduct (biasedK j))

theorem twoPow_lt_biasedBase_add_product (j : ℕ) :
    2 ^ j < biasedBase j + skeletonProduct (biasedK j) := by
  have hP : 0 < skeletonProduct (biasedK j) := skeletonProduct_pos _
  simpa [biasedBase, Nat.mul_add] using
    Nat.lt_mul_div_succ (2 ^ j) hP

theorem skeletonPrime_dvd_biasedBase (j : ℕ) (i : Fin (biasedK j)) :
    skeletonPrime (biasedK j) i ∣ biasedBase j := by
  exact (skeletonPrime_dvd_product (biasedK j) i).mul_right _

/-- The prime support of a modulus recovers its indexing subset exactly. -/
theorem skeletonPrime_dvd_biasedModulus_iff (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    skeletonPrime (biasedK j) i ∣ biasedModulus j S ↔ i ∈ S := by
  rw [biasedModulus, ← Nat.dvd_add_iff_right
    (skeletonPrime_dvd_biasedBase j i),
    skeletonPrime_dvd_subsetProduct_iff]

theorem biasedModulus_injective (j : ℕ) :
    Function.Injective (biasedModulus j) := by
  intro S T hST
  ext i
  rw [← skeletonPrime_dvd_biasedModulus_iff,
    hST, skeletonPrime_dvd_biasedModulus_iff]

theorem biasedModulus_pos (j : ℕ) (S : Finset (Fin (biasedK j))) :
    0 < biasedModulus j S := by
  unfold biasedModulus
  exact Nat.add_pos_right _ (skeletonSubsetProduct_pos _ _)

/-- Every biased modulus lies in the narrower interval
`[19*2^j/20, 21*2^j/20]` required by the global interface. -/
theorem biasedModulus_bounds {j : ℕ} (hj : 400 ≤ j)
    (S : Finset (Fin (biasedK j))) :
    19 * 2 ^ j ≤ 20 * biasedModulus j S ∧
      20 * biasedModulus j S ≤ 21 * 2 ^ j := by
  have hsmall := thirtyTwo_mul_biasedProduct_le j hj
  have hbaseUpper := biasedBase_le j
  have hbaseLower := twoPow_lt_biasedBase_add_product j
  have hdpos := skeletonSubsetProduct_pos (biasedK j) S
  have hdUpper := skeletonSubsetProduct_le_product (biasedK j) S
  unfold biasedModulus
  constructor <;> omega

/-- The integral radius `2^(j-3)`, so that `2^j = 8 * blockUnit j`
at every relevant scale. -/
def blockUnit (j : ℕ) : ℕ :=
  2 ^ (j - 3)

theorem twoPow_eq_eight_mul_blockUnit {j : ℕ} (hj : 3 ≤ j) :
    2 ^ j = 8 * blockUnit j := by
  rw [blockUnit, show j = (j - 3) + 3 by omega, pow_add]
  norm_num [Nat.mul_comm]

/-- All integers in `[9*2^(j-3), 15*2^(j-3)]`. -/
def biasedEndpoints (j : ℕ) : Finset ℕ :=
  Finset.Icc (9 * blockUnit j) (15 * blockUnit j)

theorem mem_biasedEndpoints_iff {j m : ℕ} :
    m ∈ biasedEndpoints j ↔
      9 * blockUnit j ≤ m ∧ m ≤ 15 * blockUnit j := by
  simp [biasedEndpoints]

theorem biasedEndpoints_card (j : ℕ) :
    (biasedEndpoints j).card = 6 * blockUnit j + 1 := by
  simp [biasedEndpoints]
  omega

theorem biasedEndpoint_bounds {j m : ℕ} (hj : 400 ≤ j)
    (hm : m ∈ biasedEndpoints j) :
    11 * 2 ^ j ≤ 10 * m ∧
      10 * m ≤ 19 * 2 ^ j := by
  have hQ := twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega)
  rw [mem_biasedEndpoints_iff] at hm
  omega

theorem biasedEndpoints_enough {j : ℕ} (hj : 400 ≤ j) :
    3 * 2 ^ j ≤ 8 * (biasedEndpoints j).card := by
  rw [twoPow_eq_eight_mul_blockUnit (show 3 ≤ j by omega),
    biasedEndpoints_card]
  omega

end Erdos486
