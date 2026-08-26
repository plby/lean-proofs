import ErdosProblems.Erdos486.BiasedCollision
import ErdosProblems.Erdos486.BiasedNumerics

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Union bound for biased-colouring collisions

This file takes the union, in one explicit common period, of the collision
events indexed by all pairs `(S, i)` with `i ∉ S`.  The exact single-event
count from `BiasedCollision` and a finite union bound reduce its normalized
cardinality to the numerical estimate `collision_numeric_le`.
-/

open scoped BigOperators

namespace Erdos486

/-- Representatives in the common period satisfying the collision relation
for one pair `(S, i)`. -/
noncomputable def biasedCollisionResidues (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) : Finset ℕ := by
  classical
  exact (Finset.range (biasedPeriod j)).filter (IsBiasedCollision j S i)

theorem biasedCollisionResidues_card (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    (biasedCollisionResidues j S i).card = biasedCollisionCount j S i := by
  classical
  simp only [biasedCollisionResidues, biasedCollisionCount,
    Nat.count_eq_card_filter_range]

/-- All valid collision indices `(S, i)`, with `S` ranging over the complete
powerset and `i` restricted by `i ∉ S`. -/
def biasedCollisionIndices (j : ℕ) :
    Finset (Finset (Fin (biasedK j)) × Fin (biasedK j)) :=
  ((Finset.univ.powerset).product Finset.univ).filter fun a ↦ a.2 ∉ a.1

@[simp]
theorem mem_biasedCollisionIndices_iff (j : ℕ)
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) :
    (S, i) ∈ biasedCollisionIndices j ↔ i ∉ S := by
  simp [biasedCollisionIndices]

/-- The union of all collisions in one common period. -/
noncomputable def biasedCollisionUnion (j : ℕ) : Finset ℕ := by
  classical
  exact (biasedCollisionIndices j).biUnion fun a ↦
    biasedCollisionResidues j a.1 a.2

/-- Rational normalized cardinality of the full collision union. -/
noncomputable def biasedCollisionUnionRatio (j : ℕ) : ℚ :=
  ((biasedCollisionUnion j).card : ℚ) / (biasedPeriod j : ℚ)

/-- Every collision index contributes exactly reciprocal-prime density. -/
theorem biasedCollisionResidues_ratio_eq {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    ((biasedCollisionResidues j S i).card : ℚ) / (biasedPeriod j : ℚ) =
      1 / (skeletonPrime (biasedK j) i : ℚ) := by
  rw [biasedCollisionResidues_card]
  have hN : (biasedPeriod j : ℚ) ≠ 0 := by
    exact_mod_cast (biasedPeriod_pos j).ne'
  have hp : (skeletonPrime (biasedK j) i : ℚ) ≠ 0 := by
    exact_mod_cast (skeletonPrime_spec (biasedK j) i).1.ne_zero
  rw [div_eq_div_iff hN hp]
  norm_num
  have hcount := skeletonPrime_mul_biasedCollisionCount_eq_period S i hi
  rw [Nat.mul_comm] at hcount
  exact_mod_cast hcount

/-- A prime at any coordinate is bounded below by the common scale
`2^(2k+2)`. -/
theorem twoPow_two_mul_add_two_le_skeletonPrime (j : ℕ)
    (i : Fin (biasedK j)) :
    2 ^ (2 * biasedK j + 2) ≤ skeletonPrime (biasedK j) i := by
  have hexp : biasedK j + 1 ≤ biasedK j + i.val + 1 := by omega
  have hfour : 4 ^ (biasedK j + 1) ≤
      4 ^ (biasedK j + i.val + 1) :=
    Nat.pow_le_pow_right (by norm_num) hexp
  have hprime := (skeletonPrime_spec (biasedK j) i).2.1
  calc
    2 ^ (2 * biasedK j + 2) = 4 ^ (biasedK j + 1) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      congr 2
    _ ≤ 4 ^ (biasedK j + i.val + 1) := hfour
    _ ≤ skeletonPrime (biasedK j) i := hprime.le

/-- Uniform reciprocal bound for every valid pair. -/
theorem biasedCollisionResidues_ratio_le {j : ℕ}
    (S : Finset (Fin (biasedK j))) (i : Fin (biasedK j)) (hi : i ∉ S) :
    ((biasedCollisionResidues j S i).card : ℚ) / (biasedPeriod j : ℚ) ≤
      1 / (2 : ℚ) ^ (2 * biasedK j + 2) := by
  rw [biasedCollisionResidues_ratio_eq S i hi]
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast twoPow_two_mul_add_two_le_skeletonPrime j i

/-- There are at most `2^k k` valid pairs `(S, i)`. -/
theorem biasedCollisionIndices_card_le (j : ℕ) :
    (biasedCollisionIndices j).card ≤ 2 ^ biasedK j * biasedK j := by
  calc
    (biasedCollisionIndices j).card ≤
        ((Finset.univ.powerset : Finset (Finset (Fin (biasedK j)))).product
          (Finset.univ : Finset (Fin (biasedK j)))).card := by
      unfold biasedCollisionIndices
      exact Finset.card_filter_le _ _
    _ = 2 ^ biasedK j * biasedK j := by
      simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_powerset,
        Finset.card_univ, Fintype.card_fin]

/-- The normalized union cardinal is bounded by the number of valid pairs
times the uniform reciprocal-prime bound. -/
theorem biasedCollisionUnionRatio_le_index_bound (j : ℕ) :
    biasedCollisionUnionRatio j ≤
      ((biasedCollisionIndices j).card : ℚ) *
        (1 / (2 : ℚ) ^ (2 * biasedK j + 2)) := by
  classical
  have hcard : (biasedCollisionUnion j).card ≤
      ∑ a ∈ biasedCollisionIndices j,
        (biasedCollisionResidues j a.1 a.2).card := by
    unfold biasedCollisionUnion
    exact Finset.card_biUnion_le
  have hcardQ : ((biasedCollisionUnion j).card : ℚ) ≤
      ∑ a ∈ biasedCollisionIndices j,
        ((biasedCollisionResidues j a.1 a.2).card : ℚ) := by
    exact_mod_cast hcard
  calc
    biasedCollisionUnionRatio j =
        ((biasedCollisionUnion j).card : ℚ) / (biasedPeriod j : ℚ) := rfl
    _ ≤ (∑ a ∈ biasedCollisionIndices j,
          ((biasedCollisionResidues j a.1 a.2).card : ℚ)) /
          (biasedPeriod j : ℚ) :=
      div_le_div_of_nonneg_right hcardQ (by positivity)
    _ = ∑ a ∈ biasedCollisionIndices j,
          ((biasedCollisionResidues j a.1 a.2).card : ℚ) /
            (biasedPeriod j : ℚ) := by
      rw [Finset.sum_div]
    _ ≤ ∑ _a ∈ biasedCollisionIndices j,
          1 / (2 : ℚ) ^ (2 * biasedK j + 2) := by
      apply Finset.sum_le_sum
      intro a ha
      exact biasedCollisionResidues_ratio_le a.1 a.2
        ((mem_biasedCollisionIndices_iff j a.1 a.2).mp ha)
    _ = ((biasedCollisionIndices j).card : ℚ) *
          (1 / (2 : ℚ) ^ (2 * biasedK j + 2)) := by
      simp

/-- Cancellation of the powers of two appearing in the union bound. -/
theorem powerset_collision_ratio_identity (k : ℕ) :
    (((2 ^ k * k : ℕ) : ℚ) *
        (1 / (2 : ℚ) ^ (2 * k + 2))) =
      (k : ℚ) / (2 : ℚ) ^ (k + 2) := by
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [show 2 * k + 2 = k + (k + 2) by omega, pow_add]
  field_simp

/-- The full finite union is bounded by the elementary collision term
`k / 2^(k+2)`. -/
theorem biasedCollisionUnionRatio_le_crude (j : ℕ) :
    biasedCollisionUnionRatio j ≤
      (biasedK j : ℚ) / (2 : ℚ) ^ (biasedK j + 2) := by
  calc
    biasedCollisionUnionRatio j ≤
        ((biasedCollisionIndices j).card : ℚ) *
          (1 / (2 : ℚ) ^ (2 * biasedK j + 2)) :=
      biasedCollisionUnionRatio_le_index_bound j
    _ ≤ (((2 ^ biasedK j * biasedK j : ℕ) : ℚ) *
          (1 / (2 : ℚ) ^ (2 * biasedK j + 2))) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast biasedCollisionIndices_card_le j
      · positivity
    _ = (biasedK j : ℚ) / (2 : ℚ) ^ (biasedK j + 2) :=
      powerset_collision_ratio_identity (biasedK j)

/-- The normalized cardinality of the union of all `(S, i)` collisions is at
most the target geometric error. -/
theorem biasedCollisionUnionRatio_le {j : ℕ} (_hj : 400 ≤ j) :
    biasedCollisionUnionRatio j ≤
      ((63 : ℚ) / 64) ^ (2 * biasedRadius j) := by
  exact (biasedCollisionUnionRatio_le_crude j).trans (by
    simpa only [biasedK] using collision_numeric_le (biasedRadius j))

end Erdos486
