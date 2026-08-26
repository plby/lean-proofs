import ErdosProblems.Erdos421.ParentForest

/-!
# A coarse count of unequal parents

For the density-one conclusion we can count all possible unequal parents
directly, using disjoint prime-gap lengths. No scale-contraction iteration
or distinction between long and short parents is needed for this bound.
-/

namespace Erdos421

theorem sum_gapLength_le (I : Finset ℕ) (X : ℕ)
    (hX : ∀ i ∈ I, prime (i + 1) ≤ X) : (∑ i ∈ I, gapLength i) ≤ X := by
  rcases I.eq_empty_or_nonempty with rfl | hI
  · simp
  · let j := I.max' hI
    have hj : j ∈ I := I.max'_mem hI
    have hsub : I ⊆ Finset.range (j + 1) := by
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (I.le_max' i hi))
    have hsum := Finset.sum_le_sum_of_subset (f := gapLength) hsub
    have htel := sum_nat_steps prime (j + 1)
      (fun i _ ↦ (prime_strictMono (Nat.lt_succ_self i)).le)
    change (∑ i ∈ Finset.range (j + 1), gapLength i) + prime 0 = prime (j + 1) at htel
    have hjX := hX j hj
    omega

theorem unequal_large_parent_gap_bound {u p g : ℕ} (hu : 1 ≤ u)
    (hp : 2 ^ (40 * u) ≤ p)
    (hineq : p ^ 2 ≤ 2 ^ (60 * u) * g + p * 2 ^ (3 * u)) :
    2 ^ (20 * u) ≤ 2 * g := by
  have hH : 2 * 2 ^ (3 * u) ≤ 2 ^ (40 * u) := by
    calc
      2 * 2 ^ (3 * u) = 2 ^ (3 * u + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ (40 * u) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpH : 2 * 2 ^ (3 * u) ≤ p := hH.trans hp
  have hsq : p ^ 2 ≤ 2 * 2 ^ (60 * u) * g := by nlinarith
  have hpsq := Nat.pow_le_pow_left hp 2
  have hpow : (2 ^ (40 * u)) ^ 2 = 2 ^ (60 * u) * 2 ^ (20 * u) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hpow] at hpsq
  have hbound : 2 ^ (60 * u) * 2 ^ (20 * u) ≤ 2 ^ (60 * u) * (2 * g) := by
    nlinarith [hpsq.trans hsq]
  exact Nat.le_of_mul_le_mul_left hbound (by positivity)

/-- There are at most `3 X^(2/3)` possible unequal parents at this scale. -/
theorem unequal_parent_card_bound (I : Finset ℕ) {u : ℕ} (hu : 1 ≤ u)
    (hX : ∀ i ∈ I, prime (i + 1) ≤ 2 ^ (60 * u))
    (hineq : ∀ i ∈ I, (prime i) ^ 2 ≤
      2 ^ (60 * u) * gapLength i + prime i * 2 ^ (3 * u)) :
    I.card ≤ 3 * 2 ^ (40 * u) := by
  classical
  let small := I.filter (fun i ↦ prime i < 2 ^ (40 * u))
  have hsmall : small ⊆ I := Finset.filter_subset _ _
  have hsmallcard : small.card ≤ 2 ^ (40 * u) := by
    calc
      small.card = (small.image prime).card :=
        (Finset.card_image_of_injective small prime_strictMono.injective).symm
      _ ≤ (Finset.range (2 ^ (40 * u))).card := by
        apply Finset.card_le_card
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
      _ = 2 ^ (40 * u) := Finset.card_range _
  have hlarge : ∀ i ∈ I \ small, 2 ^ (20 * u) ≤ 2 * gapLength i := by
    intro i hi
    obtain ⟨hiI, hinot⟩ := Finset.mem_sdiff.mp hi
    have hp : 2 ^ (40 * u) ≤ prime i := by
      by_contra h
      exact hinot (Finset.mem_filter.mpr ⟨hiI, by omega⟩)
    exact unequal_large_parent_gap_bound hu hp (hineq i hiI)
  have hlargeSum : 2 ^ (20 * u) * (I \ small).card ≤ 2 * 2 ^ (60 * u) := by
    calc
      2 ^ (20 * u) * (I \ small).card = ∑ _i ∈ I \ small, 2 ^ (20 * u) := by simp [mul_comm]
      _ ≤ ∑ i ∈ I \ small, 2 * gapLength i := Finset.sum_le_sum hlarge
      _ = 2 * (∑ i ∈ I \ small, gapLength i) := (Finset.mul_sum ..).symm
      _ ≤ 2 * 2 ^ (60 * u) := Nat.mul_le_mul_left 2
        (sum_gapLength_le (I \ small) _ (fun i hi ↦ hX i (Finset.mem_sdiff.mp hi).1))
  have hprod : 2 ^ (20 * u) * (2 * 2 ^ (40 * u)) = 2 * 2 ^ (60 * u) := by
    rw [mul_left_comm, ← pow_add]
    congr 2
    omega
  rw [← hprod] at hlargeSum
  have hlargecard : (I \ small).card ≤ 2 * 2 ^ (40 * u) :=
    Nat.le_of_mul_le_mul_left hlargeSum (by positivity)
  have hcards := Finset.card_sdiff_add_card_eq_card hsmall
  omega

end Erdos421
