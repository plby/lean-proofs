import Mathlib
import ErdosProblems.Erdos489.RoughCoprimePairs

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- The elementary telescoping bound `1/(m+1)^2 ≤ 1/m - 1/(m+1)`. -/
theorem one_div_succ_sq_le_telescope (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤
      1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hid : (1 : ℝ) / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) =
      1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
    field_simp
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hid]
  apply one_div_le_one_div_of_le
  · positivity
  · have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    have hmul := mul_le_mul_of_nonneg_right hle hsR.le
    simpa [pow_two] using hmul

/-- A finite initial segment of the reciprocal-square tail above `Y` is at
most `1/Y`. -/
theorem sum_range_one_div_add_sq_le (Y N : ℕ) (hY : 0 < Y) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((Y + i + 1 : ℕ) : ℝ) ^ 2) ≤
      1 / (Y : ℝ) := by
  let f : ℕ → ℝ := fun i => 1 / ((Y + i : ℕ) : ℝ)
  calc
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((Y + i + 1 : ℕ) : ℝ) ^ 2) ≤
        ∑ i ∈ Finset.range N, (f i - f (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [f, Nat.add_assoc] using one_div_succ_sq_le_telescope (Y + i) (by omega)
    _ = f 0 - f N := Finset.sum_range_sub' f N
    _ ≤ 1 / (Y : ℝ) := by
      dsimp [f]
      have hnonneg : (0 : ℝ) ≤ 1 / ((Y + N : ℕ) : ℝ) := by positivity
      linarith

/-- The reciprocal-square sum over any finite set of distinct integers in
`(Y,G]` is at most `1/Y`. -/
theorem finset_sum_one_div_sq_le
    (S : Finset ℕ) (Y G : ℕ) (hY : 0 < Y)
    (hlow : ∀ d ∈ S, Y < d) (hupp : ∀ d ∈ S, d ≤ G) :
    (∑ d ∈ S, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 / (Y : ℝ) := by
  let shift : ℕ → ℕ := fun d => d - Y - 1
  let g : ℕ → ℝ := fun k => 1 / ((Y + k + 1 : ℕ) : ℝ) ^ 2
  have hinj : Set.InjOn shift (S : Set ℕ) := by
    intro d hd e he hde
    dsimp [shift] at hde
    have hdY := hlow d hd
    have heY := hlow e he
    omega
  have himage : S.image shift ⊆ Finset.range G := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨d, hd, rfl⟩
    apply Finset.mem_range.mpr
    dsimp [shift]
    have hdG := hupp d hd
    have hdY := hlow d hd
    omega
  calc
    (∑ d ∈ S, (1 : ℝ) / (d : ℝ) ^ 2) = ∑ d ∈ S, g (shift d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdY := hlow d hd
      simp only [g, shift]
      congr 3
      omega
    _ = ∑ k ∈ S.image shift, g k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range G, g k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro k hk hkn
      positivity
    _ ≤ 1 / (Y : ℝ) := by
      exact sum_range_one_div_add_sq_le Y G hY

/-- The prime-fiber capacity sum in F-023 is `O(G^2/Y+G)` with explicit
constants. -/
theorem interval_prime_fiber_square_sum_cast_le
    (Y G : ℕ) (hY : 0 < Y) :
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / p + 1) ^ 2 : ℕ) : ℝ)) ≤
      2 * (G : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by
  let P := (G + 1).primesBelow \ (Y + 1).primesBelow
  have hpLower : ∀ p ∈ P, Y < p := by
    intro p hp
    have hpG := Finset.mem_sdiff.mp hp
    have hpprime := (Nat.mem_primesBelow.mp hpG.1).2
    by_contra hnot
    have hpY : p < Y + 1 := by omega
    exact hpG.2 (Nat.mem_primesBelow.mpr ⟨hpY, hpprime⟩)
  have hpUpper : ∀ p ∈ P, p ≤ G := by
    intro p hp
    have := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
    omega
  have hrecip : (∑ p ∈ P, (1 : ℝ) / (p : ℝ) ^ 2) ≤ 1 / (Y : ℝ) :=
    finset_sum_one_div_sq_le P Y G hY hpLower hpUpper
  have hterm : ∀ p ∈ P,
      (((G / p + 1) ^ 2 : ℕ) : ℝ) ≤
        2 * (G : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
    intro p hp
    have hpprime := (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).2
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hq : ((G / p : ℕ) : ℝ) ≤ (G : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hq0 : (0 : ℝ) ≤ (G / p : ℕ) := by positivity
    have hratio0 : (0 : ℝ) ≤ (G : ℝ) / (p : ℝ) := by positivity
    have hsq : (((G / p : ℕ) : ℝ)) ^ 2 ≤ ((G : ℝ) / (p : ℝ)) ^ 2 :=
      (sq_le_sq₀ hq0 hratio0).2 hq
    norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    have hbasic : ((((G / p : ℕ) : ℝ)) + 1) ^ 2 ≤
        2 * (((G / p : ℕ) : ℝ)) ^ 2 + 2 := by
      nlinarith [sq_nonneg ((((G / p : ℕ) : ℝ)) - 1)]
    calc
      ((((G / p : ℕ) : ℝ)) + 1) ^ 2 ≤
          2 * (((G / p : ℕ) : ℝ)) ^ 2 + 2 := hbasic
      _ ≤ 2 * ((G : ℝ) / (p : ℝ)) ^ 2 + 2 := by nlinarith
      _ = 2 * (G : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2 := by
        field_simp
  have hPsubset : P ⊆ Finset.range (G + 1) := by
    intro p hp
    exact Finset.mem_range.mpr
      (Nat.mem_primesBelow.mp (Finset.mem_sdiff.mp hp).1).1
  have hcardNat : P.card ≤ G + 1 := by
    simpa using Finset.card_le_card hPsubset
  have hcard : (P.card : ℝ) ≤ ((G + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  calc
    (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / p + 1) ^ 2 : ℕ) : ℝ)) =
        ∑ p ∈ P, (((G / p + 1) ^ 2 : ℕ) : ℝ) := rfl
    _ ≤ ∑ p ∈ P,
        (2 * (G : ℝ) ^ 2 * ((1 : ℝ) / (p : ℝ) ^ 2) + 2) := by
      apply Finset.sum_le_sum
      exact hterm
    _ = 2 * (G : ℝ) ^ 2 *
          (∑ p ∈ P, ((1 : ℝ) / (p : ℝ) ^ 2)) + 2 * (P.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 2 * (G : ℝ) ^ 2 * (1 / (Y : ℝ)) + 2 * ((G + 1 : ℕ) : ℝ) := by
      have hG0 : 0 ≤ 2 * (G : ℝ) ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hrecip hG0]
    _ = 2 * (G : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by ring

/-- Explicit real bound for the number of ordered noncoprime pairs among rough
points in an interval. -/
theorem noncoprimeOrderedPairs_cast_le_rough_interval
    (S : Finset ℕ) (L G Y : ℕ) (hY : 0 < Y)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hrough : ∀ n ∈ S, ∀ p, Nat.Prime p → p ∣ n → Y < p) :
    ((noncoprimeOrderedPairs S).card : ℝ) ≤
      2 * (G : ℝ) ^ 2 / (Y : ℝ) + 2 * ((G + 1 : ℕ) : ℝ) := by
  have hnat := noncoprimeOrderedPairs_card_le_interval_prime_sum
    S L G Y hinterval hrough
  have hcast : ((noncoprimeOrderedPairs S).card : ℝ) ≤
      (∑ p ∈ (G + 1).primesBelow \ (Y + 1).primesBelow,
        (((G / p + 1) ^ 2 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  exact hcast.trans (interval_prime_fiber_square_sum_cast_le Y G hY)

end Erdos489
