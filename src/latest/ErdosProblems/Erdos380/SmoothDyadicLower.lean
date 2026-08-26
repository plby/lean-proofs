import ErdosProblems.Erdos380.SmoothPrimeRectangle

/-! # Quantitative smooth-number lower bounds from consecutive dyadic prime pools -/

open scoped BigOperators

namespace Erdos380

def dyadicRectangleExponent (b k : ℕ) : ℕ := ∑ i : Fin k, (b + i.val + 1)

lemma dyadicPrimes_disjoint_of_double_le {M N : ℕ} (hMN : 2 * M ≤ N) :
    Disjoint (dyadicPrimes M) (dyadicPrimes N) := by
  apply Finset.disjoint_left.mpr
  intro p hpM hpN
  have hpM' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpM).1
  have hpN' := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpN).1
  omega

lemma dyadic_power_prime_pools_disjoint (b k : ℕ) :
    Pairwise fun i j : Fin k =>
      Disjoint (dyadicPrimes (2 ^ (b + i.val))) (dyadicPrimes (2 ^ (b + j.val))) := by
  intro i j hij
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · apply dyadicPrimes_disjoint_of_double_le
    calc
      2 * 2 ^ (b + i.val) = 2 ^ (b + i.val + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ (b + j.val) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · apply Disjoint.symm
    apply dyadicPrimes_disjoint_of_double_le
    calc
      2 * 2 ^ (b + j.val) = 2 ^ (b + j.val + 1) := by rw [pow_succ]; omega
      _ ≤ 2 ^ (b + i.val) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem smoothCount_ge_dyadic_prime_rectangle (a b k : ℕ) (hab : a ≤ b) :
    2 ^ a * (∏ i : Fin k, (dyadicPrimes (2 ^ (b + i.val))).card) ≤
      smoothCount (2 ^ (a + dyadicRectangleExponent b k)) (2 ^ (b + k)) := by
  let s (i : Fin k) := dyadicPrimes (2 ^ (b + i.val))
  let P (i : Fin k) := 2 ^ (b + i.val + 1)
  apply smoothCount_ge_prime_rectangle s P
  · intro i p hp
    exact dyadicPrimes_prime hp
  · intro i p hp
    have h := dyadicPrimes_le hp
    simpa only [P, pow_succ, mul_comm] using h
  · intro i p hp
    have hlow := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : a ≤ b + i.val)).trans_lt hlow
  · exact dyadic_power_prime_pools_disjoint b k
  · exact Nat.one_le_pow _ _ (by norm_num)
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro i p hp
    have h := dyadicPrimes_le hp
    calc
      p ≤ 2 ^ (b + i.val + 1) := by simpa [pow_succ, mul_comm] using h
      _ ≤ 2 ^ (b + k) := Nat.pow_le_pow_right (by norm_num) (by have := i.isLt; omega)
  · simp only [P, ← Finset.prod_pow_eq_pow_sum, dyadicRectangleExponent, pow_add]
    rfl

lemma dyadic_power_card_lower_mul {d Y : ℕ}
    (hd4 : 4 ≤ 2 ^ d) (hdY : d + 1 ≤ Y)
    (hc : (((2 ^ d : ℕ) : ℝ) / Real.log (2 ^ d : ℕ)) / 10 ≤
      ((dyadicPrimes (2 ^ d)).card : ℝ)) :
    (2 : ℝ) ^ (d + 1) ≤ (20 * Y : ℝ) * ((dyadicPrimes (2 ^ d)).card : ℝ) := by
  have hbase := dyadic_pool_card_lower_mul hd4 hc
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlog : Real.log (2 ^ d : ℕ) ≤ (Y : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    have hmul := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    have hdR : (d : ℝ) ≤ Y := by exact_mod_cast (by omega : d ≤ Y)
    linarith
  have hcard0 : (0 : ℝ) ≤ (dyadicPrimes (2 ^ d)).card := by positivity
  have hm := mul_le_mul_of_nonneg_right hlog hcard0
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hbase hm
  rw [pow_succ]
  nlinarith

/-- The exact dyadic lower estimate.  Its loss is only one factor
`20 * (b+k)` per chosen prime, with no factorial. -/
theorem exists_smoothCount_dyadic_lower : ∃ b₀ : ℕ, ∀ b ≥ b₀, ∀ a k : ℕ, a ≤ b →
    (2 : ℝ) ^ (a + dyadicRectangleExponent b k) ≤
      (20 * (b + k) : ℝ) ^ k *
        (smoothCount (2 ^ (a + dyadicRectangleExponent b k)) (2 ^ (b + k)) : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp eventually_dyadicPrimes_card_bounds
  refine ⟨max 4 N₀, fun b hb a k hab => ?_⟩
  have hb4 : 4 ≤ b := (le_max_left _ _).trans hb
  have hbN : N₀ ≤ b := (le_max_right _ _).trans hb
  have hpool (i : Fin k) : (2 : ℝ) ^ (b + i.val + 1) ≤
      (20 * (b + k) : ℝ) * ((dyadicPrimes (2 ^ (b + i.val))).card : ℝ) := by
    have hbd : b ≤ 2 ^ (b + i.val) := (by omega : b ≤ b + i.val).trans
      (Nat.le_of_lt (Nat.lt_two_pow_self))
    simpa only [Nat.cast_add] using dyadic_power_card_lower_mul (d := b + i.val) (Y := b + k)
      (hb4.trans hbd) (by have := i.isLt; omega)
      ((hN₀ _ (hbN.trans hbd)).1)
  have hprod := Finset.prod_le_prod
    (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => by positivity : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (2 : ℝ) ^ (b + i.val + 1))
    (fun i _ => hpool i)
  have hprod' : (2 : ℝ) ^ dyadicRectangleExponent b k ≤
      (20 * (b + k) : ℝ) ^ k * ∏ i : Fin k, ((dyadicPrimes (2 ^ (b + i.val))).card : ℝ) := by
    simpa only [dyadicRectangleExponent, ← Finset.prod_pow_eq_pow_sum,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] using hprod
  have hrectangle : (2 : ℝ) ^ a * ∏ i : Fin k, ((dyadicPrimes (2 ^ (b + i.val))).card : ℝ) ≤
      (smoothCount (2 ^ (a + dyadicRectangleExponent b k)) (2 ^ (b + k)) : ℝ) := by
    exact_mod_cast smoothCount_ge_dyadic_prime_rectangle a b k hab
  calc
    (2 : ℝ) ^ (a + dyadicRectangleExponent b k) = (2 : ℝ) ^ a * (2 : ℝ) ^ dyadicRectangleExponent b k := pow_add _ _ _
    _ ≤ (2 : ℝ) ^ a * ((20 * (b + k) : ℝ) ^ k *
        ∏ i : Fin k, ((dyadicPrimes (2 ^ (b + i.val))).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ = (20 * (b + k) : ℝ) ^ k * ((2 : ℝ) ^ a *
        ∏ i : Fin k, ((dyadicPrimes (2 ^ (b + i.val))).card : ℝ)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrectangle (by positivity)

end Erdos380
