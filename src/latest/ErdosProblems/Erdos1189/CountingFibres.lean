/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Decomposing the counting construction by digit exponent.
Informal source: BBMST equation (21).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingFrameLower
import ErdosProblems.Erdos1189.RealPrimeMoments

namespace Erdos1189

open Finset

lemma coordinate_mem_iff_prime_cutoff {x : ℝ} {p e : ℕ} :
    (p, e) ∈ countingCoordinates x ↔ p ∈ Nat.primesLE (Nat.ceil (x * logIncrement e)) := by
  rw [mem_countingCoordinates, mem_primesLE_ceil_iff]
  constructor
  · rintro ⟨hp, hs⟩
    exact ⟨hp, (div_lt_iff₀ (logIncrement_pos e)).mp hs⟩
  · rintro ⟨hp, hs⟩
    exact ⟨hp, (div_lt_iff₀ (logIncrement_pos e)).mpr hs⟩

lemma sum_countingCoordinates_by_exponent (x : ℝ) (f : ℕ × ℕ → ℝ) :
    (∑ c ∈ countingCoordinates x, f c) =
      ∑ e ∈ range (Nat.ceil x), ∑ p ∈ Nat.primesLE (Nat.ceil (x * logIncrement e)), f (p, e) := by
  classical
  unfold countingCoordinates
  rw [sum_filter]
  change (∑ a ∈ range (Nat.ceil x + 2) ×ˢ range (Nat.ceil x),
    if a.1.Prime ∧ coordinateScore a.1 a.2 < x then f a else 0) = _
  rw [sum_product, sum_comm]
  apply sum_congr rfl
  intro e _
  have hset : (range (Nat.ceil x + 2)).filter
      (fun p => p.Prime ∧ coordinateScore p e < x) =
        Nat.primesLE (Nat.ceil (x * logIncrement e)) := by
    ext p
    rw [← coordinate_mem_iff_prime_cutoff, mem_countingCoordinates, mem_filter, mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      have hmem := mem_filter.mp (mem_countingCoordinates.mpr h)
      exact ⟨mem_range.mp (mem_product.mp hmem.1).1, h⟩
  rw [← sum_filter, hset]

noncomputable def realPrimeWeightSum (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE (Nat.ceil x), ((p : ℝ) - 1)

lemma realPrimeWeightSum_nonneg (x : ℝ) : 0 ≤ realPrimeWeightSum x := by
  apply sum_nonneg
  intro p hp
  have h : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_lt.le
  linarith

theorem countingSize_real_eq (x : ℝ) :
    (countingSize x : ℝ) =
      1 + ∑ e ∈ range (Nat.ceil x), realPrimeWeightSum (x * logIncrement e) := by
  rw [countingSize_eq, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
  congr 1
  calc
    _ = ∑ c ∈ countingCoordinates x, ((c.1 : ℝ) - 1) := by
      apply sum_congr rfl
      intro c hc
      rw [Nat.cast_sub (mem_countingCoordinates.mp hc).1.one_lt.le, Nat.cast_one]
    _ = _ := sum_countingCoordinates_by_exponent x _

lemma realPrimeWeightSum_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : realPrimeWeightSum x = 0 := by
  apply sum_eq_zero
  intro p hp
  obtain ⟨hp, hpx⟩ := mem_primesLE_ceil_iff.mp hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  linarith

lemma realPrimeWeightSum_le_two_sq {x : ℝ} (hx : 0 ≤ x) : realPrimeWeightSum x ≤ 2 * x ^ 2 := by
  by_cases hx1 : x ≤ 1
  · rw [realPrimeWeightSum_zero_of_le_one hx1]
    positivity
  · have hx1' : 1 ≤ x := by linarith
    have hceil := Nat.ceil_lt_add_one hx
    have hcard : ((Nat.primesLE (Nat.ceil x)).card : ℝ) ≤ (Nat.ceil x : ℝ) := by
      have hsub : Nat.primesLE (Nat.ceil x) ⊆ Ioc 0 (Nat.ceil x) := by
        intro p hp
        exact mem_Ioc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
      have h := card_le_card hsub
      simp only [Nat.card_Ioc, Nat.sub_zero] at h
      exact_mod_cast h
    calc
      realPrimeWeightSum x ≤ ∑ p ∈ Nat.primesLE (Nat.ceil x), x := by
        apply sum_le_sum
        intro p hp
        exact (mem_primesLE_ceil_iff.mp hp).2.le
      _ = (Nat.primesLE (Nat.ceil x)).card * x := by simp
      _ ≤ (Nat.ceil x : ℝ) * x := mul_le_mul_of_nonneg_right hcard hx
      _ ≤ 2 * x ^ 2 := by nlinarith

lemma realPrimeWeightSum_exponent_zero {x : ℝ} {e : ℕ} (he : Nat.ceil x ≤ e) :
    realPrimeWeightSum (x * logIncrement e) = 0 := by
  apply realPrimeWeightSum_zero_of_le_one
  by_cases hx : 0 ≤ x
  · have hxe : x ≤ (e : ℝ) + 1 := by
      have hceil := Nat.le_ceil x
      have he' : (Nat.ceil x : ℝ) ≤ e := by exact_mod_cast he
      linarith
    have hmul := mul_le_mul_of_nonneg_left (logIncrement_le_inv e) hx
    have hdiv : x / ((e : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hxe
    simpa only [div_eq_mul_inv] using hmul.trans hdiv
  · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) (logIncrement_pos e).le).trans (by norm_num)

end Erdos1189
