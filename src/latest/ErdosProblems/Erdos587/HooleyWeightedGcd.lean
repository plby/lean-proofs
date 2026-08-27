import ErdosProblems.Erdos587.HooleyGcdMean
import ErdosProblems.Erdos587.HooleyDenominatorBlocks
import ErdosProblems.Erdos587.ReciprocalDivisor

/-! # The single log-log cost of the reciprocal denominator gcds -/

open scoped BigOperators

namespace Erdos587

lemma delta_card_gcd_mul_le {a q : ℕ} (ha : 0 < a) (hq : 0 < q) (b : ℕ) :
    (q.gcd (a * b)).divisors.card ≤ a.divisors.card * (q.gcd b).divisors.card := by
  have hd : q.gcd (a * b) ∣ a * q.gcd b :=
    (Nat.gcd_mul_right_dvd_mul_gcd q a b).trans
      (Nat.mul_dvd_mul (Nat.gcd_dvd_right q a) (dvd_refl (q.gcd b)))
  have hn : a * q.gcd b ≠ 0 := (Nat.mul_pos ha (Nat.gcd_pos_of_pos_left b hq)).ne'
  exact (Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd)).trans
    (card_divisors_mul_le_product a (q.gcd b))

theorem exists_delta_gcd_multiple_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a q L : ℕ, 0 < a → 0 < q →
      (∑ b ∈ Finset.Icc 1 L, ((q.gcd (a * b)).divisors.card : ℝ)) ≤
        C * a.divisors.card * L * max 1 (Real.log (Real.log (q : ℝ))) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_gcd_divisor_mean_bound
  refine ⟨C, hC, ?_⟩
  intro a q L ha hq
  have hinterval : Finset.Icc 1 L = Finset.Ioc 0 L := by
    ext b
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  calc
    _ ≤ ∑ b ∈ Finset.Icc 1 L, (a.divisors.card : ℝ) * (q.gcd b).divisors.card :=
      Finset.sum_le_sum (fun b hb => by exact_mod_cast delta_card_gcd_mul_le ha hq b)
    _ = (a.divisors.card : ℝ) * ∑ b ∈ Finset.Ioc 0 L, ((q.gcd b).divisors.card : ℝ) := by
      rw [← Finset.mul_sum, hinterval]
    _ ≤ (a.divisors.card : ℝ) * (C * L * max 1 (Real.log (Real.log (q : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hmean q L hq) (by positivity)
    _ = _ := by ring

theorem delta_sum_denominator_shell_cost (f : ℕ → ℝ) (D : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ b, 0 ≤ f b) (hprefix : ∀ L : ℕ, (∑ b ∈ Finset.Icc 1 L, f b) ≤ A * L) :
    (∑ b ∈ Finset.Icc 1 (2 ^ D), f b * ((D - Nat.clog 2 b : ℕ) + 3)) ≤
      8 * A * 2 ^ D := by
  classical
  let S := Finset.Icc 1 (2 ^ D)
  have hmap (b : ℕ) (hb : b ∈ S) : Nat.clog 2 b ∈ Finset.range (D + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.clog_le_of_le_pow (Finset.mem_Icc.mp hb).2))
  have hlevel (j : ℕ) (hj : j ∈ Finset.range (D + 1)) :
      (∑ b ∈ S with Nat.clog 2 b = j, f b * ((D - Nat.clog 2 b : ℕ) + 3)) ≤
        A * 2 ^ j * ((D - j : ℕ) + 3) := by
    let T := S.filter (fun b => Nat.clog 2 b = j)
    have hsub : T ⊆ Finset.Icc 1 (2 ^ j) := by
      intro b hb
      refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1, ?_⟩
      have h := Nat.le_pow_clog (by norm_num : 1 < 2) b
      simpa only [(Finset.mem_filter.mp hb).2] using h
    calc
      _ = (∑ b ∈ T, f b) * ((D - j : ℕ) + 3) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        rw [(Finset.mem_filter.mp hb).2]
      _ ≤ (∑ b ∈ Finset.Icc 1 (2 ^ j), f b) * ((D - j : ℕ) + 3) :=
        mul_le_mul_of_nonneg_right
          (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun b hb hnot => hf b)) (by positivity)
      _ ≤ (A * (2 ^ j : ℕ)) * ((D - j : ℕ) + 3) :=
        mul_le_mul_of_nonneg_right (hprefix (2 ^ j)) (by positivity)
      _ = _ := by push_cast; rfl
  calc
    _ = ∑ j ∈ Finset.range (D + 1),
        ∑ b ∈ S with Nat.clog 2 b = j, f b * ((D - Nat.clog 2 b : ℕ) + 3) :=
      (Finset.sum_fiberwise_of_maps_to hmap _).symm
    _ ≤ ∑ j ∈ Finset.range (D + 1), A * 2 ^ j * ((D - j : ℕ) + 3) :=
      Finset.sum_le_sum hlevel
    _ = A * ∑ j ∈ Finset.range (D + 1), (2 : ℝ) ^ j * ((D - j : ℕ) + 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ A * (8 * 2 ^ D) := mul_le_mul_of_nonneg_left (delta_sum_dyadic_shell_cost D) hA
    _ = _ := by ring

theorem exists_delta_weighted_gcd_multiple_mean_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a q D : ℕ, 0 < a → 0 < q →
      (∑ b ∈ Finset.Icc 1 (2 ^ D),
        ((q.gcd (a * b)).divisors.card : ℝ) * ((D - Nat.clog 2 b : ℕ) + 3)) ≤
        C * a.divisors.card * 2 ^ D * max 1 (Real.log (Real.log (q : ℝ))) := by
  obtain ⟨C, hC, hmean⟩ := exists_delta_gcd_multiple_mean_bound
  refine ⟨8 * C, by positivity, ?_⟩
  intro a q D ha hq
  have hprefix (L : ℕ) : (∑ b ∈ Finset.Icc 1 L, ((q.gcd (a * b)).divisors.card : ℝ)) ≤
      (C * a.divisors.card * max 1 (Real.log (Real.log (q : ℝ)))) * L :=
    (hmean a q L ha hq).trans_eq (by ring)
  have h := delta_sum_denominator_shell_cost (fun b => ((q.gcd (a * b)).divisors.card : ℝ)) D
    (by positivity) (fun b => by positivity) hprefix
  exact h.trans_eq (by ring)

end Erdos587
