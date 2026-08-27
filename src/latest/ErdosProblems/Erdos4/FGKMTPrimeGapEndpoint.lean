import ErdosProblems.Erdos4.FGKMTGrowingIntervalCover
import Mathlib.NumberTheory.Bertrand

/-! Consecutive prime gaps from the covers, with an explicit upper bound on the right endpoint. -/

namespace Erdos4.FGKMT

open Filter Classical

theorem nth_prime_succ_le_twice (n : ℕ) :
    Nat.nth Nat.Prime (n + 1) ≤ 2 * Nat.nth Nat.Prime n := by
  have hp := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime n
  obtain ⟨q, hq, hpq, hqupper⟩ := Nat.exists_prime_lt_and_le_two_mul
    (Nat.nth Nat.Prime n) hp.ne_zero
  have hnc : n < Nat.count Nat.Prime q :=
    (Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 hpq
  have hcount : n + 1 < Nat.count Nat.Prime (q + 1) := by
    rw [Nat.count_succ, if_pos hq]
    omega
  have hnext := Nat.nth_lt_of_lt_count hcount
  exact (show Nat.nth Nat.Prime (n + 1) ≤ q by omega).trans hqupper

theorem exists_gap_with_right_endpoint (b y : ℕ) (hb : 2 ≤ b)
    (hcomp : ∀ i : ℕ, 1 ≤ i → i ≤ y → ¬(b + i).Prime) :
    ∃ n : ℕ, Nat.nth Nat.Prime (n + 1) ≤ 2 * b ∧
      (y : ℝ) < (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  let c := Nat.count Nat.Prime (b + 1)
  have hcpos : 0 < c := by
    apply Nat.pos_of_ne_zero
    rw [Nat.count_ne_iff_exists]
    exact ⟨2, by omega, Nat.prime_two⟩
  let n := c - 1
  have hnadd : n + 1 = c := Nat.sub_add_cancel hcpos
  have hnltc : n < c := by omega
  have hleft : Nat.nth Nat.Prime n ≤ b := by
    have hh := Nat.nth_lt_of_lt_count hnltc
    omega
  have hcount := Erdos4.count_prime_eq_of_composite_block b y hcomp
  have hright : b + y + 1 ≤ Nat.nth Nat.Prime (n + 1) := by
    have hh := Nat.le_nth_count Nat.infinite_setOfPred_prime (b + y + 1)
    rw [hcount] at hh
    simpa only [hnadd, c] using hh
  refine ⟨n, (nth_prime_succ_le_twice n).trans (Nat.mul_le_mul_left 2 hleft), ?_⟩
  have hrR : (b : ℝ) + y + 1 ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) := by exact_mod_cast hright
  have hlR : (Nat.nth Nat.Prime n : ℝ) ≤ b := by exact_mod_cast hleft
  linarith

theorem residueCover_gap_endpoint {y : ℕ} (cover : Erdos4.ResidueCover y) :
    ∃ n : ℕ, Nat.nth Nat.Prime (n + 1) ≤ 6 * cover.modulus ∧
      (y : ℝ) < (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨b, hb, hbound, hcomp⟩ := cover.exists_composite_block_ge 2
  obtain ⟨n, hn, hgap⟩ := exists_gap_with_right_endpoint b y hb hcomp
  refine ⟨n, ?_, hgap⟩
  norm_num at hbound
  omega

theorem six_primorial_le_exp (K x : ℕ) (hx : 1 ≤ x) :
    ((6 * primorial (K * x) : ℕ) : ℝ) ≤ Real.exp (((4 * K + 10 : ℕ) : ℝ) * x) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog4 : Real.log (4 : ℝ) ≤ 4 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hprime : (primorial (K * x) : ℝ) ≤ Real.exp (4 * (K : ℝ) * x) := by
    calc
      _ ≤ (4 : ℝ) ^ (K * x) := by exact_mod_cast primorial_le_four_pow (K * x)
      _ = Real.exp (((K * x : ℕ) : ℝ) * Real.log 4) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg (K * x))
        push_cast at hh ⊢
        nlinarith only [hh]
  have hcoef : 6 ≤ Real.exp (10 * (x : ℝ)) := by
    have hh := Real.add_one_le_exp (10 * (x : ℝ))
    linarith
  calc
    _ = 6 * (primorial (K * x) : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (10 * (x : ℝ)) * Real.exp (4 * (K : ℝ) * x) :=
      mul_le_mul hcoef hprime (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

theorem exists_growing_prime_gaps :
    ∃ (c : ℝ) (D : ℕ), 0 < c ∧ 1 ≤ D ∧ ∀ᶠ x : ℕ in atTop,
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Real.exp ((D : ℝ) * x) ∧
        (growingGapLength c x : ℝ) <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, K, hc, _, hcover⟩ := exists_growing_interval_cover
  refine ⟨c, 4 * K + 10, hc, by omega, ?_⟩
  filter_upwards [hcover, eventually_ge_atTop 1] with x hx hx1
  obtain ⟨cover, hmod⟩ := hx
  obtain ⟨n, hn, hgap⟩ := residueCover_gap_endpoint cover
  refine ⟨n, ?_, hgap⟩
  have hnat := hn.trans (Nat.mul_le_mul_left 6 hmod)
  have hreal : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ (6 * primorial (K * x) : ℕ) := by
    exact_mod_cast hnat
  exact hreal.trans (six_primorial_le_exp K x hx1)

end Erdos4.FGKMT
