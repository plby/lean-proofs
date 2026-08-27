import ErdosProblems.Erdos587.HooleyRankinProduct
import ErdosProblems.Erdos587.HooleyMertens

/-!
# Uniform Rankin Euler bounds

The weighted Mertens estimate controls the extra Euler factors caused by
a small real-power twist. The resulting bound is independent of the
smoothness cutoff when the exponent times its logarithm is bounded.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_prime_log_harmonic_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ z : ℕ, 2 ≤ z →
      (∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / p) ≤ D * Real.log (z : ℝ) := by
  obtain ⟨C, hC⟩ := BoundedGaps.Maynard.exists_uniform_abs_primeLogHarmonicSum_sub_log
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨1 + |C| / Real.log 2, by positivity, ?_⟩
  intro z hz
  have hlog : Real.log (2 : ℝ) ≤ Real.log (z : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hz)
  have hupper := (abs_le.mp (hC z)).2
  change (∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / p) - Real.log (z : ℝ) ≤ C at hupper
  have habs : |C| ≤ (|C| / Real.log 2) * Real.log (z : ℝ) := by
    calc
      _ = (|C| / Real.log 2) * Real.log 2 := (div_mul_cancel₀ _ hlog2.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
  nlinarith [le_abs_self C]

noncomputable def deltaRankinMertensConstant : ℝ :=
  Classical.choose exists_delta_prime_log_harmonic_bound

lemma deltaRankinMertensConstant_pos : 0 < deltaRankinMertensConstant :=
  (Classical.choose_spec exists_delta_prime_log_harmonic_bound).1

lemma delta_prime_log_harmonic_bound {z : ℕ} (hz : 2 ≤ z) :
    (∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / p) ≤
      deltaRankinMertensConstant * Real.log (z : ℝ) :=
  (Classical.choose_spec exists_delta_prime_log_harmonic_bound).2 z hz

lemma delta_exp_sub_one_le {s M : ℝ} (hs : 0 ≤ s) (hM : s ≤ M) :
    Real.exp s - 1 ≤ s * Real.exp M := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-s))
    (Real.exp_nonneg s)
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero s)] at h
  calc
    _ ≤ s * Real.exp s := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hM) hs

lemma delta_rankin_prime_increment_le {p z : ℕ} (hp : p.Prime) (hpz : p ≤ z)
    {β M : ℝ} (hβ : 0 ≤ β) (hM : β * Real.log (z : ℝ) ≤ M) :
    ((p : ℝ) ^ β - 1) / p ≤
      (β * Real.exp M) * (Real.log (p : ℝ) / p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hlog : Real.log (p : ℝ) ≤ Real.log (z : ℝ) :=
    Real.log_le_log hp0 (by exact_mod_cast hpz)
  have hs : Real.log (p : ℝ) * β ≤ M := by
    calc
      _ = β * Real.log (p : ℝ) := mul_comm _ _
      _ ≤ β * Real.log (z : ℝ) := mul_le_mul_of_nonneg_left hlog hβ
      _ ≤ M := hM
  rw [Real.rpow_def_of_pos hp0]
  calc
    _ ≤ (Real.log (p : ℝ) * β * Real.exp M) / p :=
      div_le_div_of_nonneg_right (delta_exp_sub_one_le (mul_nonneg hlp hβ) hs) hp0.le
    _ = _ := by ring

theorem delta_rankin_euler_product_bound (P : Finset ℕ) {z : ℕ} (hz : 2 ≤ z)
    (hP : P ⊆ Nat.primesLE z) {β M : ℝ} (hβ : 0 ≤ β)
    (hM : β * Real.log (z : ℝ) ≤ M) :
    (∏ p ∈ P, (1 + 20 * (((p : ℝ) ^ β - 1) / p))) ≤
      Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M) := by
  have hsum : (∑ p ∈ P, ((p : ℝ) ^ β - 1) / p) ≤
      deltaRankinMertensConstant * M * Real.exp M := by
    calc
      _ ≤ ∑ p ∈ P, (β * Real.exp M) * (Real.log (p : ℝ) / p) := by
        apply Finset.sum_le_sum
        intro p hp
        obtain ⟨hpz, hpprime⟩ := Nat.mem_primesLE.mp (hP hp)
        exact delta_rankin_prime_increment_le hpprime hpz hβ hM
      _ = (β * Real.exp M) * ∑ p ∈ P, Real.log (p : ℝ) / p :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (β * Real.exp M) * ∑ p ∈ Nat.primesLE z, Real.log (p : ℝ) / p := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg hP
        intro p hp hnot
        exact div_nonneg (Real.log_nonneg (by
          exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)) (by positivity)
      _ ≤ (β * Real.exp M) * (deltaRankinMertensConstant * Real.log (z : ℝ)) :=
        mul_le_mul_of_nonneg_left (delta_prime_log_harmonic_bound hz) (by positivity)
      _ = (deltaRankinMertensConstant * Real.exp M) * (β * Real.log (z : ℝ)) := by ring
      _ ≤ (deltaRankinMertensConstant * Real.exp M) * M :=
        mul_le_mul_of_nonneg_left hM
          (mul_nonneg deltaRankinMertensConstant_pos.le (Real.exp_nonneg _))
      _ = _ := by ring
  calc
    _ ≤ ∏ p ∈ P, Real.exp (20 * (((p : ℝ) ^ β - 1) / p)) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpow : (1 : ℝ) ≤ (p : ℝ) ^ β := Real.one_le_rpow
          (by exact_mod_cast (Nat.mem_primesLE.mp (hP hp)).2.one_le) hβ
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (20 * (((p : ℝ) ^ β - 1) / p))
    _ = Real.exp (20 * ∑ p ∈ P, ((p : ℝ) ^ β - 1) / p) := by
      rw [← Real.exp_sum, ← Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem sum_smooth_deltaRankinWeight_bound (S : Finset ℕ) {z : ℕ} (hz : 2 ≤ z)
    (hS : ∀ n ∈ S, n ≠ 0) (hsub : ∀ n ∈ S, n.primeFactors ⊆ Nat.primesLE z)
    {β M : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (hM : β * Real.log (z : ℝ) ≤ M) :
    (∑ n ∈ S, (n.divisors.card : ℝ) * deltaRankinWeight β n / n) ≤
      Real.exp (20 * deltaRankinMertensConstant * M * Real.exp M) := by
  exact (sum_smooth_deltaRankinWeight_le S (Nat.primesLE z)
    (fun p hp => (Nat.mem_primesLE.mp hp).2) hS hsub hβ0 hβ).trans
      (delta_rankin_euler_product_bound _ hz (Finset.Subset.refl _) hβ0 hM)

end Erdos587
