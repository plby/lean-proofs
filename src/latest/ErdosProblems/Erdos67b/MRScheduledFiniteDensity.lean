import ErdosProblems.Erdos67b.MRScheduledDensityGeometry

/-! # Finite beta-sieve density uniform in the growing scheduled family -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrScheduled_sieveRemainder_le
    {eta p q L : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p) (hq : 1 ≤ q)
    (hpq : p ≤ q) (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    (hL : 1 ≤ L) {J : ℕ} (hJ : 1 ≤ J)
    (hupper : mrLogScheduleUpper q J ≤ Real.sqrt L) (S : ℕ) :
    (∑ I ∈ mrScheduledBlocks p q J, (((I.2 ^ S : ℕ) : ℝ) ^ 2)) ≤
      L * Real.exp (2 * (S : ℝ) * Real.sqrt L) := by
  have hcard : ((mrScheduledBlocks p q J).card : ℝ) ≤ J := by
    have hn : (mrScheduledBlocks p q J).card ≤ J := by
      calc
        _ ≤ (Finset.Icc 1 J).card := Finset.card_image_le
        _ = J := by simp
    exact_mod_cast hn
  have hindex := mrLastBlock_index_le_log hq hL hJ hupper
  calc
    _ ≤ ∑ _I ∈ mrScheduledBlocks p q J, Real.exp (2 * (S : ℝ) * Real.sqrt L) := by
      apply Finset.sum_le_sum
      intro I hI
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI
      have hjdata := Finset.mem_Icc.mp hj
      have hmono := mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget
        hjdata.1 hjdata.2
      have hu : ((mrScheduledPrimeInterval p q j).2 : ℝ) ≤ Real.exp (Real.sqrt L) :=
        (Nat.floor_le (Real.exp_pos _).le).trans (Real.exp_le_exp.mpr (hmono.trans hupper))
      calc
        _ ≤ (Real.exp (Real.sqrt L) ^ S) ^ 2 := by push_cast; gcongr
        _ = _ := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    _ = ((mrScheduledBlocks p q J).card : ℝ) * Real.exp (2 * (S : ℝ) * Real.sqrt L) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (hcard.trans hindex) (Real.exp_pos _).le

theorem mrExists_scheduled_finite_atypical_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ S : ℕ, 101 ≤ S ∧
      ∀ {eta p q L : ℝ}, eta ≤ 1 / 12 → 2 ≤ p → 1 ≤ q → 2 * p ≤ q →
        1 ≤ Real.log q → 4096 * Real.log q ≤ eta * p → 1 ≤ L →
      ∀ {J : ℕ}, 1 ≤ J → mrLogScheduleUpper q J ≤ Real.sqrt L →
      ∀ Z : ℕ,
        ((atypicalFactorizationSet (mrScheduledBlocks p q J) Z).card : ℝ) ≤
          C * (p / q) * Z + L * Real.exp (2 * (S : ℝ) * Real.sqrt L) := by
  obtain ⟨A, S, hA, hS, _, hfinite⟩ :=
    exists_uniform_card_atypicalFactorizationSet_mertens_beta_bound
  let K := (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
    Real.exp (2 * PrimeEstimates.mertensBound)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨4 * K, by positivity, S, hS, ?_⟩
  intro eta p q L heta hp hq hpq hlogq hbudget hL J hJ hupper Z
  have hvalid : ∀ I ∈ mrScheduledBlocks p q J, 3 ≤ I.1 ∧ I.1 ≤ I.2 := by
    intro I hI
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI
    exact mrScheduledPrimeInterval_valid hp hq hpq (Finset.mem_Icc.mp hj).1
  have hbase := hfinite (mrScheduledBlocks p q J) Z hvalid
  have hratio := mrScheduledBlocks_sum_logRatio_le heta hp hq hpq hlogq hbudget J
  have hsum : (∑ I ∈ mrScheduledBlocks p q J,
      (1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
        (Real.exp (2 * PrimeEstimates.mertensBound) *
          (Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)))) ≤ K * (4 * p / q) := by
    calc
      _ = K * (∑ I ∈ mrScheduledBlocks p q J,
          Real.log ((I.1 - 1 : ℕ) : ℝ) / Real.log (I.2 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I hI
        dsimp [K]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hratio hK.le
  have hrem := mrScheduled_sieveRemainder_le heta hp hq (by linarith) hlogq hbudget
    hL hJ hupper S
  calc
    _ ≤ (Z : ℝ) * _ + _ := hbase
    _ ≤ (Z : ℝ) * (K * (4 * p / q)) + L * Real.exp (2 * (S : ℝ) * Real.sqrt L) :=
      add_le_add (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg Z)) hrem
    _ = _ := by ring

end

end Erdos67b
