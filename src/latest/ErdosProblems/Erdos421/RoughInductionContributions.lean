import ErdosProblems.Erdos421.BuchstabInclusivePrimeSaving
import ErdosProblems.Erdos421.RoughCountEstimate

/-! # The prime and main-term contributions to the rough-number induction -/

namespace Erdos421

theorem prime_count_long_asymptotic {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ a : ℝ, b / 2 ≤ a → a ≤ b →
      |((primesInRealInterval a b).card : ℝ) - (b - a) / Real.log b| ≤
        ε * b / (Real.log b) ^ A + 8 * (b - a) ^ 2 / (b * (Real.log b) ^ 2) := by
  obtain ⟨B, hB, hbase⟩ := rough_base_asymptotic hA hε
  refine ⟨max B 16, hB.trans_le (le_max_left _ _), ?_⟩
  intro b hb a ha hab
  have hbB : B ≤ b := (le_max_left _ _).trans hb
  have hb16 : 16 ≤ b := (le_max_right _ _).trans hb
  have hwa : (roughSquareCutoff b : ℝ) ≤ a := (roughSquareCutoff_le_half hb16).trans ha
  have hs4 : 4 ≤ Real.sqrt b := Real.le_sqrt_of_sq_le (by norm_num; exact hb16)
  have hsw := sqrt_lt_roughSquareCutoff b
  have hw2 : 2 ≤ roughSquareCutoff b := by exact_mod_cast (show (2 : ℝ) ≤
    roughSquareCutoff b by linarith)
  have hsq : b < (roughSquareCutoff b : ℝ) ^ 2 :=
    (Real.sqrt_lt (by linarith : 0 ≤ b) (Nat.cast_nonneg _)).mp hsw
  have h := hbase b hbB a ha hab (roughSquareCutoff b) hw2 (hwa.trans hab) hsq.le
  rw [rough_real_interval_eq_primes (by linarith : 1 ≤ a) hab hwa hsq,
    rough_base_main_identity hw2 (hwa.trans hab), max_eq_left hwa] at h
  exact h

theorem buchstab_count_main_saving (n : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ B > 1, ∀ b : ℝ, B ≤ b → ∀ a : ℝ, b / 2 ≤ a → a ≤ b → ∀ z : ℕ,
      2 ≤ z → (z : ℝ) ≤ Real.sqrt b → b ≤ (z : ℝ) ^ (n + 3) →
      |(b - a) / Real.log b + (b - a) *
        (∑ p ∈ sievePrimes z (roughSquareCutoff b),
          finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)) -
        roughCountMain (n + 1) a b z| ≤ ε * b / (Real.log b) ^ A := by
  obtain ⟨B, hB, hprime⟩ := buchstab_inclusive_prime_main_saving n hA hε
  refine ⟨max B 16, hB.trans_le (le_max_left _ _), ?_⟩
  intro b hb a ha hab z hz hzs hbz
  have hbB : B ≤ b := (le_max_left _ _).trans hb
  have hb16 : 16 ≤ b := (le_max_right _ _).trans hb
  have hLb : 0 < Real.log b := Real.log_pos (by linarith)
  have hza : (z : ℝ) ≤ a :=
    hzs.trans (((sqrt_lt_roughSquareCutoff b).le.trans (roughSquareCutoff_le_half hb16)).trans ha)
  have h := hprime b hbB z hz hzs hbz
  let S : ℝ := ∑ p ∈ sievePrimes z (roughSquareCutoff b),
    finiteBuchstab n (logarithmicBuchstabArgument b p) / ((p : ℝ) * Real.log p)
  have heq : (b - a) / Real.log b + (b - a) * S - roughCountMain (n + 1) a b z =
      (b - a) * (1 / Real.log b + S -
        finiteBuchstab (n + 1) (Real.log b / Real.log z) / Real.log z) := by
    rw [roughCountMain, max_eq_left hza]
    ring
  change |(b - a) / Real.log b + (b - a) * S - roughCountMain (n + 1) a b z| ≤ _
  rw [heq, abs_mul, abs_of_nonneg (sub_nonneg.mpr hab)]
  calc
    _ ≤ (b - a) * (ε / (Real.log b) ^ A) :=
      mul_le_mul_of_nonneg_left h (sub_nonneg.mpr hab)
    _ ≤ b * (ε / (Real.log b) ^ A) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

end Erdos421
