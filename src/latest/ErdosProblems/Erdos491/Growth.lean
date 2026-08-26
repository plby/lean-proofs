import ErdosProblems.Erdos491.Basic

/-! # Logarithmic growth and positivity for completely additive functions -/

namespace Erdos491

lemma PosCompletelyAdditive.exists_log_bound
    {g : ℕ → ℝ} (hg : PosCompletelyAdditive g) {K : ℝ} (hK : 0 ≤ K)
    (hgap : ∀ n : ℕ, 0 < n → |g (n + 1) - g n| ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → |g n| ≤ C * Real.log (n : ℝ) := by
  let K₀ := K + |g 1 - g 0|
  have hK₀ : 0 ≤ K₀ := add_nonneg hK (abs_nonneg _)
  have hgap₀ (n : ℕ) : |g (n + 1) - g n| ≤ K₀ := by
    cases n with
    | zero => dsimp [K₀]; linarith
    | succ n => exact (hgap (n + 1) (by omega)).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let D := (|g 2| + K₀) / Real.log (2 : ℝ)
  have hD : 0 ≤ D := div_nonneg (add_nonneg (abs_nonneg _) hK₀) hlog2.le
  refine ⟨D + 1, by linarith, fun n hn ↦ ?_⟩
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  calc
    |g n| ≤ (Nat.log 2 n : ℝ) * (|g 2| + K₀) :=
      hg.abs_le_natLog_two_mul hK₀ hgap₀ n hn
    _ ≤ Real.logb 2 (n : ℝ) * (|g 2| + K₀) :=
      mul_le_mul_of_nonneg_right (Real.natLog_le_logb n 2)
        (add_nonneg (abs_nonneg _) hK₀)
    _ = D * Real.log (n : ℝ) := by dsimp [D, Real.logb]; ring
    _ ≤ (D + 1) * Real.log (n : ℝ) := by nlinarith

lemma PosCompletelyAdditive.nonneg_of_prime
    {g : ℕ → ℝ} (hg : PosCompletelyAdditive g)
    (hp : ∀ p : ℕ, p.Prime → 0 ≤ g p) :
    ∀ n : ℕ, 0 < n → 0 ≤ g n := by
  intro n
  induction n using Nat.recOnPrimeCoprime with
  | zero => simp
  | prime_pow p k hprime =>
      intro _
      rw [hg.pow hprime.pos]
      exact mul_nonneg (Nat.cast_nonneg _) (hp p hprime)
  | coprime a b ha hb _ hia hib =>
      intro _
      rw [hg (by omega) (by omega)]
      exact add_nonneg (hia (by omega)) (hib (by omega))

lemma PosCompletelyAdditive.le_of_dvd
    {g : ℕ → ℝ} (hg : PosCompletelyAdditive g)
    (hnonneg : ∀ n : ℕ, 0 < n → 0 ≤ g n)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) : g a ≤ g b := by
  obtain ⟨d, rfl⟩ := hab
  have hd : 0 < d := Nat.pos_of_mul_pos_left hb
  rw [hg ha hd]
  exact le_add_of_nonneg_right (hnonneg d hd)

lemma log_forward_difference_bound (n : ℕ) (hn : 0 < n) :
    |Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)| ≤ Real.log 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
    apply sub_nonneg.mpr
    exact Real.log_le_log hnR (by norm_num)
  rw [abs_of_nonneg hpos]
  have hle : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h := Real.log_le_log (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) hle
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR.ne'] at h
  linarith

lemma sub_log_forward_difference_bound
    {g : ℕ → ℝ} {K : ℝ}
    (hgap : ∀ n : ℕ, 0 < n → |g (n + 1) - g n| ≤ K) (c : ℝ)
    (n : ℕ) (hn : 0 < n) :
    |(g (n + 1) - c * Real.log ((n + 1 : ℕ) : ℝ)) -
        (g n - c * Real.log (n : ℝ))| ≤ K + |c| * Real.log 2 := by
  calc
    _ = |(g (n + 1) - g n) -
        c * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))| := by congr 1; ring
    _ ≤ |g (n + 1) - g n| +
        |c * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ))| := abs_sub _ _
    _ ≤ K + |c| * Real.log 2 := by
      rw [abs_mul]
      exact add_le_add (hgap n hn)
        (mul_le_mul_of_nonneg_left (log_forward_difference_bound n hn) (abs_nonneg c))

end Erdos491
