import Mathlib

/-!
# Integer cutoffs for logarithmic prime ranges

The block index is `floor(log R / log p)`. Its upper and lower prime
cutoffs are integer parts of exponentials. Rounding strengthens the
lower logarithmic bound used in the sieve denominator.
-/

namespace Erdos587

noncomputable def deltaLogCutoff (R j : ℕ) : ℕ :=
  Nat.floor (Real.exp (Real.log (R : ℝ) / (j : ℝ)))

lemma deltaLogCutoff_pos {R : ℕ} (hR : 1 ≤ R) (j : ℕ) : 0 < deltaLogCutoff R j := by
  apply Nat.lt_of_lt_of_le Nat.zero_lt_one
  apply Nat.le_floor
  have hnonneg : 0 ≤ Real.log (R : ℝ) / (j : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hR)) (by positivity)
  simpa only [Real.exp_zero, Nat.cast_one] using Real.exp_le_exp.mpr hnonneg

lemma deltaLogCutoff_log_le {R : ℕ} (hR : 1 ≤ R) (j : ℕ) :
    Real.log (deltaLogCutoff R j : ℝ) ≤ Real.log (R : ℝ) / (j : ℝ) := by
  have hpos : (0 : ℝ) < deltaLogCutoff R j := by exact_mod_cast deltaLogCutoff_pos hR j
  have h := Real.log_le_log hpos (Nat.floor_le (Real.exp_nonneg (Real.log (R : ℝ) / j)))
  rwa [Real.log_exp] at h

lemma deltaLogCutoff_succ_log_gt (R j : ℕ) :
    Real.log (R : ℝ) / (j : ℝ) < Real.log (deltaLogCutoff R j + 1 : ℕ) := by
  have h := Real.log_lt_log (Real.exp_pos (Real.log (R : ℝ) / j))
    (Nat.lt_floor_add_one (Real.exp (Real.log (R : ℝ) / j)))
  rw [Real.log_exp] at h
  simpa only [deltaLogCutoff, Nat.cast_add, Nat.cast_one] using h

lemma deltaLogCutoff_le {R j : ℕ} (hR : 1 ≤ R) (hj : 1 ≤ j) : deltaLogCutoff R j ≤ R := by
  have hlogR : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hdiv : Real.log (R : ℝ) / (j : ℝ) ≤ Real.log (R : ℝ) :=
    div_le_self hlogR (by exact_mod_cast hj)
  have hcast : (deltaLogCutoff R j : ℝ) ≤ R := by
    calc
      _ ≤ Real.exp (Real.log (R : ℝ) / j) := Nat.floor_le (Real.exp_nonneg _)
      _ ≤ Real.exp (Real.log (R : ℝ)) := Real.exp_le_exp.mpr hdiv
      _ = _ := Real.exp_log hRpos
  exact_mod_cast hcast

lemma deltaLogCutoff_next_sq_le {R j : ℕ} (hR : 1 ≤ R) (hj : 1 ≤ j) :
    deltaLogCutoff R (j + 1) ^ 2 ≤ R := by
  have hQpos : (0 : ℝ) < deltaLogCutoff R (j + 1) := by
    exact_mod_cast deltaLogCutoff_pos hR (j + 1)
  have hlogQ : 0 ≤ Real.log (deltaLogCutoff R (j + 1) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast deltaLogCutoff_pos hR (j + 1))
  have hupper := (le_div_iff₀ (by positivity : (0 : ℝ) < (j + 1 : ℕ))).mp
    (deltaLogCutoff_log_le hR (j + 1))
  have hjR : (2 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast (show 2 ≤ j + 1 by omega)
  have htwice : 2 * Real.log (deltaLogCutoff R (j + 1) : ℝ) ≤ Real.log (R : ℝ) := by
    nlinarith
  have hexp := Real.exp_le_exp.mpr htwice
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hQpos,
    Real.exp_log (by exact_mod_cast (show 0 < R by omega))] at hexp
  exact_mod_cast hexp

lemma deltaLogCutoff_sieve_size {R Y j : ℕ} (hR : 1 ≤ R) (hj : 1 ≤ j) (hY : R ^ 4 ≤ Y) :
    R ^ 2 * deltaLogCutoff R (j + 1) ^ 2 ≤ Y := by
  calc
    _ ≤ R ^ 2 * R := Nat.mul_le_mul_left _ (deltaLogCutoff_next_sq_le hR hj)
    _ = R ^ 3 := by ring
    _ ≤ R ^ 4 := Nat.pow_le_pow_right hR (by norm_num)
    _ ≤ Y := hY

theorem delta_prime_log_block {R p : ℕ} (hp : p.Prime) (hpR : p ≤ R) :
    let j := Nat.floor (Real.log (R : ℝ) / Real.log (p : ℝ))
    1 ≤ j ∧ j ≤ Nat.floor (Real.log (R : ℝ) / Real.log 2) ∧
      p ≤ deltaLogCutoff R j ∧ deltaLogCutoff R (j + 1) < p := by
  dsimp only
  let j := Nat.floor (Real.log (R : ℝ) / Real.log (p : ℝ))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlogR : 0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le.trans hpR)
  have hlogpR : Real.log (p : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log hp0 (by exact_mod_cast hpR)
  have hratio1 : (1 : ℝ) ≤ Real.log (R : ℝ) / Real.log (p : ℝ) :=
    (le_div_iff₀ hlogp).mpr (by simpa only [one_mul] using hlogpR)
  have hj : 1 ≤ j := Nat.le_floor (by simpa only [Nat.cast_one] using hratio1)
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hlow : (j : ℝ) ≤ Real.log (R : ℝ) / Real.log (p : ℝ) :=
    Nat.floor_le (by positivity)
  have hupp : Real.log (R : ℝ) / Real.log (p : ℝ) < (j : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨hj, ?_, ?_, ?_⟩
  · apply Nat.floor_mono
    apply div_le_div_of_nonneg_left hlogR (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  · apply Nat.le_floor
    have hlog : Real.log (p : ℝ) ≤ Real.log (R : ℝ) / (j : ℝ) := by
      apply (le_div_iff₀ hjpos).mpr
      have h := (le_div_iff₀ hlogp).mp hlow
      nlinarith
    calc
      _ = Real.exp (Real.log (p : ℝ)) := (Real.exp_log hp0).symm
      _ ≤ _ := Real.exp_le_exp.mpr hlog
  · have hjnext : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    have hlog : Real.log (R : ℝ) / ((j + 1 : ℕ) : ℝ) < Real.log (p : ℝ) := by
      apply (div_lt_iff₀ hjnext).mpr
      have h := (div_lt_iff₀ hlogp).mp hupp
      push_cast
      nlinarith
    have hcast : (deltaLogCutoff R (j + 1) : ℝ) < p := by
      calc
        _ ≤ Real.exp (Real.log (R : ℝ) / ((j + 1 : ℕ) : ℝ)) := Nat.floor_le (Real.exp_nonneg _)
        _ < Real.exp (Real.log (p : ℝ)) := Real.exp_lt_exp.mpr hlog
        _ = _ := Real.exp_log hp0
    exact_mod_cast hcast

/-- The Rankin saving dominates the rough-cofactor cost on each block.
The remaining block weight is the summable geometric weight `exp (-j)`. -/
lemma delta_log_block_decay {x z q H k j E : ℝ} (hz : 0 < z) (hq : 0 < q)
    (hH0 : 0 ≤ H) (hk : 0 ≤ k) (hj : 0 ≤ j)
    (hH : H ≤ 2 * k * x) (hcutq : x ≤ (j + 1) * q) (hcutz : j * z ≤ x) :
    (H / q) * Real.exp (Real.log 2 * H / q + E - (2 * k + 2) * x / z) ≤
      2 * k * Real.exp (E + 2 * k) * Real.exp (-j) := by
  have hratio : H / q ≤ 2 * k * (j + 1) := by
    apply (div_le_iff₀ hq).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcutq (by positivity : 0 ≤ 2 * k)]
  have hratio0 : 0 ≤ H / q := div_nonneg hH0 hq.le
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hcost : Real.log 2 * H / q ≤ 2 * k * (j + 1) := by
    calc
      _ = Real.log 2 * (H / q) := by ring
      _ ≤ 1 * (H / q) := mul_le_mul_of_nonneg_right hlog2 hratio0
      _ ≤ _ := by simpa only [one_mul] using hratio
  have hsaving : (2 * k + 2) * j ≤ (2 * k + 2) * x / z := by
    apply (le_div_iff₀ hz).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcutz (by positivity : 0 ≤ 2 * k + 2)]
  have hexp : Real.exp (Real.log 2 * H / q + E - (2 * k + 2) * x / z) ≤
      Real.exp (E + 2 * k - 2 * j) := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ (2 * k * (j + 1)) * Real.exp (E + 2 * k - 2 * j) :=
      mul_le_mul hratio hexp (Real.exp_nonneg _) (by positivity)
    _ = (2 * k * Real.exp (E + 2 * k)) * ((j + 1) * Real.exp (-2 * j)) := by
      rw [show E + 2 * k - 2 * j = (E + 2 * k) + (-2 * j) by ring, Real.exp_add]
      ring
    _ ≤ (2 * k * Real.exp (E + 2 * k)) * (Real.exp j * Real.exp (-2 * j)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.add_one_le_exp j) (Real.exp_nonneg _)) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, show j + -2 * j = -j by ring]


end Erdos587
