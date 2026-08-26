import ErdosProblems.Erdos76.PatternRemoval

/-! Finite upward quantization of nonnegative edge-cover weights. -/

namespace Erdos76.CoverQuantization

noncomputable def label (q : ℕ) (z : ℝ) : Fin (q + 1) :=
  ⟨min ⌈(q : ℝ) * z⌉₊ q, Nat.lt_succ_of_le (min_le_right _ _)⟩

noncomputable def value {q : ℕ} (i : Fin (q + 1)) : ℝ := (i.val : ℝ) / q

lemma value_nonneg {q : ℕ} (i : Fin (q + 1)) : 0 ≤ value i := by
  unfold value
  positivity

lemma min_le_value_label {q : ℕ} (hq : 0 < q) (z : ℝ) :
    min z 1 ≤ value (label q z) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  by_cases hceil : ⌈(q : ℝ) * z⌉₊ ≤ q
  · simp only [value, label, min_eq_left hceil]
    apply (min_le_left z 1).trans
    apply (le_div_iff₀ hqr).mpr
    simpa [mul_comm] using Nat.le_ceil ((q : ℝ) * z)
  · have hle : q ≤ ⌈(q : ℝ) * z⌉₊ := (le_of_not_ge hceil)
    simp only [value, label, min_eq_right hle, div_self hqr.ne']
    exact min_le_right z 1

lemma value_label_le_add {q : ℕ} (hq : 0 < q) {z : ℝ} (hz : 0 ≤ z) :
    value (label q z) ≤ z + 1 / (q : ℝ) := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hmin : ((min ⌈(q : ℝ) * z⌉₊ q : ℕ) : ℝ) ≤ ⌈(q : ℝ) * z⌉₊ := by
    exact_mod_cast min_le_left ⌈(q : ℝ) * z⌉₊ q
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hqr.le hz)).le
  unfold value label
  apply (div_le_iff₀ hqr).mpr
  have hmul : (z + 1 / (q : ℝ)) * q = (q : ℝ) * z + 1 := by field_simp
  rw [hmul]
  exact hmin.trans hceil

lemma le_value_of_value_lt_one {q : ℕ} (hq : 0 < q) {z : ℝ}
    (h : value (label q z) < 1) : z ≤ value (label q z) := by
  have hmin := min_le_value_label hq z
  by_cases hz : z ≤ 1
  · simpa [min_eq_left hz] using hmin
  · rw [min_eq_right (le_of_not_ge hz)] at hmin
    linarith

lemma value_sum_lt_of_sum_lt {q : ℕ} (hq : 0 < q) {a b c α : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hstep : 3 / (q : ℝ) ≤ α / 2) (h : a + b + c < 1 - α) :
    value (label q a) + value (label q b) + value (label q c) < 1 - α / 2 := by
  have h₁ := value_label_le_add hq ha
  have h₂ := value_label_le_add hq hb
  have h₃ := value_label_le_add hq hc
  have hdiv : 3 / (q : ℝ) = 3 * (1 / (q : ℝ)) := by ring
  rw [hdiv] at hstep
  linarith

lemma sum_lt_of_value_sum_lt {q : ℕ} (hq : 0 < q) {a b c α : ℝ}
    (hα : 0 < α)
    (h : value (label q a) + value (label q b) + value (label q c) < 1 - α) :
    a + b + c < 1 - α := by
  have h₁ := value_nonneg (label q a)
  have h₂ := value_nonneg (label q b)
  have h₃ := value_nonneg (label q c)
  have ha := le_value_of_value_lt_one hq (z := a) (by linarith)
  have hb := le_value_of_value_lt_one hq (z := b) (by linarith)
  have hc := le_value_of_value_lt_one hq (z := c) (by linarith)
  linarith

end Erdos76.CoverQuantization
