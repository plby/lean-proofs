import ErdosProblems.Erdos336.ProjectionLargeFiber

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise

/-- Division-free arithmetic core of the two-piece estimate. -/
theorem two_piece_projection_arithmetic
    (n₁ n₂ a₁ a₂ d₁ d₁₂ d₂ : ℕ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hd₁ : n₁ * d₁ ≥ (2 * n₁ - 1) * a₁)
    (hd₂ : n₂ * d₂ ≥ (2 * n₂ - 1) * a₂)
    (hlarge₁ : n₁ * d₁₂ ≥ (n₁ + n₂ - 1) * a₁)
    (hlarge₂ : n₂ * d₁₂ ≥ (n₁ + n₂ - 1) * a₂) :
    (n₁ + n₂) * (d₁ + d₁₂ + d₂) ≥
      3 * (n₁ + n₂ - 1) * (a₁ + a₂) := by
  let qn₁ : ℚ := n₁
  let qn₂ : ℚ := n₂
  let qa₁ : ℚ := a₁
  let qa₂ : ℚ := a₂
  let qd₁ : ℚ := d₁
  let qd₁₂ : ℚ := d₁₂
  let qd₂ : ℚ := d₂
  have hn₁q : (0 : ℚ) < qn₁ := by
    change (0 : ℚ) < (n₁ : ℚ)
    exact_mod_cast hn₁
  have hn₂q : (0 : ℚ) < qn₂ := by
    change (0 : ℚ) < (n₂ : ℚ)
    exact_mod_cast hn₂
  have hn₁one : (1 : ℚ) ≤ qn₁ := by
    change (1 : ℚ) ≤ (n₁ : ℚ)
    exact_mod_cast (show 1 ≤ n₁ by omega)
  have hn₂one : (1 : ℚ) ≤ qn₂ := by
    change (1 : ℚ) ≤ (n₂ : ℚ)
    exact_mod_cast (show 1 ≤ n₂ by omega)
  have hnq : (0 : ℚ) < qn₁ + qn₂ := by positivity
  have hn₁ne : qn₁ ≠ 0 := ne_of_gt hn₁q
  have hn₂ne : qn₂ ≠ 0 := ne_of_gt hn₂q
  have hnne : qn₁ + qn₂ ≠ 0 := ne_of_gt hnq
  have hd₁q : qd₁ ≥ (2 - 1 / qn₁) * qa₁ := by
    have hc : (((2 * n₁ - 1 : ℕ) : ℚ) * qa₁) ≤ qn₁ * qd₁ := by
      change ((2 * n₁ - 1 : ℕ) : ℚ) * (a₁ : ℚ) ≤
        (n₁ : ℚ) * (d₁ : ℚ)
      exact_mod_cast hd₁
    have hid : (2 : ℚ) - 1 / qn₁ =
        ((2 * n₁ - 1 : ℕ) : ℚ) / qn₁ := by
      dsimp [qn₁]
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n₁), Nat.cast_mul]
      norm_num
      field_simp
    rw [hid, div_mul_eq_mul_div]
    exact (div_le_iff₀ hn₁q).mpr (by simpa [mul_comm] using hc)
  have hd₂q : qd₂ ≥ (2 - 1 / qn₂) * qa₂ := by
    have hc : (((2 * n₂ - 1 : ℕ) : ℚ) * qa₂) ≤ qn₂ * qd₂ := by
      change ((2 * n₂ - 1 : ℕ) : ℚ) * (a₂ : ℚ) ≤
        (n₂ : ℚ) * (d₂ : ℚ)
      exact_mod_cast hd₂
    have hid : (2 : ℚ) - 1 / qn₂ =
        ((2 * n₂ - 1 : ℕ) : ℚ) / qn₂ := by
      dsimp [qn₂]
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n₂), Nat.cast_mul]
      norm_num
      field_simp
    rw [hid, div_mul_eq_mul_div]
    exact (div_le_iff₀ hn₂q).mpr (by simpa [mul_comm] using hc)
  have hlarge₁q : qd₁₂ ≥ ((qn₁ + qn₂ - 1) / qn₁) * qa₁ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hn₁q).mpr
    have hc : (((n₁ + n₂ - 1 : ℕ) : ℚ) * qa₁) ≤ qn₁ * qd₁₂ := by
      change ((n₁ + n₂ - 1 : ℕ) : ℚ) * (a₁ : ℚ) ≤
        (n₁ : ℚ) * (d₁₂ : ℚ)
      exact_mod_cast hlarge₁
    dsimp [qn₁, qn₂] at hc ⊢
    rw [Nat.cast_sub (by omega : 1 ≤ n₁ + n₂)] at hc
    simpa [mul_comm] using hc
  have hlarge₂q : qd₁₂ ≥ ((qn₁ + qn₂ - 1) / qn₂) * qa₂ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hn₂q).mpr
    have hc : (((n₁ + n₂ - 1 : ℕ) : ℚ) * qa₂) ≤ qn₂ * qd₁₂ := by
      change ((n₁ + n₂ - 1 : ℕ) : ℚ) * (a₂ : ℚ) ≤
        (n₂ : ℚ) * (d₁₂ : ℚ)
      exact_mod_cast hlarge₂
    dsimp [qn₁, qn₂] at hc ⊢
    rw [Nat.cast_sub (by omega : 1 ≤ n₁ + n₂)] at hc
    simpa [mul_comm] using hc
  have combine (hneeded : qd₁₂ ≥
      (1 + 1 / qn₁ - 3 / (qn₁ + qn₂)) * qa₁ +
      (1 + 1 / qn₂ - 3 / (qn₁ + qn₂)) * qa₂) :
      qd₁ + qd₁₂ + qd₂ ≥
        3 * (1 - 1 / (qn₁ + qn₂)) * (qa₁ + qa₂) := by
    calc
      3 * (1 - 1 / (qn₁ + qn₂)) * (qa₁ + qa₂) =
          (2 - 1 / qn₁) * qa₁ + (2 - 1 / qn₂) * qa₂ +
            ((1 + 1 / qn₁ - 3 / (qn₁ + qn₂)) * qa₁ +
             (1 + 1 / qn₂ - 3 / (qn₁ + qn₂)) * qa₂) := by ring
      _ ≤ qd₁ + qd₂ + qd₁₂ := by gcongr
      _ = qd₁ + qd₁₂ + qd₂ := by ring
  have hqfinal : qd₁ + qd₁₂ + qd₂ ≥
      3 * (1 - 1 / (qn₁ + qn₂)) * (qa₁ + qa₂) := by
    by_cases hdensity : qa₂ * qn₁ ≤ qa₁ * qn₂
    · apply combine
      have hc : 0 ≤ (qn₁ + qn₂) * qn₂ + (qn₁ + qn₂) - 3 * qn₂ := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hn₁one) (sub_nonneg.mpr hn₂one)]
      have hp : 0 ≤
          ((qn₁ + qn₂) * qn₂ + (qn₁ + qn₂) - 3 * qn₂) *
            (qa₁ * qn₂ - qa₂ * qn₁) :=
        mul_nonneg hc (sub_nonneg.mpr hdensity)
      have hcoef :
          (1 + 1 / qn₁ - 3 / (qn₁ + qn₂)) * qa₁ +
          (1 + 1 / qn₂ - 3 / (qn₁ + qn₂)) * qa₂ ≤
            ((qn₁ + qn₂ - 1) / qn₁) * qa₁ := by
        field_simp
        nlinarith
      exact le_trans hcoef hlarge₁q
    · apply combine
      have hdensity' : qa₁ * qn₂ ≤ qa₂ * qn₁ := by linarith
      have hc : 0 ≤ (qn₁ + qn₂) * qn₁ + (qn₁ + qn₂) - 3 * qn₁ := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hn₁one) (sub_nonneg.mpr hn₂one)]
      have hp : 0 ≤
          ((qn₁ + qn₂) * qn₁ + (qn₁ + qn₂) - 3 * qn₁) *
            (qa₂ * qn₁ - qa₁ * qn₂) :=
        mul_nonneg hc (sub_nonneg.mpr hdensity')
      have hcoef :
          (1 + 1 / qn₁ - 3 / (qn₁ + qn₂)) * qa₁ +
          (1 + 1 / qn₂ - 3 / (qn₁ + qn₂)) * qa₂ ≤
            ((qn₁ + qn₂ - 1) / qn₂) * qa₂ := by
        field_simp
        nlinarith
      exact le_trans hcoef hlarge₂q
  have hmul := mul_le_mul_of_nonneg_left hqfinal hnq.le
  have hleftIdentity :
      (qn₁ + qn₂) *
        (3 * (1 - 1 / (qn₁ + qn₂)) * (qa₁ + qa₂)) =
      (3 * (n₁ + n₂ - 1) * (a₁ + a₂) : ℕ) := by
    dsimp [qn₁, qn₂, qa₁, qa₂]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n₁ + n₂)]
    field_simp
    push_cast
    ring
  have hrightIdentity :
      (qn₁ + qn₂) * (qd₁ + qd₁₂ + qd₂) =
      (((n₁ + n₂) * (d₁ + d₁₂ + d₂) : ℕ) : ℚ) := by
    dsimp [qn₁, qn₂, qd₁, qd₁₂, qd₂]
    push_cast
    ring
  rw [hleftIdentity, hrightIdentity] at hmul
  exact_mod_cast hmul

/-- Lev's sharp two-piece estimate in `ℤ × H`. -/
theorem projection_two_piece_bound
    {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A₁ A₂ : Finset (ℤ × H)) (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) :
    let n₁ := (A₁.image Prod.fst).card
    let n₂ := (A₂.image Prod.fst).card
    (n₁ + n₂) * ((A₁ + A₁).card + (A₁ + A₂).card + (A₂ + A₂).card) ≥
      3 * (n₁ + n₂ - 1) * (A₁.card + A₂.card) := by
  dsimp
  apply two_piece_projection_arithmetic
  · exact (hA₁.image Prod.fst).card_pos
  · exact (hA₂.image Prod.fst).card_pos
  · exact projection_kneser_double_bound A₁ hA₁
  · exact projection_kneser_double_bound A₂ hA₂
  · exact projection_large_fiber_bound A₁ A₂ hA₁ hA₂
  · simpa [add_comm] using projection_large_fiber_bound A₂ A₁ hA₂ hA₁

end Erdos336
