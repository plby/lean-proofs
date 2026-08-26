import ErdosProblems.Erdos421.CanonicalLowerSieve

/-! # Choosing the small sieve cutoff with arbitrarily small relative error -/

namespace Erdos421

theorem exists_transfer_sieve_accuracy {d η : ℝ} (hd : 0 < d) (hη : 0 < η) :
    ∃ ε β : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < β ∧ β < d ∧ ε / β ≤ η ∧
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ d / (2 * β) := by
  let C : ℝ := 16 * Real.exp 1 + 33 + Real.log 32
  have hC : 0 < C := by
    dsimp only [C]
    have hp : 0 < Real.exp 1 := Real.exp_pos 1
    have hl : 0 ≤ Real.log 32 := Real.log_nonneg (by norm_num)
    linarith
  let m : ℝ := max 1 (4 * (C + 3) / (d * η))
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm : 0 < m := by linarith
  have hmlevel : 4 * (C + 3) / (d * η) ≤ m := le_max_right _ _
  let ε : ℝ := (m ^ 2)⁻¹
  let β : ℝ := d / (4 * (C + 2 * m + 1))
  have hden : 0 < 4 * (C + 2 * m + 1) := by positivity
  have hε : 0 < ε := inv_pos.mpr (sq_pos_of_pos hm)
  have hε1 : ε ≤ 1 := by
    apply (inv_le_one₀ (sq_pos_of_pos hm)).mpr
    nlinarith
  have hβ : 0 < β := div_pos hd hden
  have hβd : β < d := by
    apply (div_lt_iff₀ hden).mpr
    have hden1 : 1 < 4 * (C + 2 * m + 1) := by linarith
    nlinarith
  refine ⟨ε, β, hε, hε1, hβ, hβd, ?_, ?_⟩
  · have hnum : C + 2 * m + 1 ≤ (C + 3) * m := by
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hm1)]
    calc
      ε / β = 4 * (C + 2 * m + 1) / (d * m ^ 2) := by
        dsimp only [ε, β]
        field_simp
      _ ≤ 4 * ((C + 3) * m) / (d * m ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (by norm_num))
          (by positivity)
      _ = 4 * (C + 3) / (d * m) := by field_simp
      _ ≤ η := by
        apply (div_le_iff₀ (mul_pos hd hm)).mpr
        have hb := (div_le_iff₀ (mul_pos hd hη)).mp hmlevel
        nlinarith
  · have hlog : Real.log (32 / ε) = Real.log 32 + 2 * Real.log m := by
      dsimp only [ε]
      rw [div_inv_eq_mul, Real.log_mul (by norm_num) (pow_ne_zero 2 hm.ne'), Real.log_pow]
      norm_num
    have hlm := Real.log_le_sub_one_of_pos hm
    have hratio : d / (2 * β) = 2 * (C + 2 * m + 1) := by
      dsimp only [β]
      field_simp
      norm_num
    rw [hlog, hratio]
    dsimp only [C] at hC ⊢
    linarith

end Erdos421
