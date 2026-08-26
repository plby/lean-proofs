import ErdosProblems.Erdos1148.FixedZeroLowerBound
import ErdosProblems.Erdos1148.RealDirichletPolynomialAlternative

/-! # Siegel's ineffective lower bound for primitive real Dirichlet characters -/

namespace Erdos1148.DukeArithmetic

theorem exists_primitive_realDirichlet_siegel_lower_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℝ q),
      χ.IsPrimitive → χ ≠ 1 → c * (q : ℝ) ^ (-ε) ≤ realDirichletValue χ 1 := by
  classical
  let δ := min (1 / 16 : ℝ) (ε / 64)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ16 : δ ≤ 1 / 16 := min_le_left _ _
  have hδε : δ ≤ ε / 64 := min_le_right _ _
  by_cases hbad : ∃ (q : ℕ) (χ : DirichletCharacter ℝ q),
      0 < q ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧
        ∃ β : ℝ, 1 - δ ≤ β ∧ β < 1 ∧ realDirichletValue χ β = 0
  · obtain ⟨q, χ, hq, hχprim, hχ, β, hβ, hβ1, hzero⟩ := hbad
    let : NeZero q := ⟨Nat.ne_zero_of_lt hq⟩
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    obtain ⟨C, hC, hbound⟩ := exists_fixedZero_lower_bound χ hχ
      (by linarith : 15 / 16 ≤ β) hβ1 hzero hε (by linarith : 32 * (1 - β) ≤ ε)
    let c0 := realDirichletValue χ 1 * (q : ℝ) ^ ε
    have hc0 : 0 < c0 := mul_pos (realDirichletValue_one_pos χ hχ) (Real.rpow_pos_of_pos hq0 _)
    refine ⟨min C c0, lt_min hC hc0, ?_⟩
    intro r hr ψ hψprim hψ
    let : NeZero r := ⟨Nat.ne_zero_of_lt hr⟩
    by_cases hqr : q = r
    · subst r
      by_cases hψχ : ψ = χ
      · subst ψ
        calc
          _ ≤ c0 * (q : ℝ) ^ (-ε) :=
            mul_le_mul_of_nonneg_right (min_le_right C c0) (by positivity)
          _ = _ := by
            dsimp only [c0]
            rw [mul_assoc, ← Real.rpow_add hq0, add_neg_cancel, Real.rpow_zero, mul_one]
      · exact (mul_le_mul_of_nonneg_right (min_le_left C c0) (by positivity)).trans
          (hbound q hq ψ hψ (productDirichletCharacter_ne_one_of_ne χ ψ (Ne.symm hψχ)))
    · exact (mul_le_mul_of_nonneg_right (min_le_left C c0) (by positivity)).trans
        (hbound r hr ψ hψ
          (productDirichletCharacter_ne_one_of_primitive_moduli_ne χ ψ hχprim hψprim hqr))
  · obtain ⟨c, hc, hbound⟩ := realDirichlet_polynomial_lower_bound_or_zero hδ (by linarith)
    refine ⟨c, hc, ?_⟩
    intro q hq χ hχprim hχ
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    rcases hbound q hq χ hχ with hgood | ⟨β, hβ, hβ1, hzero⟩
    · calc
        _ ≤ c * (q : ℝ) ^ (-(4 * δ)) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)) hc.le
        _ ≤ _ := hgood
    · exact (hbad ⟨q, χ, hq, hχprim, hχ, β, hβ, hβ1, hzero⟩).elim

end Erdos1148.DukeArithmetic
