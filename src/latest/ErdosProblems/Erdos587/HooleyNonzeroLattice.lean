import ErdosProblems.Erdos587.LatticeBounds

/-! # A nonzero Fourier-lattice tail with square decay in the spacing -/

namespace Erdos587

theorem delta_nonzero_lattice_decay_bound {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun n : ℤ => if n = 0 then (0 : ℝ) else 1 / (1 + σ * |(n : ℝ)|) ^ 2) ∧
      (∑' n : ℤ, if n = 0 then (0 : ℝ) else 1 / (1 + σ * |(n : ℝ)|) ^ 2) ≤ 20 / σ ^ 2 := by
  classical
  obtain ⟨hbase, hbaseBound⟩ :=
    normalized_lattice_kernel_bound (by norm_num : (0 : ℝ) < 1) le_rfl
  simp only [one_mul] at hbase hbaseBound
  let f := fun n : ℤ => if n = 0 then (0 : ℝ) else 1 / (1 + σ * |(n : ℝ)|) ^ 2
  have hf (n : ℤ) : 0 ≤ f n := by dsimp only [f]; split_ifs <;> positivity
  have hpoint (n : ℤ) : f n ≤ (4 / σ ^ 2) * (1 / (1 + |(n : ℝ)|) ^ 2) := by
    by_cases hn : n = 0
    · simp only [f, if_pos hn]
      positivity
    · simp only [f, if_neg hn]
      have hgap : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hlinear : σ * (1 + |(n : ℝ)|) ≤ 2 * (1 + σ * |(n : ℝ)|) := by
        nlinarith [mul_le_mul_of_nonneg_left hgap hσ.le]
      have hsquare := pow_le_pow_left₀ (by positivity) hlinear 2
      calc
        _ ≤ 4 / (σ ^ 2 * (1 + |(n : ℝ)|) ^ 2) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith
        _ = _ := by field_simp
  have hsum : Summable f :=
    Summable.of_nonneg_of_le hf hpoint (hbase.mul_left (4 / σ ^ 2))
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' n : ℤ, (4 / σ ^ 2) * (1 / (1 + |(n : ℝ)|) ^ 2) :=
      hsum.tsum_le_tsum hpoint (hbase.mul_left (4 / σ ^ 2))
    _ = (4 / σ ^ 2) * ∑' n : ℤ, 1 / (1 + |(n : ℝ)|) ^ 2 := tsum_mul_left
    _ ≤ (4 / σ ^ 2) * 5 := mul_le_mul_of_nonneg_left hbaseBound (by positivity)
    _ = _ := by ring

end Erdos587
