import ErdosProblems.Erdos941.SquareConvolutionSum
import ErdosProblems.Erdos941.CoprimeConvolutionAsymptotic

/-! # From the quadratic-character mean to a uniform sphere-count lower bound -/

namespace Erdos941

open ArithmeticFunction Finset Analytic Filter Topology

theorem root_square_sum_bound {n : ℕ} {A K H : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hroot : ∀ X : ℕ, (allRootCount n X : ℝ) ≤ A * X + K * Real.sqrt X + H)
    (N : ℕ) :
    (∑ a ∈ Ioc 0 (N ^ 2),
      ((allRootCoefficient n : ArithmeticFunction ℝ) * (squareIndicator : ArithmeticFunction ℝ)) a) ≤
      2 * A * (N : ℝ) ^ 2 + K * N * Real.sqrt (2 * N) + H * N := by
  rw [sum_square_convolution]
  have hpoint (c : ℕ) (hc : c ∈ Ioc 0 N) :
      (allRootCount n (N ^ 2 / c ^ 2) : ℝ) ≤
        A * (N : ℝ) ^ 2 * ((c : ℝ)⁻¹) ^ 2 + K * N * (c : ℝ)⁻¹ + H := by
    have hc0 : (0 : ℝ) < c := by exact_mod_cast (mem_Ioc.mp hc).1
    have hdiv : ((N ^ 2 / c ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 / (c : ℝ) ^ 2 := by
      exact_mod_cast (Nat.cast_div_le (α := ℝ) (m := N ^ 2) (n := c ^ 2))
    have hsqrt : Real.sqrt ((N ^ 2 / c ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / c := by
      apply (Real.sqrt_le_left (div_nonneg (Nat.cast_nonneg N) hc0.le)).mpr
      simpa only [div_pow] using hdiv
    calc
      _ ≤ A * ((N ^ 2 / c ^ 2 : ℕ) : ℝ) + K * Real.sqrt ((N ^ 2 / c ^ 2 : ℕ) : ℝ) + H :=
        hroot _
      _ ≤ A * ((N : ℝ) ^ 2 / (c : ℝ) ^ 2) + K * ((N : ℝ) / c) + H := by
        gcongr
      _ = _ := by simp only [div_eq_mul_inv, inv_pow]; ring
  calc
    _ = ∑ c ∈ Ioc 0 N, (allRootCount n (N ^ 2 / c ^ 2) : ℝ) := by
      apply sum_congr rfl
      intro c hc
      exact (allRootCount_eq_sum_Ioc_real _ _).symm
    _ ≤ ∑ c ∈ Ioc 0 N,
        (A * (N : ℝ) ^ 2 * ((c : ℝ)⁻¹) ^ 2 + K * N * (c : ℝ)⁻¹ + H) :=
      sum_le_sum hpoint
    _ = A * (N : ℝ) ^ 2 * (∑ c ∈ Ioc 0 N, ((c : ℝ)⁻¹) ^ 2) +
        K * N * (∑ c ∈ Ioc 0 N, (c : ℝ)⁻¹) + H * N := by
      simp only [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero,
        nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have h1 := mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le_two N)
        (mul_nonneg hA (sq_nonneg (N : ℝ)))
      have h2 := mul_le_mul_of_nonneg_left (sum_inv_Ioc_le_sqrt N)
        (mul_nonneg hK (Nat.cast_nonneg N))
      nlinarith

theorem root_square_mean_bound {n : ℕ} {A K H : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hroot : ∀ X : ℕ, (allRootCount n X : ℝ) ≤ A * X + K * Real.sqrt X + H)
    {N : ℕ} (hN : 0 < N) :
    (∑ a ∈ Ioc 0 (N ^ 2),
      ((allRootCoefficient n : ArithmeticFunction ℝ) * (squareIndicator : ArithmeticFunction ℝ)) a) /
      (N : ℝ) ^ 2 ≤ 2 * A + K * Real.sqrt (2 / N) + H / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : Real.sqrt (2 * (N : ℝ)) / N = Real.sqrt (2 / N) := by
    calc
      _ = Real.sqrt (2 * (N : ℝ)) / Real.sqrt ((N : ℝ) ^ 2) := by rw [Real.sqrt_sq hNR.le]
      _ = Real.sqrt ((2 * (N : ℝ)) / (N : ℝ) ^ 2) :=
        (Real.sqrt_div (by positivity) _).symm
      _ = _ := by congr 1; field_simp
  have he : (2 * A * (N : ℝ) ^ 2 + K * N * Real.sqrt (2 * N) + H * N) /
      (N : ℝ) ^ 2 = 2 * A + K * Real.sqrt (2 / N) + H / N := by
    rw [show (2 * A * (N : ℝ) ^ 2 + K * N * Real.sqrt (2 * N) + H * N) /
        (N : ℝ) ^ 2 = 2 * A + K * (Real.sqrt (2 * N) / N) + H / N by field_simp]
    rw [hsqrt]
  exact (div_le_div_of_nonneg_right (root_square_sum_bound hA hK hroot N)
    (sq_nonneg (N : ℝ))).trans_eq he

theorem principalMean_mul_LValue_le_sphere {v : Triple} {n : ℕ} [NeZero n] (hn : 0 < n)
    (hv : tripleNorm v = n) (hp : PrimitiveTriple v) :
    principalCharacterMean (4 * n) * ((negativeQuadraticCharacter n).LFunction 1).re ≤
      16 * (sphereCount n : ℝ) / Real.sqrt (n : ℝ) := by
  let A : ℝ := 8 * (sphereCount n : ℝ) / Real.sqrt (n : ℝ)
  obtain ⟨K, hK, hcount⟩ := allRootCount_bound hn hv hp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hroot (X : ℕ) : (allRootCount n X : ℝ) ≤
      A * X + K * Real.sqrt X + (sphereCount n : ℝ) := by
    convert hcount X using 1 <;> dsimp [A] <;> ring
  have hlim := coprime_convolution_sum_div_sq_tendsto
    (realNegativeQuadraticCharacter n) (realNegativeQuadraticCharacter_ne_one n)
  rw [realNegativeDirichletValue_eq] at hlim
  have hupper : Tendsto (fun N : ℕ => 2 * A + K * Real.sqrt (2 / (N : ℝ)) +
      (sphereCount n : ℝ) / N) atTop (𝓝 (2 * A)) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).sqrt.const_mul K
    simpa only [Real.sqrt_zero, mul_zero, add_zero] using
      (tendsto_const_nhds.add h0).add
        (tendsto_const_div_atTop_nhds_zero_nat (sphereCount n : ℝ))
  have hle : principalCharacterMean (4 * n) * ((negativeQuadraticCharacter n).LFunction 1).re ≤
      2 * A := by
    apply le_of_tendsto_of_tendsto hlim hupper
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hs := sum_le_sum (s := Ioc 0 (N ^ 2))
      (fun a _ => coprime_convolution_le_root_square n a)
    have hb := root_square_mean_bound hA hK hroot hN
    rw [pow_two N] at hs hb
    exact (div_le_div_of_nonneg_right hs (sq_nonneg (N : ℝ))).trans hb
  convert hle using 1 <;> dsimp [A] <;> ring

end Erdos941
