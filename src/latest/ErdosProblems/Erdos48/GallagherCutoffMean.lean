import ErdosProblems.Erdos48.AdaptiveDetectorBand

open scoped BigOperators

noncomputable section

namespace Erdos48

open Complex

/-- The coefficient in Gallagher's unweighted cutoff polynomial. -/
noncomputable def cutoffVonMangoldtCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n * (n : ℝ)⁻¹ : ℝ)

theorem cutoffVonMangoldtCoefficient_eq_weighted (n : ℕ) :
    cutoffVonMangoldtCoefficient n =
      (weightedVonMangoldtMajorant 0 0 n : ℂ) := by
  simp [cutoffVonMangoldtCoefficient, weightedVonMangoldtMajorant,
    Real.rpow_neg_one]

/-- The logarithmically weighted family of all cutoff partial sums.  After
unfolding `primitiveNegativeDirichletMass`, its `m`-th summand is
`m⁻¹` times the primitive-character mean square of
`sum_{A < n ≤ m} Lambda(n) chi(n) n⁻¹ n^{-it}`. -/
noncomputable def primitiveCutoffVonMangoldtEnergy
    (Q A N : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
    primitiveNegativeDirichletMass Q (Finset.Ioc A m)
      cutoffVonMangoldtCoefficient t

private theorem intervalIntegral_cutoffVonMangoldt_le
    (Q A N T m : ℕ) (hA : 1 ≤ A)
    (hheight : 4 * (T + 1) ≤ A)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ A)
    (hm : m ≤ N) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc A m)
          cutoffVonMangoldtCoefficient t) ≤
      4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2 := by
  let M : ℕ := Nat.log 2 (N - 1) + 1
  let C : ℝ := 4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4)
  have hmain := intervalIntegral_weightedDetectorBand_adaptive_le
    Q A m T 0 hA hheight hconductor 0 (by positivity)
  rw [show (fun n ↦ (weightedVonMangoldtMajorant 0 0 n : ℂ)) =
      cutoffVonMangoldtCoefficient by
    funext n
    exact (cutoffVonMangoldtCoefficient_eq_weighted n).symm] at hmain
  have hmSub : m - 1 ≤ N - 1 := Nat.sub_le_sub_right hm 1
  have hlog : Nat.log 2 (m - 1) ≤ Nat.log 2 (N - 1) :=
    Nat.log_mono_right hmSub
  have haM : ∀ a ∈ detectorActiveShells A m, a + 1 ≤ M := by
    intro a ha
    have haRange := Finset.mem_range.mp
      ((detectorActiveShells_subset A m) ha)
    dsimp [M]
    omega
  have hterm : ∀ a ∈ detectorActiveShells A m,
      ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * 0 + 1)) *
          ((2 ^ a : ℕ) : ℝ) ^ (-(2 * (0 : ℝ))) ≤
        (M : ℝ) * Real.log 2 := by
    intro a ha
    have haCast : ((a + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast haM a ha
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simpa using mul_le_mul_of_nonneg_right haCast hlog2
  have hcard : ((detectorActiveShells A m).card : ℝ) ≤ M := by
    exact_mod_cast (detectorActiveShells_card_le A m).trans (by omega)
  have hsum :
      (∑ a ∈ detectorActiveShells A m,
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * 0 + 1)) *
            ((2 ^ a : ℕ) : ℝ) ^ (-(2 * (0 : ℝ)))) ≤
        (M : ℝ) ^ 2 * Real.log 2 := by
    calc
      _ ≤ ∑ _a ∈ detectorActiveShells A m,
          (M : ℝ) * Real.log 2 := Finset.sum_le_sum hterm
      _ = ((detectorActiveShells A m).card : ℝ) *
          ((M : ℝ) * Real.log 2) := by simp
      _ ≤ (M : ℝ) * ((M : ℝ) * Real.log 2) := by
        gcongr
      _ = (M : ℝ) ^ 2 * Real.log 2 := by ring
  calc
    _ ≤ C * ∑ a ∈ detectorActiveShells A m,
        ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * 0 + 1)) *
          ((2 ^ a : ℕ) : ℝ) ^ (-(2 * (0 : ℝ))) := by
      simpa only [C] using hmain
    _ ≤ C * ((M : ℝ) ^ 2 * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left hsum (by dsimp [C]; positivity)
    _ = _ := by dsimp [C, M]; ring

/-- Gallagher's complete cutoff energy is bounded by three logarithmic
factors: two from the uniform hybrid mean square, and the remaining
harmonic cutoff sum is displayed explicitly. -/
theorem intervalIntegral_primitiveCutoffVonMangoldtEnergy_le
    (Q A N T : ℕ) (hA : 1 ≤ A)
    (hheight : 4 * (T + 1) ≤ A)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ A) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveCutoffVonMangoldtEnergy Q A N t) ≤
      (4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2) *
          ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ := by
  let K : ℝ :=
    4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
      ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2
  unfold primitiveCutoffVonMangoldtEnergy
  rw [intervalIntegral.integral_finsetSum]
  · calc
      (∑ m ∈ Finset.Icc A N,
          ∫ t in (0 : ℝ)..(T : ℝ),
            (m : ℝ)⁻¹ * primitiveNegativeDirichletMass Q
              (Finset.Ioc A m) cutoffVonMangoldtCoefficient t) =
          ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ *
            (∫ t in (0 : ℝ)..(T : ℝ),
              primitiveNegativeDirichletMass Q (Finset.Ioc A m)
                cutoffVonMangoldtCoefficient t) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [intervalIntegral.integral_const_mul]
      _ ≤ ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ * K := by
        apply Finset.sum_le_sum
        intro m hm
        apply mul_le_mul_of_nonneg_left
        · exact intervalIntegral_cutoffVonMangoldt_le Q A N T m hA
            hheight hconductor (Finset.mem_Icc.mp hm).2
        · positivity
      _ = K * ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring
      _ = _ := rfl
  · intro m hm
    exact (continuous_const.mul
      (continuous_primitiveNegativeDirichletMass Q (Finset.Ioc A m)
        cutoffVonMangoldtCoefficient)).intervalIntegrable 0 T

private theorem sum_cutoff_inv_le_one_add_log
    (A N : ℕ) (hA : 1 ≤ A) :
    (∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹) ≤ 1 + Real.log N := by
  calc
    (∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹) ≤
        ∑ m ∈ Finset.Icc 1 N, (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr
          ⟨hA.trans (Finset.mem_Icc.mp hm).1, (Finset.mem_Icc.mp hm).2⟩
      · intro m hm hnot
        positivity
    _ ≤ 1 + Real.log N := by
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast] using harmonic_le_one_add_log N

/-- Fully explicit `O(log³ N)` form of the global cutoff-energy bound. -/
theorem intervalIntegral_primitiveCutoffVonMangoldtEnergy_le_logCube
    (Q A N T : ℕ) (hA : 1 ≤ A)
    (hheight : 4 * (T + 1) ≤ A)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ A) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveCutoffVonMangoldtEnergy Q A N t) ≤
      (4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2) *
          (1 + Real.log N) := by
  calc
    _ ≤ (4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ((Nat.log 2 (N - 1) + 1 : ℕ) : ℝ) ^ 2 * Real.log 2) *
          ∑ m ∈ Finset.Icc A N, (m : ℝ)⁻¹ :=
      intervalIntegral_primitiveCutoffVonMangoldtEnergy_le Q A N T hA
        hheight hconductor
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (sum_cutoff_inv_le_one_add_log A N hA)
      positivity

end Erdos48

