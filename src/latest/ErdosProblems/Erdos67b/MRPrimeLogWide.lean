import ErdosProblems.Erdos67b.MRPrimeLogDyadic

/-! # Three dyadic pieces cover the complete smooth-kernel support -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

open LogWeylParameters ResidueLogPhase

theorem mrSum_Icc_split_before (u : ℕ → ℂ) {A B M : ℕ}
    (hAB : A < B) (hBM : B ≤ M) :
    (∑ n ∈ Finset.Icc A M, u n) =
      (∑ n ∈ Finset.Icc A (B - 1), u n) + ∑ n ∈ Finset.Icc B M, u n := by
  have hs : Finset.Icc A M = Finset.Icc A (B - 1) ∪ Finset.Icc B M := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  rw [hs, Finset.sum_union]
  apply Finset.disjoint_left.2
  intro n hn hn'
  simp only [Finset.mem_Icc] at hn hn'
  omega

theorem mrNorm_Icc_le_three_dyadic_bounds (u : ℕ → ℂ) {A M : ℕ}
    (hA : 1 ≤ A) (hM : M ≤ 8 * A) {E : ℝ} (hE : 0 ≤ E)
    (hfirst : ∀ m ≤ 2 * A, ‖∑ n ∈ Finset.Icc A m, u n‖ ≤ E)
    (hsecond : ∀ m ≤ 4 * A, ‖∑ n ∈ Finset.Icc (2 * A) m, u n‖ ≤ 2 * E)
    (hthird : ∀ m ≤ 8 * A, ‖∑ n ∈ Finset.Icc (4 * A) m, u n‖ ≤ 4 * E) :
    ‖∑ n ∈ Finset.Icc A M, u n‖ ≤ 7 * E := by
  by_cases hMtwo : M ≤ 2 * A
  · exact (hfirst M hMtwo).trans (by linarith)
  rw [mrSum_Icc_split_before u (B := 2 * A) (by omega) (by omega)]
  have hb₁ := hfirst (2 * A - 1) (by omega)
  by_cases hMfour : M ≤ 4 * A
  · have hb₂ := hsecond M hMfour
    exact (norm_add_le _ _).trans (by linarith)
  rw [mrSum_Icc_split_before u (A := 2 * A) (B := 4 * A) (M := M) (by omega) (by omega)]
  have hb₂ := hsecond (4 * A - 1) (by omega)
  have hb₃ := hthird M hM
  refine (norm_add_le _ _).trans ?_
  calc
    _ ≤ E + (2 * E + 4 * E) :=
      add_le_add hb₁ ((norm_add_le _ _).trans (add_le_add hb₂ hb₃))
    _ = 7 * E := by ring

theorem mrExists_primeMellin_wide_bound (R : ℕ) (hR : 2 ≤ R) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ {A M : ℕ}, A₀ ≤ A → M ≤ 8 * A →
      ∀ {t : ℝ}, t ≠ 0 → positiveLogCoefficient t < (A : ℝ) ^ (R + 1) →
        ‖∑ n ∈ Finset.Icc A M, mrPrimeMellinMonomial 0 t n‖ ≤
          7 * (3 * (A : ℝ) / positiveLogCoefficient t +
            (mrPrimeWeylConstant R + 20) * (A : ℝ) ^ (1 - savingExponent R)) := by
  obtain ⟨A₀, hA₀one, hA₀⟩ := mrExists_primeMellin_allHeight_dyadic_bound R hR
  refine ⟨A₀, hA₀one, ?_⟩
  intro A M hA hM t ht hu
  have hAone : 1 ≤ A := hA₀one.trans hA
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hAone
  have ha := positiveLogCoefficient_pos ht
  have hC := mrPrimeWeylConstant_pos R
  have hd := savingExponent_pos R
  let E := 3 * (A : ℝ) / positiveLogCoefficient t +
    (mrPrimeWeylConstant R + 20) * (A : ℝ) ^ (1 - savingExponent R)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hblock (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : m ≤ 2 * (k * A)) :
      ‖∑ n ∈ Finset.Icc (k * A) m, mrPrimeMellinMonomial 0 t n‖ ≤ (k : ℝ) * E := by
    have hAk : A ≤ k * A := by nlinarith
    have hheight : positiveLogCoefficient t < ((k * A : ℕ) : ℝ) ^ (R + 1) := by
      apply hu.trans_le
      exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hAk) _
    have hb := hA₀ (hA.trans hAk) hm ht hheight
    have hkpow : (k : ℝ) ^ (1 - savingExponent R) ≤ k :=
      Real.rpow_le_self_of_one_le (by exact_mod_cast hk) (by linarith)
    have hterm : ((k * A : ℕ) : ℝ) ^ (1 - savingExponent R) ≤
        (k : ℝ) * (A : ℝ) ^ (1 - savingExponent R) := by
      rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg A)]
      exact mul_le_mul_of_nonneg_right hkpow (Real.rpow_nonneg (Nat.cast_nonneg A) _)
    apply hb.trans
    calc
      _ ≤ 3 * ((k * A : ℕ) : ℝ) / positiveLogCoefficient t +
          (mrPrimeWeylConstant R + 20) * ((k : ℝ) * (A : ℝ) ^ (1 - savingExponent R)) := by
        gcongr
      _ = (k : ℝ) * E := by dsimp [E]; push_cast; ring
  apply mrNorm_Icc_le_three_dyadic_bounds _ hAone hM hE
  · intro m hm
    simpa only [one_mul, Nat.cast_one] using hblock 1 (by norm_num) m (by simpa using hm)
  · intro m hm
    simpa only [Nat.cast_ofNat] using hblock 2 (by norm_num) m (by omega)
  · intro m hm
    simpa only [Nat.cast_ofNat] using hblock 4 (by norm_num) m (by omega)

end

end Erdos67b
