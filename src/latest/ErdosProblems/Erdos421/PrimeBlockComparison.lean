import ErdosProblems.Erdos421.NormalizedVonMangoldt
import ErdosProblems.Erdos421.ProperPrimePowers

/-! # Removing proper prime powers from the Dirichlet block -/

namespace Erdos421

open Complex

noncomputable def primeDirichletBlock (M N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ (Finset.range N).filter (fun n ↦ (M + n + 1).Prime),
    ((M + n + 1 : ℕ) : ℂ) ^ (-s)

theorem normalizedVonMangoldt_term_norm_le {M n : ℕ} (hM : 1 ≤ M) (hn : M < n)
    (s : ℂ) (hs : 1 ≤ s.re) :
    ‖LSeries.term (fun m ↦ (normalizedVonMangoldt m : ℂ)) s n‖ ≤ (M : ℝ)⁻¹ := by
  have hn2 : 2 ≤ n := by omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  rw [LSeries.norm_term_eq, if_neg (by omega),
    Complex.norm_of_nonneg (normalizedVonMangoldt_nonneg n)]
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ s.re := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 hs
  calc
    _ ≤ 1 / (n : ℝ) ^ s.re := div_le_div_of_nonneg_right
      (normalizedVonMangoldt_le_one hn2) (Real.rpow_nonneg hnp.le _)
    _ ≤ 1 / (n : ℝ) := div_le_div_of_nonneg_left (by norm_num) hnp hpow
    _ ≤ 1 / (M : ℝ) := div_le_div_of_nonneg_left (by norm_num) hMp
      (by exact_mod_cast hn.le)
    _ = _ := one_div _

theorem normalizedVonMangoldtBlock_sub_prime (M N : ℕ) (s : ℂ) :
    normalizedVonMangoldtBlock M N s - primeDirichletBlock M N s =
      ∑ n ∈ (Finset.range N).filter
        (fun n ↦ IsPrimePow (M + n + 1) ∧ ¬(M + n + 1).Prime),
        LSeries.term (fun m ↦ (normalizedVonMangoldt m : ℂ)) s (M + n + 1) := by
  classical
  unfold normalizedVonMangoldtBlock primeDirichletBlock
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hp : (M + n + 1).Prime
  · simp only [hp, not_true_eq_false, and_false, if_false, if_true,
      LSeries.term_of_ne_zero (by omega : M + n + 1 ≠ 0), normalizedVonMangoldt_prime hp,
      Complex.ofReal_one, one_div, Complex.cpow_neg, sub_self]
  · by_cases hpp : IsPrimePow (M + n + 1)
    · simp only [hp, hpp, not_false_eq_true, and_self, if_true, if_false, sub_zero]
    · simp only [hp, hpp, not_false_eq_true, false_and, if_false, sub_zero,
        LSeries.term_of_ne_zero (by omega : M + n + 1 ≠ 0),
        normalizedVonMangoldt_eq_zero hpp, Complex.ofReal_zero, zero_div]

theorem normalizedVonMangoldtBlock_sub_prime_norm_le {M N : ℕ} (hM : 1 ≤ M)
    (hN : N ≤ M) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖normalizedVonMangoldtBlock M N s - primeDirichletBlock M N s‖ ≤
      ((properPrimePowers (2 * M)).card : ℝ) / M := by
  classical
  let S := (Finset.range N).filter
    (fun n ↦ IsPrimePow (M + n + 1) ∧ ¬(M + n + 1).Prime)
  have hcard : S.card ≤ (properPrimePowers (2 * M)).card := by
    apply Finset.card_le_card_of_injOn (fun n ↦ M + n + 1)
    · intro n hn
      obtain ⟨hnN, hpp⟩ := Finset.mem_filter.mp hn
      have hnlt := Finset.mem_range.mp hnN
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by change M + n + 1 < 2 * M + 1; omega), hpp⟩
    · intro n _ m _ he
      dsimp only at he
      omega
  rw [normalizedVonMangoldtBlock_sub_prime]
  calc
    _ ≤ ∑ n ∈ S, ‖LSeries.term (fun m ↦ (normalizedVonMangoldt m : ℂ)) s (M + n + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ S, (M : ℝ)⁻¹ := Finset.sum_le_sum fun n _ ↦
      normalizedVonMangoldt_term_norm_le hM (by omega) s hs
    _ = (S.card : ℝ) / M := by rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

theorem primeDirichletBlock_norm_le {M N : ℕ} (hM : 1 ≤ M) (hN : N ≤ M)
    (s : ℂ) (hs : 1 ≤ s.re) :
    ‖primeDirichletBlock M N s‖ ≤ ‖normalizedVonMangoldtBlock M N s‖ +
      ((properPrimePowers (2 * M)).card : ℝ) / M := by
  have he : primeDirichletBlock M N s = normalizedVonMangoldtBlock M N s -
      (normalizedVonMangoldtBlock M N s - primeDirichletBlock M N s) := by ring
  calc
    _ = ‖normalizedVonMangoldtBlock M N s -
        (normalizedVonMangoldtBlock M N s - primeDirichletBlock M N s)‖ := congrArg norm he
    _ ≤ ‖normalizedVonMangoldtBlock M N s‖ +
        ‖normalizedVonMangoldtBlock M N s - primeDirichletBlock M N s‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl (normalizedVonMangoldtBlock_sub_prime_norm_le hM hN s hs)

end Erdos421
