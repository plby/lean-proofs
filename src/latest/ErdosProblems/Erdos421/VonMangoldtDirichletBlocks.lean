import ErdosProblems.Erdos421.VonMangoldtBlocks
import ErdosProblems.Erdos421.ZetaBlocks

/-! # Logarithmic savings for von Mangoldt Dirichlet blocks -/

namespace Erdos421

open Complex

theorem LSeries_term_eq_real_weight {n : ℕ} (hn : 0 < n) (f : ℕ → ℂ) (s : ℂ) :
    LSeries.term f s n = (n : ℝ) ^ (-s.re) • LSeries.term f (s.im * I) n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
  simp only [div_eq_mul_inv, ← Complex.cpow_neg]
  rw [← Complex.ofReal_natCast, cpow_neg_eq_weighted_phase hnp s,
    cpow_neg_eq_weighted_phase hnp (s.im * I)]
  simp only [mul_I_re, ofReal_im, neg_zero, Real.rpow_zero, ofReal_one,
    one_mul, mul_I_im, ofReal_re, Complex.real_smul]
  ring

noncomputable def vonMangoldtDirichletBlock (M N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N,
    LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) s (M + n + 1)

theorem vonMangoldtDirichletBlock_norm_le_of_prefix_bounds {M : ℕ} (hM : 0 < M)
    (N : ℕ) (s : ℂ) (hs : 0 ≤ s.re) {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ N, ‖vonMangoldtBlock M n s.im‖ ≤ B) :
    ‖vonMangoldtDirichletBlock M N s‖ ≤ (M : ℝ) ^ (-s.re) * B := by
  let w : ℕ → ℝ := fun n ↦ ((M + n + 1 : ℕ) : ℝ) ^ (-s.re)
  have hw : ∀ n, 0 ≤ w n := fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  have ha : Antitone w := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (show 0 < M + i + 1 by omega)
    · exact_mod_cast (show M + i + 1 ≤ M + j + 1 by omega)
    · exact neg_nonpos.mpr hs
  have hb := norm_sum_antitone_weight_le w
    (fun n ↦ LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
      (s.im * I) (M + n + 1)) N hw ha hB hprefix
  have he : vonMangoldtDirichletBlock M N s = ∑ n ∈ Finset.range N,
      w n • LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
        (s.im * I) (M + n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    exact LSeries_term_eq_real_weight (by omega) _ s
  have hw0 : w 0 ≤ (M : ℝ) ^ (-s.re) := by
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast hM
    · exact_mod_cast (show M ≤ M + 0 + 1 by omega)
    · exact neg_nonpos.mpr hs
  rw [he]
  exact hb.trans (mul_le_mul_of_nonneg_right hw0 hB)

theorem vonMangoldtDirichletBlock_log_saving (K : ℕ) {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M N : ℕ, M₀ ≤ M → N ≤ M → ∀ s : ℂ, 1 ≤ s.re →
      (Real.log M) ^ (2 * A + 9) ≤ |s.im| → |s.im| ≤ (M : ℝ) ^ K →
      ‖vonMangoldtDirichletBlock M N s‖ ≤ ε / (Real.log M) ^ A := by
  obtain ⟨M₀, hM₀, hsave⟩ := vonMangoldtBlock_log_saving K hA hε
  refine ⟨M₀, hM₀, ?_⟩
  intro M N hM hNM s hs hlo hhi
  have hM2 : 2 ≤ M := hM₀.trans hM
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hp : 0 < (Real.log M) ^ A := Real.rpow_pos_of_pos hlog _
  have hb := vonMangoldtDirichletBlock_norm_le_of_prefix_bounds (by omega : 0 < M)
    N s (by linarith) (B := ε * M / (Real.log M) ^ A) (by positivity)
    (fun n hn ↦ hsave M n hM (hn.trans hNM) s.im hlo hhi)
  have hweight : (M : ℝ) ^ (-s.re) * M ≤ 1 := by
    calc
      _ ≤ (M : ℝ) ^ (-1 : ℝ) * M := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)) hMpos.le
      _ = 1 := by rw [Real.rpow_neg_one, inv_mul_cancel₀ hMpos.ne']
  calc
    _ ≤ (M : ℝ) ^ (-s.re) * (ε * M / (Real.log M) ^ A) := hb
    _ = ((M : ℝ) ^ (-s.re) * M) * (ε / (Real.log M) ^ A) := by ring
    _ ≤ 1 * (ε / (Real.log M) ^ A) := mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := one_mul _

end Erdos421
