import ErdosProblems.Erdos421.VonMangoldtDirichletBlocks

/-! # Removing the logarithmic coefficient by summation by parts -/

namespace Erdos421

open Complex Filter Topology

noncomputable def normalizedVonMangoldt (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.log n

theorem normalizedVonMangoldt_nonneg (n : ℕ) : 0 ≤ normalizedVonMangoldt n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

theorem normalizedVonMangoldt_le_one {n : ℕ} (hn : 2 ≤ n) :
    normalizedVonMangoldt n ≤ 1 := by
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact (div_le_one hlog).mpr ArithmeticFunction.vonMangoldt_le_log

theorem normalizedVonMangoldt_prime {p : ℕ} (hp : p.Prime) :
    normalizedVonMangoldt p = 1 := by
  unfold normalizedVonMangoldt
  rw [ArithmeticFunction.vonMangoldt_apply_prime hp,
    div_self (Real.log_pos (by exact_mod_cast hp.one_lt)).ne']

theorem normalizedVonMangoldt_eq_zero {n : ℕ} (hn : ¬IsPrimePow n) :
    normalizedVonMangoldt n = 0 := by
  rw [normalizedVonMangoldt, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, zero_div]

noncomputable def normalizedVonMangoldtBlock (M N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N,
    LSeries.term (fun m ↦ (normalizedVonMangoldt m : ℂ)) s (M + n + 1)

theorem normalizedVonMangoldtBlock_eq_weighted (M N : ℕ) (s : ℂ) :
    normalizedVonMangoldtBlock M N s = ∑ n ∈ Finset.range N,
      (Real.log (M + n + 1 : ℕ))⁻¹ •
        LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) s (M + n + 1) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [LSeries.term_of_ne_zero (by omega), LSeries.term_of_ne_zero (by omega)]
  simp only [normalizedVonMangoldt, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_mul, div_eq_mul_inv]
  ring

theorem normalizedVonMangoldtBlock_norm_le_of_prefix_bounds {M : ℕ} (hM : 1 ≤ M)
    (N : ℕ) (s : ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ n ≤ N, ‖vonMangoldtDirichletBlock M n s‖ ≤ B) :
    ‖normalizedVonMangoldtBlock M N s‖ ≤ (Real.log (M + 1 : ℕ))⁻¹ * B := by
  let w : ℕ → ℝ := fun n ↦ (Real.log (M + n + 1 : ℕ))⁻¹
  have hw : ∀ n, 0 ≤ w n := fun n ↦ inv_nonneg.mpr (Real.log_natCast_nonneg _)
  have ha : Antitone w := by
    intro i j hij
    apply inv_anti₀
    · exact Real.log_pos (by exact_mod_cast (show 1 < M + i + 1 by omega))
    · apply Real.log_le_log
      · exact_mod_cast (show 0 < M + i + 1 by omega)
      · exact_mod_cast (show M + i + 1 ≤ M + j + 1 by omega)
  have hb := norm_sum_antitone_weight_le w
    (fun n ↦ LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) s
      (M + n + 1)) N hw ha hB hprefix
  rw [normalizedVonMangoldtBlock_eq_weighted]
  simpa only [w, Nat.add_zero] using hb

theorem normalizedVonMangoldtBlock_log_saving (K : ℕ) {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M N : ℕ, M₀ ≤ M → N ≤ M → ∀ s : ℂ, 1 ≤ s.re →
      (Real.log M) ^ (2 * A + 9) ≤ |s.im| → |s.im| ≤ (M : ℝ) ^ K →
      ‖normalizedVonMangoldtBlock M N s‖ ≤ ε / (Real.log M) ^ A := by
  obtain ⟨M₁, hM₁, hsave⟩ := vonMangoldtDirichletBlock_log_saving K hA hε
  have hlarge : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log M :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨M₂, hM₂⟩ := eventually_atTop.mp hlarge
  refine ⟨max M₁ M₂, hM₁.trans (le_max_left _ _), ?_⟩
  intro M N hM hNM s hs hlo hhi
  have hM1 : M₁ ≤ M := (le_max_left _ _).trans hM
  have hMpos : 1 ≤ M := by omega
  have hlog : 1 ≤ Real.log M := hM₂ M ((le_max_right _ _).trans hM)
  have hlogp : 0 < Real.log M := by linarith
  have hb := normalizedVonMangoldtBlock_norm_le_of_prefix_bounds hMpos N s
    (B := ε / (Real.log M) ^ A) (by positivity)
    (fun n hn ↦ hsave M n hM1 (hn.trans hNM) s hs hlo hhi)
  have hw : (Real.log (M + 1 : ℕ))⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    apply hlog.trans
    exact Real.log_le_log (by exact_mod_cast (show 0 < M by omega))
      (by exact_mod_cast (show M ≤ M + 1 by omega))
  exact hb.trans ((mul_le_mul_of_nonneg_right hw (by positivity)).trans_eq (one_mul _))

end Erdos421
