import ErdosProblems.Erdos1141b.SiegelSigns
import ErdosProblems.Erdos1141b.SiegelParameters

/-!
# Siegel's lower bound for quadratic L-values

The zero-free theorem, positivity of the zeta convolution, and the cutoff
`q^16` give the lower-bound form needed by the small-prime argument.
-/

open Complex Filter
open scoped BigOperators Topology

namespace Erdos1141b

theorem exists_siegel_LValue_lower_bound_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ q0 : ℕ,
      ∀ (q : ℕ) [NeZero q], q0 ≤ q →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → χ ^ 2 = 1 →
          c * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  obtain ⟨c0, hc0, hzeroFree⟩ := BoundedGaps.Maynard.exists_siegelRealCharacterZeroFree ε hε
  let c := min c0 (1 / 8)
  have hc : 0 < c := lt_min hc0 (by norm_num)
  have hc0le : c ≤ c0 := min_le_left _ _
  have hcsmall : c ≤ 1 / 8 := min_le_right _ _
  obtain ⟨η, hη, hzeta⟩ := exists_zeta_left_sign_bound
  have hδlim : Tendsto (fun q : ℕ ↦ c / 2 * (q : ℝ) ^ (-ε)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_neg_atTop hε).comp tendsto_natCast_atTop_atTop).const_mul (c / 2)
  have hloglim := tendsto_rpow_neg_mul_log (c / 2) ε hε
  have hcut : ∀ᶠ q : ℕ in atTop, 16 ≤ q ∧
      c / 2 * (q : ℝ) ^ (-ε) < η ∧
      c / 2 * (q : ℝ) ^ (-ε) * Real.log (q : ℝ) ≤ 1 / 128 := by
    filter_upwards [eventually_ge_atTop 16,
      hδlim.eventually (Iio_mem_nhds hη),
      hloglim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 128))]
      with q hq hδ hlog
    exact ⟨hq, hδ, hlog.le⟩
  obtain ⟨q0, hq0⟩ := eventually_atTop.mp hcut
  refine ⟨c / 12, by positivity, q0, ?_⟩
  intro q _ hq χ hχ hsquare
  obtain ⟨hq16, hnear, hlog⟩ := hq0 q hq
  have hq' : 1 < q := by omega
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq'.le
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq'
  let δ := c / 2 * (q : ℝ) ^ (-ε)
  let β := 1 - δ
  have hwpos : 0 < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hqpos _
  have hwone : (q : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hqone (by linarith)
  have hδ : 0 < δ := mul_pos (by positivity) hwpos
  have hδsmall : δ ≤ 1 / 16 := by
    have h := mul_le_mul_of_nonneg_left hwone (show 0 ≤ c / 2 by positivity)
    dsimp [δ]
    linarith
  have hβ : 3 / 4 ≤ β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have hβwindow : 1 - η < β := by dsimp [β, δ]; linarith
  obtain ⟨hznonpos, hzbound⟩ := hzeta β hβwindow hβ1
  have hLβ : 0 < (χ.LFunction (β : ℂ)).re := by
    apply quadratic_LFunction_pos_of_zeroFree hq' χ hχ hsquare hβ1.le
    intro σ hσ
    have hcoef : c / 2 < c0 := by linarith
    have hprod := mul_lt_mul_of_pos_right hcoef hwpos
    have hthreshold : 1 - c0 * (q : ℝ) ^ (-ε) < σ := by
      have hlow : β ≤ σ := hσ.1
      dsimp [β, δ] at hlow
      linarith
    exact hzeroFree q χ hχ hsquare σ hthreshold
  have hproduct : (riemannZeta (β : ℂ) * χ.LFunction (β : ℂ)).re ≤ 0 := by
    rw [Complex.mul_re, quadratic_LFunction_real χ hχ hsquare β, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hznonpos hLβ.le
  have hX : 0 < q ^ 16 := pow_pos (by omega) _
  have hmain := one_le_LValue_mul_cutoff_add_error hq' χ hχ hsquare hβ hβ1 hproduct (q ^ 16) hX
  have herror := siegel_cutoff_error_le hq16 hβ
  have hweight := siegel_scaled_weighted_cutoff_le (show 1 ≤ q by omega) hδ.le hδsmall hlog
  have hzscaled : -δ * (riemannZeta (β : ℂ)).re ≤ 2 := by
    rw [show 1 - β = δ by dsimp [β]; ring] at hzbound
    have h := (le_div_iff₀ hδ).mp hzbound
    nlinarith
  have hdenom : δ *
      ((∑ n ∈ Finset.Icc 1 (q ^ 16), (n : ℝ) ^ (-β)) - (riemannZeta (β : ℂ)).re) ≤ 3 := by
    change δ * (∑ n ∈ Finset.Icc 1 (q ^ 16), (n : ℝ) ^ (-β)) ≤ 1 at hweight
    nlinarith
  have hLpos := quadratic_LFunction_one_pos hq' χ hχ hsquare
  have hmainScaled := mul_le_mul_of_nonneg_left hmain hδ.le
  have hdenomScaled := mul_le_mul_of_nonneg_left hdenom hLpos.le
  have herrorScaled := mul_le_mul_of_nonneg_left herror hδ.le
  have hfinal : δ / 6 ≤ (χ.LFunction 1).re := by nlinarith
  calc
    c / 12 * (q : ℝ) ^ (-ε) = δ / 6 := by dsimp [δ]; ring
    _ ≤ _ := hfinal

/-- Uniform Siegel lower bound, including the finitely many smaller moduli. -/
theorem exists_siegel_LValue_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], 1 < q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → χ ^ 2 = 1 →
        c * (q : ℝ) ^ (-ε) ≤ (χ.LFunction 1).re := by
  obtain ⟨c0, hc0, q0, hlarge⟩ := exists_siegel_LValue_lower_bound_eventually ε hε
  let Q := max q0 2
  have hQtwo : (2 : ℝ) ≤ Q := by exact_mod_cast (le_max_right q0 2)
  have hQpos : (0 : ℝ) < Q := by linarith
  have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  let d : ℝ := 1 / (8192 * Real.sqrt (Q : ℝ) * (Real.log (Q : ℝ)) ^ 2)
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨min c0 d, lt_min hc0 hd, ?_⟩
  intro q _ hq χ hχ hsquare
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.zero_lt_of_lt hq
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  by_cases hq0 : q0 ≤ q
  · exact (mul_le_mul_of_nonneg_right (min_le_left c0 d) (Real.rpow_nonneg hqpos.le _)).trans
      (hlarge q hq0 χ hχ hsquare)
  · have hqQ : (q : ℝ) ≤ Q := by exact_mod_cast (show q ≤ Q from (Nat.le_of_lt
        (lt_of_not_ge hq0)).trans (le_max_left q0 2))
    have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq)
    have hdle : d ≤ 1 / (8192 * Real.sqrt (q : ℝ) * (Real.log (q : ℝ)) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr
    have hlower := Complex.re_le_re
      (BoundedGaps.Maynard.effectiveQuadraticLValueLowerBound hq χ hχ hsquare)
    simp only [Complex.ofReal_re] at hlower
    calc
      min c0 d * (q : ℝ) ^ (-ε) ≤ min c0 d * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos hqone (by linarith)) (le_min hc0.le hd.le)
      _ ≤ d := by simp
      _ ≤ _ := hdle.trans hlower

end Erdos1141b
