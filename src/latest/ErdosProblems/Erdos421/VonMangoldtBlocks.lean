import ErdosProblems.Erdos421.VonMangoldtLogSaving

/-! # Uniform prefix bounds for von Mangoldt blocks -/

namespace Erdos421

open Complex Filter Topology

noncomputable def vonMangoldtBlock (M N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N,
    LSeries.term (fun m ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (t * I) (M + n + 1)

theorem vonMangoldtBlock_eq_prefix (M N : ℕ) (t : ℝ) :
    vonMangoldtBlock M N t = vonMangoldtTwistSum ((M + N : ℕ) : ℝ) t -
      vonMangoldtTwistSum (M : ℝ) t := by
  unfold vonMangoldtTwistSum finiteRealPrefix vonMangoldtBlock
  simp only [Nat.floor_natCast]
  rw [show M + N + 1 = (M + 1) + N by omega, Finset.sum_range_add, add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  omega

theorem vonMangoldtBlock_log_saving (K : ℕ) {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M N : ℕ, M₀ ≤ M → N ≤ M → ∀ t : ℝ,
      (Real.log M) ^ (2 * A + 9) ≤ |t| → |t| ≤ (M : ℝ) ^ K →
      ‖vonMangoldtBlock M N t‖ ≤ ε * M / (Real.log M) ^ A := by
  let η : ℝ := ε / 3
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨X₁, hX₁, hsave⟩ := vonMangoldtTwistSum_log_saving K hA hη
  have hlargeM : ∀ᶠ M : ℕ in atTop, max X₁ 2 ≤ (M : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  have hlargeLog : ∀ᶠ M : ℕ in atTop, max 1 ((2 : ℝ) ^ (2 * A + 8)) ≤ Real.log M :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hlarge : ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, N ≤ M → ∀ t : ℝ,
      (Real.log M) ^ (2 * A + 9) ≤ |t| → |t| ≤ (M : ℝ) ^ K →
      ‖vonMangoldtBlock M N t‖ ≤ ε * M / (Real.log M) ^ A := by
    filter_upwards [hlargeM, hlargeLog] with M hM hloglarge
    intro N hNM t hlo hhi
    have hMx : X₁ ≤ (M : ℝ) := (le_max_left _ _).trans hM
    have hM2 : (2 : ℝ) ≤ M := (le_max_right _ _).trans hM
    have hMp : (0 : ℝ) < M := by linarith
    have hMN : (M : ℝ) ≤ (M + N : ℕ) := by exact_mod_cast Nat.le_add_right M N
    have hMN2 : ((M + N : ℕ) : ℝ) ≤ 2 * M := by exact_mod_cast (show M + N ≤ 2 * M by omega)
    have hlog : 1 ≤ Real.log M := (le_max_left _ _).trans hloglarge
    have hlogp : 0 < Real.log M := by linarith
    have hlogtwo : (2 : ℝ) ^ (2 * A + 8) ≤ Real.log M :=
      (le_max_right _ _).trans hloglarge
    have hlogs : Real.log M ≤ Real.log ((M + N : ℕ) : ℝ) ∧
        Real.log ((M + N : ℕ) : ℝ) ≤ 2 * Real.log M := by
      simpa only [Nat.cast_add] using
        unsmoothing_log_bounds hM2 (Nat.cast_nonneg N) (Nat.cast_le.mpr hNM)
    have hlogNp : 0 < Real.log ((M + N : ℕ) : ℝ) := hlogp.trans_le hlogs.1
    have hfreq : (Real.log ((M + N : ℕ) : ℝ)) ^ (2 * A + 8) ≤
        (Real.log M) ^ (2 * A + 9) := by
      calc
        _ ≤ (2 * Real.log M) ^ (2 * A + 8) :=
          Real.rpow_le_rpow hlogNp.le hlogs.2 (by linarith)
        _ = (2 : ℝ) ^ (2 * A + 8) * (Real.log M) ^ (2 * A + 8) :=
          Real.mul_rpow (by norm_num) hlogp.le
        _ ≤ Real.log M * (Real.log M) ^ (2 * A + 8) :=
          mul_le_mul_of_nonneg_right hlogtwo (Real.rpow_nonneg hlogp.le _)
        _ = _ := by
          rw [show 2 * A + 9 = 1 + (2 * A + 8) by ring,
            Real.rpow_add hlogp 1 (2 * A + 8), Real.rpow_one]
    have hbottom := hsave (M : ℝ) t hMx
      ((Real.rpow_le_rpow_of_exponent_le hlog (by linarith)).trans hlo) hhi
    have htop := hsave ((M + N : ℕ) : ℝ) t (hMx.trans hMN) (hfreq.trans hlo)
      (hhi.trans (pow_le_pow_left₀ hMp.le hMN K))
    have hpow : 0 < (Real.log M) ^ A := Real.rpow_pos_of_pos hlogp _
    have htop' : ‖vonMangoldtTwistSum ((M + N : ℕ) : ℝ) t‖ ≤
        2 * η * M / (Real.log M) ^ A := by
      apply htop.trans
      apply (div_le_div_of_nonneg_left (by positivity) hpow
        (Real.rpow_le_rpow hlogp.le hlogs.1 hA)).trans
      exact div_le_div_of_nonneg_right (by nlinarith only [hMN2, hη]) hpow.le
    rw [vonMangoldtBlock_eq_prefix]
    have hb := (norm_sub_le _ _).trans (add_le_add htop' hbottom)
    exact hb.trans_eq (by dsimp only [η]; ring)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max M₀ 2, le_max_right _ _, ?_⟩
  intro M N hM hN t hlo hhi
  exact hM₀ M ((le_max_left M₀ 2).trans hM) N hN t hlo hhi

end Erdos421
