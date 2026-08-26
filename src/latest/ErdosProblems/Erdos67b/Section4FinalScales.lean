import ErdosProblems.Erdos67b.Section4FinalParameters

/-! # The final dyadic scale pays all scalar Section 4 errors -/

namespace Erdos67b

theorem section4Log_largeScale (K D : ℕ) :
    Real.log (((4 ^ K) ^ D : ℕ) : ℝ) =
      (D : ℝ) * Real.log ((4 ^ K : ℕ) : ℝ) := by
  rw [Nat.cast_pow, Real.log_pow]

theorem section4Log_largeScale_ge {D : ℕ} (hD : 0 < D) (K : ℕ) :
    (K : ℝ) ≤ Real.log (((4 ^ K) ^ D : ℕ) : ℝ) := by
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_two_gt_d9]
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast hD
  rw [section4Log_largeScale, Nat.cast_pow, Real.log_pow]
  calc
    (K : ℝ) ≤ (D : ℝ) * K := by nlinarith [Nat.cast_nonneg (α := ℝ) K]
    _ ≤ (D : ℝ) * K * Real.log 4 := le_mul_of_one_le_right (by positivity) hlog4
    _ = (D : ℝ) * (K * Real.log 4) := by ring

theorem exists_section4FinalScaleThreshold
    (A H k D : ℕ) (hD : 0 < D)
    {c : ℝ} (hc : 0 < c) (hDc : 16 * (H : ℝ) ≤ c * D) :
    ∃ K₀ : ℕ, max A (A ^ k) ≤ K₀ ∧ 2 ≤ K₀ ∧
      ∀ K : ℕ, K₀ ≤ K →
        A ≤ 2 ^ K ∧
        8 * (H : ℝ) * (4 * H / ((2 ^ K : ℕ) : ℝ)) ≤ c ∧
        4 * (H : ℝ) * (1 + 2 * Real.log ((4 ^ K : ℕ) : ℝ)) ≤
          c * Real.log (((4 ^ K) ^ D : ℕ) : ℝ) ∧
        8 * ((A ^ k : ℕ) : ℝ) * H ≤ c * Real.log (((4 ^ K) ^ D : ℕ) : ℝ) ∧
        4 * ((A ^ k : ℕ) : ℝ) * H * (1 + 4 * H) ≤
          c * Real.log (((4 ^ K) ^ D : ℕ) : ℝ) := by
  let R : ℝ := max (32 * (H : ℝ) ^ 2 / c)
    (max (8 * (H : ℝ) / c)
      (max (8 * ((A ^ k : ℕ) : ℝ) * H / c)
        (4 * ((A ^ k : ℕ) : ℝ) * H * (1 + 4 * H) / c)))
  let K₀ := max (max A (A ^ k)) (max 2 ⌈R⌉₊)
  refine ⟨K₀, le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro K hK
  have hAK : A ≤ K := ((le_max_left _ _).trans (le_max_left _ _)).trans hK
  have hceilK : ⌈R⌉₊ ≤ K := ((le_max_right _ _).trans (le_max_right _ _)).trans hK
  have hRK : R ≤ (K : ℝ) := (Nat.le_ceil R).trans (Nat.cast_le.2 hceilK)
  have hphaseK : 32 * (H : ℝ) ^ 2 / c ≤ K := (le_max_left _ _).trans hRK
  have hrest := (le_max_right _ _).trans hRK
  have hshortK : 8 * (H : ℝ) / c ≤ K := (le_max_left _ _).trans hrest
  have hlast := (le_max_right _ _).trans hrest
  have hlinearK : 8 * ((A ^ k : ℕ) : ℝ) * H / c ≤ K := (le_max_left _ _).trans hlast
  have htailK : 4 * ((A ^ k : ℕ) : ℝ) * H * (1 + 4 * H) / c ≤ K :=
    (le_max_right _ _).trans hlast
  have hlogK := section4Log_largeScale_ge hD K
  have hscale : 8 * (H : ℝ) ≤ c * Real.log (((4 ^ K) ^ D : ℕ) : ℝ) := by
    have hh := (div_le_iff₀ hc).1 hshortK
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hlogK hc.le])
  have hlogY : 0 ≤ Real.log ((4 ^ K : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_pow K 4 (by norm_num))
  have hDlog := mul_le_mul_of_nonneg_right hDc hlogY
  have hquad : 4 * (H : ℝ) * (1 + 2 * Real.log ((4 ^ K : ℕ) : ℝ)) ≤
      c * Real.log (((4 ^ K) ^ D : ℕ) : ℝ) := by
    rw [section4Log_largeScale] at hscale ⊢
    nlinarith only [hscale, hDlog]
  refine ⟨hAK.trans K.lt_two_pow_self.le, ?_, hquad, ?_, ?_⟩
  · have hpow : (K : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by exact_mod_cast K.lt_two_pow_self.le
    have hh := (div_le_iff₀ hc).1 (hphaseK.trans hpow)
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 ^ K : ℕ))).2
    nlinarith only [hh]
  · have hh := (div_le_iff₀ hc).1 hlinearK
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hlogK hc.le])
  · have hh := (div_le_iff₀ hc).1 htailK
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hlogK hc.le])

end Erdos67b
