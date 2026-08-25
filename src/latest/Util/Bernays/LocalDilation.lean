import Util.Bernays.LocalCountingAsymptotic

/-!
# Fixed dilations of the local counting asymptotic
-/

open Filter Topology Asymptotics Real
open scoped Classical

namespace Bernays

theorem parityAdmissible_mul_of_unobstructed (S : ℕ → Prop) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hS : ∀ p : ℕ, p.Prime → S p → ¬p ∣ m) :
    ParityAdmissible S (m * n) ↔ ParityAdmissible S n := by
  have heq (p : ℕ) (hp : p.Prime) (hSp : S p) : padicValNat p (m * n) = padicValNat p n := by
    letI : Fact p.Prime := ⟨hp⟩
    rw [padicValNat.mul hm.ne' hn.ne', padicValNat.eq_zero_of_not_dvd (hS p hp hSp), zero_add]
  exact ⟨fun h p hp hSp => (heq p hp hSp) ▸ h p hp hSp,
    fun h p hp hSp => (heq p hp hSp).symm ▸ h p hp hSp⟩

theorem localParity_mul_of_unobstructed (S : ℕ → Prop) {m : ℕ} (hm : 0 < m)
    (hS : ∀ p : ℕ, p.Prime → S p → ¬p ∣ m) (n : ℕ) :
    localParity S (m * n) = localParity S n := by
  by_cases hn : 0 < n
  · simp only [localParity, hn, Nat.mul_pos hm hn, true_and,
      parityAdmissible_mul_of_unobstructed S hm hn hS]
  · simp [Nat.eq_zero_of_not_pos hn]

theorem localCount_divisible (S : ℕ → Prop) {m : ℕ} (hm : 0 < m)
    (hS : ∀ p : ℕ, p.Prime → S p → ¬p ∣ m) (N : ℕ) :
    (((Finset.Icc 1 N).filter fun n => ParityAdmissible S n).filter fun n => m ∣ n).card =
      localCount S (N / m) := by
  symm
  unfold localCount
  apply Finset.card_bij (fun n _ => m * n)
  · intro n hn
    obtain ⟨hnI, hnS⟩ := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnI).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hm hnpos,
        by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hm).mp (Finset.mem_Icc.mp hnI).2⟩
    · exact (parityAdmissible_mul_of_unobstructed S hm hnpos hS).mpr hnS
  · intro n _ k _ h
    exact Nat.mul_left_cancel hm h
  · intro n hn
    obtain ⟨hnA, hmn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnI, hnS⟩ := Finset.mem_filter.mp hnA
    obtain ⟨k, rfl⟩ := hmn
    have hk : 0 < k := Nat.pos_of_mul_pos_left (Finset.mem_Icc.mp hnI).1
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, ?_⟩, ?_⟩, rfl⟩
    · apply (Nat.le_div_iff_mul_le hm).mpr
      simpa only [Nat.mul_comm] using (Finset.mem_Icc.mp hnI).2
    · exact (parityAdmissible_mul_of_unobstructed S hm hk hS).mp hnS

theorem scale_dilation_limit {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x : ℝ => scale (x / d) / scale x) atTop (𝓝 d⁻¹) := by
  have hsmall : Tendsto (fun x : ℝ => log d / log x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp tendsto_log_atTop).const_mul (log d)
  have hlog : Tendsto (fun x : ℝ => log (x / d) / log x) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hsmall
    rw [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    rw [log_div (zero_lt_one.trans hx).ne' hd.ne', sub_div, div_self (log_pos hx).ne']
  have hsqrt : Tendsto (fun x : ℝ => sqrt (log (x / d)) / sqrt (log x)) atTop (𝓝 1) := by
    have h := hlog.sqrt
    rw [sqrt_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact sqrt_div' _ (log_pos hx).le
  have h := hsqrt.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have h' := h.const_mul d⁻¹
  simp only [inv_one, mul_one] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop (max 1 d)] with x hx
  have hx₀ : x ≠ 0 := (zero_lt_one.trans (lt_of_le_of_lt (le_max_left _ _) hx)).ne'
  have hL : sqrt (log x) ≠ 0 := (sqrt_pos.mpr (log_pos (lt_of_le_of_lt (le_max_left _ _) hx))).ne'
  have hLd : sqrt (log (x / d)) ≠ 0 :=
    (sqrt_pos.mpr (log_pos ((one_lt_div hd).mpr (lt_of_le_of_lt (le_max_right _ _) hx)))).ne'
  dsimp only [scale]
  field_simp

theorem localCount_dilation_limit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ₂ : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => (localCount (fun p : ℕ => χ p = -1) (N / m) : ℝ) / scale N)
      atTop (𝓝 ((characterLocalConstant χ / sqrt π) / m)) := by
  let C := characterLocalConstant χ / sqrt π
  have hC : C ≠ 0 := (div_pos (characterLocalConstant_pos χ hχ) (sqrt_pos.mpr pi_pos)).ne'
  have hloc : Tendsto (fun x : ℝ =>
      (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ) / scale x) atTop (𝓝 C) := by
    have heq := localCount_isEquivalent χ hχ₂ hχ
    have ht := (isEquivalent_iff_tendsto_one (show ∀ᶠ x : ℝ in atTop,
        C * x / sqrt (log x) ≠ 0 by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact div_ne_zero (mul_ne_zero hC (zero_lt_one.trans hx).ne') (sqrt_pos.mpr (log_pos hx)).ne')).mp heq
    have h := ht.mul_const C
    rw [one_mul] at h
    apply h.congr'
    exact Eventually.of_forall fun x => by
      change (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ) /
        (C * x / sqrt (log x)) * C =
        (localCount (fun p : ℕ => χ p = -1) ⌊x⌋₊ : ℝ) / (x / sqrt (log x))
      rw [mul_div_assoc, mul_comm C, div_mul_eq_div_div, div_mul_cancel₀ _ hC]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := (hloc.comp (tendsto_id.atTop_div_const hmR)).mul (scale_dilation_limit hmR)
  have h' := h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  change Tendsto _ _ (𝓝 (C * (m : ℝ)⁻¹)) at h'
  rw [← div_eq_mul_inv] at h'
  apply h'.congr'
  filter_upwards [eventually_gt_atTop m] with N hN
  have hscale : scale ((N : ℝ) / m) ≠ 0 :=
    (scale_pos ((one_lt_div hmR).mpr (by exact_mod_cast hN))).ne'
  dsimp only [Function.comp_def, id_eq]
  rw [div_mul_div_cancel₀ hscale, Nat.floor_div_natCast, Nat.floor_natCast]

end Bernays
