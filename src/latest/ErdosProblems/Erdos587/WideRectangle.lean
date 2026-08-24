import ErdosProblems.Erdos587.CyclicBlocks

/-!
# A rectangle locator from centered Fourier means

The full-period density and the centered cyclic error are compared using
one common logarithmic envelope. No growing convolution order is needed.
-/

open scoped BigOperators

namespace Erdos587

lemma log2_add_one_le_log_envelope {q n : ℕ} (hq : 0 < q) (hqn : q ≤ n) :
    ((q.log2 + 1 : ℕ) : ℝ) ≤
      ((Real.log 2)⁻¹ + 1) * (1 + Real.log n) := by
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hlog : Real.log (q : ℝ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqn)
  have hi : 0 < (Real.log (2 : ℝ))⁻¹ := inv_pos.mpr (Real.log_pos (by norm_num))
  have hbase := Real.log2_le_logb q
  change (q.log2 : ℝ) ≤ Real.log (q : ℝ) / Real.log 2 at hbase
  push_cast
  rw [div_eq_mul_inv] at hbase
  nlinarith

lemma exists_plain_rectangle_of_centered_error
    (q A C X Z L U : ℕ) [NeZero q]
    (herror : ‖∑ h : ZMod q, nvCyclicIntervalCoeff q U h *
        nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖ <
      (L : ℝ) * (nvSmoothedRectangleCount q A 0 C X Z q U 1 : ℝ)) :
    ∃ x < U, ∃ z < L,
      ((A * (Z + z) ^ 2 + C : ℕ) : ZMod q) = ((X + x : ℕ) : ZMod q) := by
  have herr : ‖∑ h : ZMod q, nvCyclicIntervalCoeff q U h ^ 1 *
      nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖ <
      (L : ℝ) * (nvSmoothedRectangleCount q A 0 C X Z q U 1 : ℝ) := by
    simpa only [pow_one] using herror
  obtain ⟨v, z, hz, heq⟩ := exists_rectangle_of_centered_error q A 0 C X Z L U 1 herr
  refine ⟨(v 0 : ℕ), (v 0).isLt, z, hz, ?_⟩
  simpa using heq

theorem exists_wide_rectangle_locator (j : ℕ) (hj : 0 < j) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q A C X Z L U M₀ : ℕ) [NeZero q], A.Coprime q → 0 < L → 0 < M₀ →
        q ≤ U * M₀ → A₀ * Real.sqrt q ≤ U →
        3 ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ)) →
        (q : ℝ) ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ)) →
        K * M₀ * (1 + Real.log ((4 * (q + M₀) * L : ℕ) : ℝ)) ^ O < Real.sqrt L →
        ∃ x < U, ∃ z < L,
          ((A * (Z + z) ^ 2 + C : ℕ) : ZMod q) = ((X + x : ℕ) : ZMod q) := by
  classical
  obtain ⟨A₀, hA₀, D, hD, P, hP, hdensity⟩ := exists_smoothed_complete_period_density
  obtain ⟨K₀, hK₀, O₀, hO₀, herror⟩ := exists_centered_cyclic_weighted_error_bound j hj
  let c := (Real.log (2 : ℝ))⁻¹ + 1
  have hc : 0 < c := by
    have := inv_pos.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    dsimp [c]
    linarith
  refine ⟨A₀, hA₀, K₀ * c * D, by positivity, O₀ + 1 + P, by omega, ?_⟩
  intro q A C X Z L U M₀ hq ha hL hM₀ hqU hU hroot hmargin hbudget
  let n := 4 * (q + M₀) * L
  let F := 1 + Real.log (n : ℝ)
  have hqpos : 0 < q := NeZero.pos q
  have hqn : q ≤ n := by
    dsimp [n]
    calc
      q ≤ 4 * (q + M₀) := by omega
      _ ≤ 4 * (q + M₀) * L := Nat.le_mul_of_pos_right _ hL
  have hnpos : 0 < n := hqpos.trans_le hqn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hnpos)
  have hF : 1 ≤ F := by dsimp [F]; linarith
  have hFpos : 0 < F := lt_of_lt_of_le zero_lt_one hF
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hqpos)
  have hlogqn : 1 + Real.log (q : ℝ) ≤ F := by
    apply add_le_add le_rfl
    exact Real.log_le_log (by exact_mod_cast hqpos) (by exact_mod_cast hqn)
  have hUpos : 0 < U := by
    by_contra hnot
    have : U = 0 := by omega
    simp only [this, zero_mul] at hqU
    omega
  have hUR : (0 : ℝ) < U := by exact_mod_cast hUpos
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsqrt : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLR
  have hfull := hdensity q A C X Z U 0 ha hU
  simp only [zero_add, pow_one] at hfull
  have hmain : (U : ℝ) / (D * F ^ P) ≤
      (nvSmoothedRectangleCount q A 0 C X Z q U 1 : ℝ) := by
    apply le_trans _ hfull
    apply div_le_div_of_nonneg_left hUR.le (mul_pos hD (pow_pos (by linarith) P))
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hlogqn P) hD.le
  have herr := herror q A C X Z L U M₀ ha hL hM₀ hqU hroot hmargin
  have hblocks : ((q.log2 + 1 : ℕ) : ℝ) ≤ c * F := log2_add_one_le_log_envelope hqpos hqn
  have hlogF : Real.log (n : ℝ) ^ O₀ ≤ F ^ O₀ :=
    pow_le_pow_left₀ hlogn (by dsimp [F]; linarith) O₀
  have herr' : ‖∑ h : ZMod q, nvCyclicIntervalCoeff q U h *
      nvCenteredQuadraticIntervalSum q A 0 C X Z L h‖ ≤
      K₀ * c * U * M₀ * Real.sqrt L * F ^ (O₀ + 1) := by
    apply herr.trans
    calc
      _ ≤ (K₀ * U * M₀ * Real.sqrt L * F ^ O₀) * (c * F) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hlogF (by positivity)
        · exact hblocks
        · positivity
        · positivity
      _ = _ := by rw [pow_succ]; ring
  have hden : 0 < D * F ^ P := mul_pos hD (pow_pos hFpos P)
  have herrlt : K₀ * c * U * M₀ * Real.sqrt L * F ^ (O₀ + 1) <
      (L : ℝ) * ((U : ℝ) / (D * F ^ P)) := by
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ hden).mpr
    have hh := mul_lt_mul_of_pos_right hbudget (mul_pos hUR hsqrt)
    change (K₀ * c * D * M₀ * F ^ (O₀ + 1 + P)) * (U * Real.sqrt L) <
      Real.sqrt L * (U * Real.sqrt L) at hh
    calc
      _ = (K₀ * c * D * M₀ * F ^ (O₀ + 1 + P)) * (U * Real.sqrt L) := by
        rw [pow_add]
        ring
      _ < Real.sqrt L * (U * Real.sqrt L) := hh
      _ = L * U := by
        rw [show Real.sqrt L * (U * Real.sqrt L) = (Real.sqrt L) ^ 2 * U by ring,
          Real.sq_sqrt hLR.le]
  apply exists_plain_rectangle_of_centered_error q A C X Z L U
  exact (herr'.trans_lt herrlt).trans_le (mul_le_mul_of_nonneg_left hmain hLR.le)

theorem exists_wide_quadratic_congruence (j : ℕ) (hj : 0 < j) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K : ℝ, 0 < K ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (q u t X Z L U M₀ : ℕ) [NeZero q], u.Coprime q → 0 < L → 0 < M₀ →
        q ≤ U * M₀ → A₀ * Real.sqrt q ≤ U →
        3 ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 / (4 ^ j : ℕ) : ℝ)) →
        (q : ℝ) ≤ (((2 * M₀ * L : ℕ) : ℝ) ^ (1 - 2 / (4 ^ j : ℕ) : ℝ)) →
        K * M₀ * (1 + Real.log ((4 * (q + M₀) * L : ℕ) : ℝ)) ^ O < Real.sqrt L →
        ∃ x < U, ∃ z < L, (Z + z) ^ 2 ≡ t + u * (X + x) [MOD q] := by
  obtain ⟨A₀, hA₀, K, hK, O, hO, hloc⟩ := exists_wide_rectangle_locator j hj
  refine ⟨A₀, hA₀, K, hK, O, hO, ?_⟩
  intro q u t X Z L U M₀ hq hu hL hM₀ hqU hU hroot hmargin hbudget
  let w := ZMod.unitOfCoprime u hu
  let a : ZMod q := (w⁻¹ : (ZMod q)ˣ)
  have ha : a.val.Coprime q := inverse_unit_val_coprime q w
  obtain ⟨x, hx, z, hz, heq⟩ :=
    hloc q a.val (-a * t).val X Z L U M₀ ha hL hM₀ hqU hU hroot hmargin hbudget
  refine ⟨x, hx, z, hz, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  have hua : (u : ZMod q) * a = 1 := by
    change (u : ZMod q) * ((w⁻¹ : (ZMod q)ˣ) : ZMod q) = 1
    rw [← ZMod.coe_unitOfCoprime u hu]
    exact Units.mul_inv w
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, ZMod.natCast_zmod_val] at heq ⊢
  calc
    _ = (u : ZMod q) * (a * ((Z : ZMod q) + z) ^ 2) := by
      rw [← mul_assoc, hua, one_mul]
    _ = u * ((X + x) + a * t) := by congr 1; linear_combination heq
    _ = t + u * (X + x) := by rw [mul_add, ← mul_assoc, hua, one_mul]; ring

lemma exists_progression_coordinate_of_square_congruence
    {q u t x z J : ℕ} (hq : 0 < q)
    (hcong : z ^ 2 ≡ t + u * x [MOD q])
    (hlo : t + u * x ≤ z ^ 2) (hhi : z ^ 2 ≤ t + u * x + q * J) :
    ∃ y ≤ J, z ^ 2 = t + u * x + q * y := by
  have hdiv : q ∣ z ^ 2 - (t + u * x) :=
    (Nat.modEq_iff_dvd' hlo).mp hcong.symm
  obtain ⟨y, hy⟩ := hdiv
  refine ⟨y, ?_, ?_⟩
  · apply Nat.le_of_mul_le_mul_left _ hq
    omega
  · omega

end Erdos587
