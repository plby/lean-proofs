import ErdosProblems.Erdos587.WideRectangle
import ErdosProblems.Erdos587.CriticalScale

/-!
# The enlarged cutoff for power-separated moduli

A cutoff of size `T^(1/4)/(1+log T)^F` has enough power margin for
moduli at most `T^(3/4-1/1000)`. Rounding costs only a fixed factor.
-/

open Filter

namespace Erdos587

lemma half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hh := Nat.lt_floor_add_one x
  have hfloor : (1 : ℝ) ≤ ⌊x⌋₊ := by
    exact_mod_cast (Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by norm_num; linarith))
  linarith

theorem eventually_wide_cutoff_bounds (F : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      let x := T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ F
      let M := ⌊x⌋₊
      0 < M ∧ T ^ (2499 / 10000 : ℝ) ≤ M ∧ (M : ℝ) ≤ x ∧ x / 2 ≤ M := by
  have hlog := eventually_const_mul_one_add_log_pow_le_rpow 2 F (by norm_num)
    (s := (1 / 10000 : ℝ)) (by norm_num)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℝ)] with T hlog hT
  dsimp only
  have hTpos : 0 < T := by linarith
  have hFpos : 0 < (1 + Real.log T) ^ F := pow_pos (by
    have := Real.log_nonneg hT
    linarith) F
  have hpower : 1 ≤ T ^ (2499 / 10000 : ℝ) := Real.one_le_rpow hT (by norm_num)
  have hx : 2 * T ^ (2499 / 10000 : ℝ) ≤ T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ F := by
    apply (le_div_iff₀ hFpos).mpr
    calc
      _ = (2 * (1 + Real.log T) ^ F) * T ^ (2499 / 10000 : ℝ) := by ring
      _ ≤ T ^ (1 / 10000 : ℝ) * T ^ (2499 / 10000 : ℝ) :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hTpos.le _)
      _ = T ^ (1 / 4 : ℝ) := by rw [← Real.rpow_add hTpos]; norm_num
  have hx2 : 2 ≤ T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ F := by linarith
  have hhalf := half_le_nat_floor hx2
  have hMlo : T ^ (2499 / 10000 : ℝ) ≤ (⌊T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ F⌋₊ : ℝ) :=
    (by linarith : T ^ (2499 / 10000 : ℝ) ≤ (T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ F) / 2).trans hhalf
  refine ⟨?_, hMlo, Nat.floor_le (by linarith), hhalf⟩
  exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ) < T ^ (2499 / 10000 : ℝ)) hMlo)

theorem eventually_wide_root_margin (F : ℕ) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ q L : ℕ,
      (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) → c * Real.sqrt T ≤ L →
      let M := ⌊T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ F⌋₊
      3 ≤ (((2 * M * L : ℕ) : ℝ) ^ (1 / (4 ^ 6 : ℕ) : ℝ)) ∧
        (q : ℝ) ≤ (((2 * M * L : ℕ) : ℝ) ^ (1 - 2 / (4 ^ 6 : ℕ) : ℝ)) := by
  have hLlarge := eventually_rpow_le_const_mul_rpow
    (a := (4999 / 10000 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) hc
  have hrootlarge := (tendsto_rpow_atTop
    (show (0 : ℝ) < (3749 / 5000) * (1 / (4 ^ 6 : ℕ)) by norm_num)).eventually_ge_atTop 3
  filter_upwards [eventually_wide_cutoff_bounds F, hLlarge, hrootlarge,
    eventually_ge_atTop (1 : ℝ)] with T hM hLlarge hrootlarge hT
  intro q L hq hL
  let M := ⌊T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ F⌋₊
  have hTpos : 0 < T := by linarith
  have hMlo : T ^ (2499 / 10000 : ℝ) ≤ M := hM.2.1
  have hLlo : T ^ (4999 / 10000 : ℝ) ≤ L := by
    rw [← Real.sqrt_eq_rpow] at hLlarge
    exact hLlarge.trans hL
  have hXlo : T ^ (3749 / 5000 : ℝ) ≤ ((2 * M * L : ℕ) : ℝ) := by
    calc
      _ = T ^ (2499 / 10000 : ℝ) * T ^ (4999 / 10000 : ℝ) := by
        rw [← Real.rpow_add hTpos]; norm_num
      _ ≤ (M : ℝ) * L := mul_le_mul hMlo hLlo (by positivity) (Nat.cast_nonneg M)
      _ ≤ ((2 * M * L : ℕ) : ℝ) := by push_cast; nlinarith
  constructor
  · apply hrootlarge.trans
    rw [Real.rpow_mul hTpos.le]
    exact Real.rpow_le_rpow (by positivity) hXlo (by positivity)
  · apply hq.trans
    calc
      _ ≤ T ^ ((3749 / 5000 : ℝ) * (1 - 2 / (4 ^ 6 : ℕ))) :=
        Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
      _ = (T ^ (3749 / 5000 : ℝ)) ^ (1 - 2 / (4 ^ 6 : ℕ) : ℝ) :=
        Real.rpow_mul hTpos.le _ _
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hXlo (by norm_num)

lemma wide_log_argument_bound {T : ℝ} {q M L : ℕ}
    (hT : 8 ≤ T) (hq : (q : ℝ) ≤ T) (hM : (M : ℝ) ≤ T) (hL : (L : ℝ) ≤ T)
    (hn : 0 < 4 * (q + M) * L) :
    1 + Real.log ((4 * (q + M) * L : ℕ) : ℝ) ≤ 3 * (1 + Real.log T) := by
  have hT0 : 0 < T := by linarith
  have hsize : ((4 * (q + M) * L : ℕ) : ℝ) ≤ T ^ 3 := by
    calc
      _ = 4 * ((q : ℝ) + M) * L := by push_cast; rfl
      _ ≤ 4 * (T + T) * T := by gcongr
      _ ≤ T ^ 3 := by nlinarith [sq_nonneg T]
  have hlog := Real.log_le_log (by exact_mod_cast hn) hsize
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith

theorem eventually_wide_cutoff_error_budget (K c : ℝ) (O : ℕ)
    (hK : 0 < K) (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ q L : ℕ,
      0 < q → (q : ℝ) ≤ T → c * Real.sqrt T ≤ L → (L : ℝ) ≤ T →
      let M := ⌊T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ (O + 1)⌋₊
      K * M * (1 + Real.log ((4 * (q + M) * L : ℕ) : ℝ)) ^ O < Real.sqrt L := by
  have hloglarge := Real.tendsto_log_atTop.eventually_ge_atTop
    (K * 3 ^ O / Real.sqrt c + 1)
  filter_upwards [eventually_wide_cutoff_bounds (O + 1), hloglarge,
    eventually_ge_atTop (8 : ℝ)] with T hM hloglarge hT
  intro q L hq hqT hL hLT
  let M := ⌊T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ (O + 1)⌋₊
  let F := 1 + Real.log T
  have hT1 : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hF1 : 1 ≤ F := by dsimp [F]; have := Real.log_nonneg hT1; linarith
  have hFpos : 0 < F := by linarith
  have hFp : 0 < F ^ (O + 1) := pow_pos hFpos _
  have hMhi : (M : ℝ) ≤ T ^ (1 / 4 : ℝ) / F ^ (O + 1) := hM.2.2.1
  have hMT : (M : ℝ) ≤ T := by
    calc
      _ ≤ T ^ (1 / 4 : ℝ) / F ^ (O + 1) := hMhi
      _ ≤ T ^ (1 / 4 : ℝ) := div_le_self (by positivity) (one_le_pow₀ hF1)
      _ ≤ T := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hT1 (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hLpos : 0 < L := by
    exact_mod_cast (lt_of_lt_of_le (mul_pos hc (Real.sqrt_pos.mpr hTpos)) hL)
  have hn : 0 < 4 * (q + M) * L := by positivity
  have hlog : 1 + Real.log ((4 * (q + M) * L : ℕ) : ℝ) ≤ 3 * F :=
    wide_log_argument_bound hT hqT hMT hLT hn
  have hlog0 : 0 ≤ 1 + Real.log ((4 * (q + M) * L : ℕ) : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ ((4 * (q + M) * L : ℕ) : ℝ))
    linarith
  have hcoef : K * 3 ^ O / F < Real.sqrt c := by
    apply (div_lt_iff₀ hFpos).mpr
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
    have hbase : K * 3 ^ O / Real.sqrt c < F := by dsimp [F]; linarith
    have hh := (div_lt_iff₀ hsc).mp hbase
    linarith
  calc
    _ ≤ K * (T ^ (1 / 4 : ℝ) / F ^ (O + 1)) * (3 * F) ^ O := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hMhi hK.le
      · exact pow_le_pow_left₀ hlog0 hlog O
      · positivity
      · positivity
    _ = (K * 3 ^ O / F) * T ^ (1 / 4 : ℝ) := by
      rw [mul_pow, pow_succ]
      field_simp
    _ < Real.sqrt c * T ^ (1 / 4 : ℝ) :=
      mul_lt_mul_of_pos_right hcoef (Real.rpow_pos_of_pos hTpos _)
    _ = Real.sqrt (c * Real.sqrt T) := by
      rw [Real.sqrt_mul hc.le]
      congr 1
      simp only [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul hTpos.le]
      norm_num
    _ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL

lemma wide_cutoff_product_budget {q U M : ℕ} {F : ℕ} {P Λ : ℝ}
    (hΛ : 2 ≤ Λ) (hbudget : (q : ℝ) * Λ ^ (F + 1) ≤ U * P)
    (hhalf : (P / Λ ^ F) / 2 ≤ M) : q ≤ U * M := by
  have hΛpos : 0 < Λ := by linarith
  have hden : 0 < 2 * Λ ^ F := mul_pos (by norm_num) (pow_pos hΛpos F)
  have hqP : (q : ℝ) * (2 * Λ ^ F) ≤ U * P := by
    calc
      _ = ((q : ℝ) * Λ ^ F) * 2 := by ring
      _ ≤ ((q : ℝ) * Λ ^ F) * Λ :=
        mul_le_mul_of_nonneg_left hΛ (mul_nonneg (Nat.cast_nonneg q) (pow_nonneg hΛpos.le F))
      _ = q * Λ ^ (F + 1) := by rw [pow_succ]; ring
      _ ≤ _ := hbudget
  have hqhalf : (q : ℝ) ≤ U * ((P / Λ ^ F) / 2) := by
    calc
      _ ≤ ((U : ℝ) * P) / (2 * Λ ^ F) := (le_div_iff₀ hden).mpr hqP
      _ = _ := by ring
  exact_mod_cast hqhalf.trans (mul_le_mul_of_nonneg_left hhalf (Nat.cast_nonneg U))

theorem exists_eventual_wide_quadratic_congruence (c : ℝ) (hc : 0 < c) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ B : ℕ, 0 < B ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (q u t Z L U : ℕ), 0 < q → u.Coprime q →
        (q : ℝ) ≤ T ^ (3 / 4 - 1 / 1000 : ℝ) → c * Real.sqrt T ≤ L → (L : ℝ) ≤ T →
        A₀ * Real.sqrt q ≤ U → (q : ℝ) * (1 + Real.log T) ^ B ≤ U * T ^ (1 / 4 : ℝ) →
        ∃ x < U, ∃ z < L, (Z + z) ^ 2 ≡ t + u * x [MOD q] := by
  obtain ⟨A₀, hA₀, K, hK, O, hO, hloc⟩ := exists_wide_quadratic_congruence 6 (by norm_num)
  refine ⟨A₀, hA₀, O + 2, by omega, ?_⟩
  filter_upwards [eventually_wide_cutoff_bounds (O + 1),
    eventually_wide_root_margin (O + 1) c hc,
    eventually_wide_cutoff_error_budget K c O hK hc,
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (1 : ℝ)] with T hcut hroot herr hlog hT
  intro q u t Z L U hq hu hqsize hL hLT hU hbudget
  letI : NeZero q := ⟨hq.ne'⟩
  let M := ⌊T ^ (1 / 4 : ℝ) / (1 + Real.log T) ^ (O + 1)⌋₊
  have hqT : (q : ℝ) ≤ T := by
    apply hqsize.trans
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT
      (show (3 / 4 - 1 / 1000 : ℝ) ≤ 1 by norm_num)
  have hLpos : 0 < L := by
    exact_mod_cast (lt_of_lt_of_le (mul_pos hc (Real.sqrt_pos.mpr (by linarith))) hL)
  have hqUM : q ≤ U * M :=
    wide_cutoff_product_budget (F := O + 1) (by linarith) hbudget hcut.2.2.2
  obtain ⟨hroot₁, hroot₂⟩ := hroot q L hqsize hL
  have hresult := hloc q u t 0 Z L U M hu hLpos hcut.1 hqUM hU hroot₁ hroot₂
    (herr q L hq hqT hL hLT)
  simpa only [zero_add] using hresult

end Erdos587
