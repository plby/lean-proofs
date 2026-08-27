import ErdosProblems.Erdos4.TiltedPrimeSurvival
import ErdosProblems.Erdos4.FGKMTGrowingAccuracyBudget

/-! Explicit cutoff budgets for the tilted prime-survival law. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT RandomResidueSieve

variable {P : Type*} [Fintype P] [DecidableEq P]
  (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

theorem tilted_accurate_of_prime_cutoff (τ : ℝ) (hτ : 0 ≤ τ)
    {K r Y : ℕ} {ε : ℝ} (hK : 0 < K) (hinj : Function.Injective ell)
    (hlarge : ∀ l, K < ell l) (hsize : 2 * r ≤ K) (hY : 1 ≤ Y)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hbudget : 2 * (r : ℝ) ^ 2 / K +
      2 * (r : ℝ) ^ 3 * Real.log (Y : ℝ) / ((K : ℝ) * Real.log 2) ≤ ε / 2)
    (T : Finset ℕ) (hTr : T.card ≤ r) (hT : ∀ n ∈ T, n ≤ Y)
    (hnonzero : ∀ n ∈ T, ∀ l, ¬ell l ∣ n) :
    |(sieveLaw ell τ hτ).prob (fun a => Survives ell a T) / primeSurvival ell τ ^ T.card - 1| ≤ ε := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogY : 0 ≤ Real.log (Y : ℝ) := Real.log_natCast_nonneg Y
  have htail := indexed_reciprocal_square_cutoff ell hK hinj hlarge
  have htail0 : 0 ≤ ∑ l, 1 / (ell l : ℝ) ^ 2 := Finset.sum_nonneg (fun l _ => by positivity)
  have hr : (T.card : ℝ) ≤ r := by exact_mod_cast hTr
  have hr2 := pow_le_pow_left₀ (Nat.cast_nonneg T.card) hr 2
  have hr3 := pow_le_pow_left₀ (Nat.cast_nonneg T.card) hr 3
  have hfirst : 2 * (T.card : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) ≤ 2 * (r : ℝ) ^ 2 / K := by
    calc
      _ ≤ 2 * (r : ℝ) ^ 2 * (∑ l, 1 / (ell l : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 (by norm_num)) htail0
      _ ≤ 2 * (r : ℝ) ^ 2 * (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ = _ := by ring
  have hsecond : 2 * (T.card : ℝ) ^ 3 * Real.log (Y : ℝ) / ((K : ℝ) * Real.log 2) ≤
      2 * (r : ℝ) ^ 3 * Real.log (Y : ℝ) / ((K : ℝ) * Real.log 2) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr3 (by norm_num)) hlogY)
      (mul_nonneg hKpos.le hlog2.le)
  have hh := tilted_uniform_relative_error_le ell hinj τ hτ T hnonzero
    (fun l => (Nat.mul_le_mul_left 2 hTr).trans (hsize.trans (hlarge l).le)) hY hT hKpos
    (fun l => by exact_mod_cast (hlarge l).le)
  exact hh.trans (exp_sub_one_le_of_half_budget hε0 hε1 (by linarith))

universe u

open Filter in
/-- Uniformity includes the tilt parameter, the growing prime family, and all target sets. -/
theorem eventually_tilted_prime_accuracy :
    ∀ᶠ x : ℕ in atTop,
      ∀ (Q : Type u) [Fintype Q] [DecidableEq Q] (modulus : Q → ℕ)
        [∀ q, Fact (modulus q).Prime], ∀ (τ : ℝ) (hτ : 0 ≤ τ) (Y r : ℕ),
      1 ≤ Y → Y ≤ x ^ 3 → (r : ℝ) ≤ 3 * Real.log (x : ℝ) →
      Function.Injective modulus → (∀ q, ⌊Real.log (x : ℝ) ^ (100 : ℕ)⌋₊ < modulus q) →
      ∀ T : Finset ℕ, T.card ≤ r → (∀ n ∈ T, n ≤ Y) →
        (∀ n ∈ T, ∀ q, ¬modulus q ∣ n) →
        |(sieveLaw modulus τ hτ).prob (fun a => Survives modulus a T) /
          primeSurvival modulus τ ^ T.card - 1| ≤
          1 / Real.log (x : ℝ) ^ (80 : ℕ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlog.eventually (eventually_ge_atTop (max 12 (2 * (36 + 324 / Real.log 2))))]
    with x hlarge
  let L := Real.log (x : ℝ)
  let K := ⌊L ^ (100 : ℕ)⌋₊
  change max 12 (2 * (36 + 324 / Real.log 2)) ≤ L at hlarge
  have hL : 12 ≤ L := (le_max_left _ _).trans hlarge
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLpow : L ≤ L ^ (100 : ℕ) := by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (100 : ℕ))
  have hKhalf : L ^ (100 : ℕ) / 2 ≤ (K : ℝ) := by
    have hh := Nat.lt_floor_add_one (L ^ (100 : ℕ))
    change L ^ (100 : ℕ) < (K : ℝ) + 1 at hh
    linarith
  have hKpos : (0 : ℝ) < K := (by positivity : 0 < L ^ (100 : ℕ) / 2).trans_le hKhalf
  have hK : 0 < K := by exact_mod_cast hKpos
  have hcoef : 2 * (36 + 324 / Real.log 2) ≤ L ^ (16 : ℕ) := by
    apply ((le_max_right _ _).trans hlarge).trans
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (16 : ℕ))
  intro Q _ _ modulus _ τ hτ Y r hY hYx hr hinj hell T hTr hT hnonzero
  have hsize : 2 * r ≤ K := by
    have hL2100 : L ^ (2 : ℕ) ≤ L ^ (100 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)
    have hh : (2 : ℝ) * r ≤ K := by
      calc
        _ ≤ 6 * L := by linarith
        _ ≤ L ^ (2 : ℕ) / 2 := by nlinarith
        _ ≤ L ^ (100 : ℕ) / 2 := by linarith
        _ ≤ _ := hKhalf
    exact_mod_cast hh
  have hYlog : Real.log (Y : ℝ) ≤ 3 * L := by
    have hh := Real.log_le_log (by exact_mod_cast hY : (0 : ℝ) < Y)
      (by exact_mod_cast hYx : (Y : ℝ) ≤ (x : ℝ) ^ 3)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  apply tilted_accurate_of_prime_cutoff modulus τ hτ hK hinj hell hsize hY
    (by positivity) ((div_le_one (pow_pos hLpos 80)).mpr (one_le_pow₀ hL1))
    (growing_joint_exponent_budget hL hKhalf (Nat.cast_nonneg r) hr
      (Real.log_natCast_nonneg Y) hYlog hcoef) T hTr hT hnonzero

end Erdos4.Tilted
