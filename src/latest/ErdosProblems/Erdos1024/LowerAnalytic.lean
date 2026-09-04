/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1024.LowerFinite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Explicit asymptotic parameters for the lower bound

The constants are intentionally generous.  We sample with probability
approximately `n^(-9/20)`, use logarithmic truncation, and set the proposed
independence threshold to one millionth of `sqrt (n log n)`.
-/

open Filter

namespace Erdos1024
namespace Lower

noncomputable def lowerConstant : ℝ := 1 / 1000000

noncomputable def lowerScale (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * Real.log n)

noncomputable def sampleRoot (n : ℕ) : ℝ :=
  (n : ℝ) ^ ((9 : ℝ) / 20)

noncomputable def sampleColors (n : ℕ) : ℕ :=
  ⌈sampleRoot n⌉₊

noncomputable def independenceCutoff (n : ℕ) : ℕ :=
  ⌊lowerConstant * lowerScale n⌋₊

noncomputable def weightCutoff (n : ℕ) : ℕ :=
  ⌊Real.log n / 1000⌋₊

noncomputable def extensionTarget (n : ℕ) : ℝ :=
  100 * (independenceCutoff n : ℝ) ^ 2 / sampleColors n +
    10 * (weightCutoff n : ℝ) * (independenceCutoff n + 1 : ℕ) *
      Real.log (n + 1)

noncomputable def extensionCap (n : ℕ) : ℕ :=
  ⌈extensionTarget n⌉₊

noncomputable def sampleTarget (n : ℕ) : ℝ :=
  (n : ℝ) / (2 * sampleColors n)

lemma lowerConstant_pos : 0 < lowerConstant := by
  norm_num [lowerConstant]

lemma lowerScale_nonneg (n : ℕ) : 0 ≤ lowerScale n := Real.sqrt_nonneg _

lemma lowerScale_sq {n : ℕ} (hn : 1 ≤ n) :
    (lowerScale n) ^ 2 = (n : ℝ) * Real.log n := by
  unfold lowerScale
  rw [Real.sq_sqrt]
  exact mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast hn))

lemma sampleRoot_pos {n : ℕ} (hn : 0 < n) : 0 < sampleRoot n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma sampleColors_pos {n : ℕ} (hn : 0 < n) : 0 < sampleColors n := by
  exact Nat.ceil_pos.mpr (sampleRoot_pos hn)

lemma sampleColors_bounds {n : ℕ} (hn : 1 ≤ n) :
    sampleRoot n ≤ (sampleColors n : ℝ) ∧
      (sampleColors n : ℝ) ≤ 2 * sampleRoot n := by
  have hrpos := sampleRoot_pos (by omega : 0 < n)
  have hrone : 1 ≤ sampleRoot n := by
    unfold sampleRoot
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hlower : sampleRoot n ≤ (sampleColors n : ℝ) := Nat.le_ceil _
  have hupper0 : (sampleColors n : ℝ) < sampleRoot n + 1 :=
    Nat.ceil_lt_add_one hrpos.le
  exact ⟨hlower, by linarith⟩

lemma independenceCutoff_upper {n : ℕ} (_hn : 1 ≤ n) :
    (independenceCutoff n : ℝ) ≤ lowerConstant * lowerScale n := by
  exact Nat.floor_le (mul_nonneg lowerConstant_pos.le (lowerScale_nonneg n))

lemma weightCutoff_upper {n : ℕ} (hn : 1 ≤ n) :
    (weightCutoff n : ℝ) ≤ Real.log n / 1000 := by
  exact Nat.floor_le (div_nonneg (Real.log_nonneg (by exact_mod_cast hn)) (by norm_num))

lemma weightCutoff_lower {n : ℕ}
    (hlog : 2000 ≤ Real.log (n : ℝ)) :
    Real.log n / 2000 ≤ weightCutoff n := by
  have hx : 2 ≤ Real.log (n : ℝ) / 1000 := by linarith
  have hfloor := Nat.sub_one_lt_floor (Real.log (n : ℝ) / 1000)
  have hnonneg : 0 ≤ Real.log (n : ℝ) / 1000 := by linarith
  have hfloorCast : Real.log (n : ℝ) / 1000 - 1 <
      (weightCutoff n : ℝ) := by
    simpa [weightCutoff] using hfloor
  linarith

lemma extensionTarget_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ extensionTarget n := by
  have hk : (0 : ℝ) < sampleColors n := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  unfold extensionTarget
  apply add_nonneg
  · exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hk.le
  · have hlog' : 0 ≤ Real.log ((n : ℝ) + 1) := by simpa using hlog
    positivity

lemma extensionCap_bounds {n : ℕ} (hn : 1 ≤ n) :
    extensionTarget n ≤ (extensionCap n : ℝ) ∧
      (extensionCap n : ℝ) ≤ extensionTarget n + 1 := by
  have hnonneg := extensionTarget_nonneg hn
  exact ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one hnonneg).le⟩

lemma log_four_lt_two : Real.log (4 : ℝ) < 2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  calc
    (4 : ℝ) = 2 ^ 2 := by norm_num
    _ < Real.exp 1 ^ 2 := by gcongr; exact Real.exp_one_gt_two
    _ = Real.exp 2 := by
      rw [← Real.exp_nat_mul]
      norm_num

/-- The exponential union-bound term is already at most `(n+1)⁻²`.
This estimate is pointwise once the logarithmic cutoff is positive. -/
lemma extensionBadBound_le {n : ℕ} (hn : 1 ≤ n)
    (hB : 0 < weightCutoff n) :
    (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
      Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
        ((sampleColors n : ℝ) * weightCutoff n) -
          (extensionCap n : ℝ) / weightCutoff n)) ≤
      1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
  let a := independenceCutoff n
  let b := weightCutoff n
  let k := sampleColors n
  let x : ℝ := n + 1
  have hbR : (0 : ℝ) < b := by exact_mod_cast hB
  have hkR : (0 : ℝ) < k := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hx : 1 < x := by dsimp [x]; exact_mod_cast Nat.lt_add_one_iff.mpr hn
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hchooseNat : a.choose 2 ≤ a ^ 2 := Nat.choose_le_pow _ _
  have hchoose : (((a.choose 2 : ℕ) : ℝ)) ≤ (a : ℝ) ^ 2 := by
    exact_mod_cast hchooseNat
  have hT := (extensionCap_bounds hn).1
  have htarget : extensionTarget n =
      100 * (a : ℝ) ^ 2 / k +
        10 * (b : ℝ) * (a + 1 : ℕ) * Real.log (n + 1) := rfl
  have hTdiv :
      (100 * (a : ℝ) ^ 2 / k +
          10 * (b : ℝ) * (a + 1 : ℕ) * Real.log (n + 1)) / b ≤
        (extensionCap n : ℝ) / b := by
    rw [← htarget]
    exact div_le_div_of_nonneg_right hT hbR.le
  have hdivide :
      (100 * (a : ℝ) ^ 2 / k +
          10 * (b : ℝ) * (a + 1 : ℕ) * Real.log (n + 1)) / b =
        100 * (a : ℝ) ^ 2 / (k * b) +
          10 * (a + 1 : ℕ) * Real.log (n + 1) := by
    field_simp
  rw [hdivide] at hTdiv
  have hexponent :
      2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) -
          (extensionCap n : ℝ) / b ≤
        -10 * (a + 1 : ℕ) * Real.log (n + 1) := by
    have hnonneg : 0 ≤ (a : ℝ) ^ 2 / ((k : ℝ) * b) := by positivity
    have hchooseDiv :
        2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) ≤
          2 * (a : ℝ) ^ 2 / ((k : ℝ) * b) := by gcongr
    calc
      2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) -
          (extensionCap n : ℝ) / b ≤
        2 * (a : ℝ) ^ 2 / ((k : ℝ) * b) -
          (extensionCap n : ℝ) / b := sub_le_sub_right hchooseDiv _
      _ ≤ 2 * (a : ℝ) ^ 2 / ((k : ℝ) * b) -
          (100 * (a : ℝ) ^ 2 / ((k : ℝ) * b) +
            10 * (a + 1 : ℕ) * Real.log (n + 1)) :=
        sub_le_sub_left hTdiv _
      _ = -98 * ((a : ℝ) ^ 2 / ((k : ℝ) * b)) -
          10 * (a + 1 : ℕ) * Real.log (n + 1) := by ring
      _ ≤ -10 * (a + 1 : ℕ) * Real.log (n + 1) := by linarith
  have hpowexp : (x : ℝ) ^ (a + 1) =
      Real.exp (((a + 1 : ℕ) : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < x)]
  have hmain :
      (x : ℝ) ^ (a + 1) *
          Real.exp (2 * (((a.choose 2 : ℕ) : ℝ)) / ((k : ℝ) * b) -
            (extensionCap n : ℝ) / b) ≤
        Real.exp (-2 * Real.log x) := by
    rw [hpowexp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have haone : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by norm_num
    have hlogrewrite : Real.log (n + 1) = Real.log x := by rfl
    rw [hlogrewrite] at hexponent
    nlinarith
  calc
    (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
      Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
        ((sampleColors n : ℝ) * weightCutoff n) -
          (extensionCap n : ℝ) / weightCutoff n)) ≤
        Real.exp (-2 * Real.log x) := by simpa [a, b, k, x] using hmain
    _ = 1 / x ^ 2 := by
      rw [show -2 * Real.log x = -(2 * Real.log x) by ring, Real.exp_neg]
      rw [show (2 : ℝ) * Real.log x = (2 : ℕ) * Real.log x by norm_num,
        Real.exp_nat_mul, Real.exp_log (by linarith : 0 < x)]
      simp [one_div]
    _ = 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by simp [x]

/-! ## Elementary eventual power estimates -/

lemma eventually_log_le_rpow_nat {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≤ (n : ℝ) ^ r := by
  have hsmall : (fun n : ℕ ↦ Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ r) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [hsmall.eventuallyLE, eventually_gt_atTop 1] with n hn hn1
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  have hpow : 0 < (n : ℝ) ^ r :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) _
  simpa [Real.norm_eq_abs, abs_of_pos hlog, abs_of_pos hpow] using hn

lemma eventually_const_le_rpow_nat (C : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ r := by
  exact ((tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop C)

lemma eventually_two_thousand_le_log :
    ∀ᶠ n : ℕ in atTop, 2000 ≤ Real.log (n : ℝ) := by
  exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop 2000)

lemma log_succ_le_two_mul_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hsquare : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast (show n + 1 ≤ n ^ 2 by nlinarith)
  calc
    Real.log ((n + 1 : ℕ) : ℝ) ≤ Real.log ((n : ℝ) ^ 2) :=
      Real.log_le_log (by positivity) hsquare
    _ = 2 * Real.log n := by rw [Real.log_pow]; norm_num

lemma sampleRoot_pow_five {n : ℕ} (hn : 0 < n) :
    (sampleRoot n) ^ 5 = (n : ℝ) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (sampleRoot n) ^ 5 =
        ((n : ℝ) ^ ((9 : ℝ) / 20)) ^ ((5 : ℕ) : ℝ) := by
      dsimp [sampleRoot]
      exact (Real.rpow_natCast ((n : ℝ) ^ ((9 : ℝ) / 20)) 5).symm
    _ = (n : ℝ) ^ (((9 : ℝ) / 20) * 5) := by
      exact (Real.rpow_mul hnR.le _ _).symm
    _ = (n : ℝ) ^ ((9 : ℝ) / 4) := by norm_num
    _ = (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hnR]
      norm_num
    _ = (n : ℝ) ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 4) := by
      congr 1
      exact Real.rpow_natCast n 2

lemma quotient_sampleRoot {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / sampleRoot n = (n : ℝ) ^ ((11 : ℝ) / 20) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    (n : ℝ) / sampleRoot n =
        (n : ℝ) ^ (1 : ℝ) / (n : ℝ) ^ ((9 : ℝ) / 20) := by
      rw [sampleRoot, Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) - (9 : ℝ) / 20) :=
      (Real.rpow_sub hnR _ _).symm
    _ = (n : ℝ) ^ ((11 : ℝ) / 20) := by norm_num

lemma lowerScale_le_rpow {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    lowerScale n ≤ (n : ℝ) ^ ((51 : ℝ) / 100) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  rw [lowerScale, Real.sqrt_le_iff]
  constructor
  · exact (Real.rpow_pos_of_pos hnpos _).le
  · have hmul : (n : ℝ) * Real.log n ≤
        (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 100) := by gcongr
    calc
      (n : ℝ) * Real.log n ≤
          (n : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 100) := hmul
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ ((1 : ℝ) / 100) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (1 : ℝ) / 100) :=
        (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ) ^ ((101 : ℝ) / 100) := by
        norm_num
      _ ≤ (n : ℝ) ^ ((102 : ℝ) / 100) :=
        Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
      _ = ((n : ℝ) ^ ((51 : ℝ) / 100)) ^ 2 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hnpos.le]
        norm_num

lemma four_pow_weightCutoff_le {n : ℕ} (hn : 1 ≤ n) :
    (((4 ^ weightCutoff n : ℕ) : ℝ)) ≤
      (n : ℝ) ^ ((1 : ℝ) / 500) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hB := weightCutoff_upper hn
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hexponent : (weightCutoff n : ℝ) * Real.log 4 ≤
      Real.log n / 500 := by
    calc
      (weightCutoff n : ℝ) * Real.log 4 ≤
          (Real.log n / 1000) * Real.log 4 := by gcongr
      _ ≤ (Real.log n / 1000) * 2 := by gcongr; exact log_four_lt_two.le
      _ = Real.log n / 500 := by ring
  have hpowexp : ((4 : ℝ) ^ weightCutoff n) =
      Real.exp ((weightCutoff n : ℝ) * Real.log 4) := by
    symm
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  calc
    (((4 ^ weightCutoff n : ℕ) : ℝ)) = (4 : ℝ) ^ weightCutoff n := by norm_num
    _ = Real.exp ((weightCutoff n : ℝ) * Real.log 4) := hpowexp
    _ ≤ Real.exp (Real.log n / 500) := Real.exp_le_exp.mpr hexponent
    _ = (n : ℝ) ^ ((1 : ℝ) / 500) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      ring

/-! ## The sampling-score inequality -/

lemma triangle_loss_le {n : ℕ} (hn : 1 ≤ n)
    (hquarter : 8 ≤ (n : ℝ) ^ ((1 : ℝ) / 4)) :
    (((n ^ 3 : ℕ) : ℝ) / (sampleColors n : ℝ) ^ 6) ≤
      (n : ℝ) / (8 * sampleColors n) := by
  let x : ℝ := n
  let k : ℝ := sampleColors n
  have hx : 0 < x := by dsimp [x]; positivity
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hroot := (sampleColors_bounds hn).1
  have hcore : 8 * x ^ 2 ≤ k ^ 5 := by
    calc
      8 * x ^ 2 ≤ x ^ ((1 : ℝ) / 4) * x ^ 2 := by
        gcongr
      _ = (sampleRoot n) ^ 5 := by
        rw [sampleRoot_pow_five (by omega : 0 < n)]
        ring
      _ ≤ k ^ 5 := by
        exact pow_le_pow_left₀ (sampleRoot_pos (by omega)).le hroot 5
  have hcross : x ^ 3 * (8 * k) ≤ x * k ^ 6 := by
    calc
      x ^ 3 * (8 * k) = (x * k) * (8 * x ^ 2) := by ring
      _ ≤ (x * k) * k ^ 5 := by gcongr
      _ = x * k ^ 6 := by ring
  rw [div_le_div_iff₀ (pow_pos hk 6) (mul_pos (by norm_num) hk)]
  simpa only [x, k, Nat.cast_pow] using hcross

lemma sampleColors_le_n {n : ℕ} (hn : 1 ≤ n)
    (hpower : 2 ≤ (n : ℝ) ^ ((11 : ℝ) / 20)) :
    (sampleColors n : ℝ) ≤ n := by
  have hr := (sampleColors_bounds hn).2
  have hq := quotient_sampleRoot (by omega : 0 < n)
  have hrootpos := sampleRoot_pos (by omega : 0 < n)
  rw [← hq] at hpower
  have hmul := mul_le_mul_of_nonneg_right hpower hrootpos.le
  have hncast : (n : ℝ) / sampleRoot n * sampleRoot n = n := by
    field_simp
  linarith

lemma bad_loss_le {n : ℕ} (hn : 6 ≤ n)
    (hpower : 2 ≤ (n : ℝ) ^ ((11 : ℝ) / 20))
    (hB : 0 < weightCutoff n) :
    (n : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
          Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
            ((sampleColors n : ℝ) * weightCutoff n) -
              (extensionCap n : ℝ) / weightCutoff n)) ≤
      (n : ℝ) / (8 * sampleColors n) := by
  have hq := extensionBadBound_le (show 1 ≤ n by omega) hB
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hk : (0 : ℝ) < sampleColors n := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hkn : (sampleColors n : ℝ) ≤ n :=
    sampleColors_le_n (show 1 ≤ n by omega) hpower
  have hden : (8 : ℝ) * sampleColors n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have h8n : (8 : ℝ) * n ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      push_cast
      have hn' : (6 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 3)]
    exact (mul_le_mul_of_nonneg_left hkn (by norm_num)).trans h8n
  calc
    (n : ℝ) *
        (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
          Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
            ((sampleColors n : ℝ) * weightCutoff n) -
              (extensionCap n : ℝ) / weightCutoff n)) ≤
        (n : ℝ) * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by gcongr
    _ ≤ (n : ℝ) * (1 / ((8 : ℝ) * sampleColors n)) := by
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le (by positivity) hden) hn0
    _ = (n : ℝ) / (8 * sampleColors n) := by ring

theorem eventually_sampling_score :
    ∀ᶠ n : ℕ in atTop,
      0 < weightCutoff n ∧ 0 < sampleTarget n ∧
      sampleTarget n ≤
        (n : ℝ) / sampleColors n -
          (((n ^ 3 : ℕ) : ℝ) / (sampleColors n : ℝ) ^ 6) -
          (n : ℝ) *
            (((n + 1 : ℕ) : ℝ) ^ (independenceCutoff n + 1) *
              Real.exp (2 * (((independenceCutoff n).choose 2 : ℕ) : ℝ) /
                ((sampleColors n : ℝ) * weightCutoff n) -
                  (extensionCap n : ℝ) / weightCutoff n)) := by
  filter_upwards [eventually_ge_atTop 6, eventually_two_thousand_le_log,
    eventually_const_le_rpow_nat 8 (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_const_le_rpow_nat 2 (by norm_num : (0 : ℝ) < 11 / 20)]
      with n hn hlog hquarter hpower
  have hB : 0 < weightCutoff n := by
    have hlower := weightCutoff_lower hlog
    have : (1 : ℝ) ≤ weightCutoff n := by linarith
    exact_mod_cast this
  have hk : (0 : ℝ) < sampleColors n := by
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have htri := triangle_loss_le (show 1 ≤ n by omega) hquarter
  have hbad := bad_loss_le hn hpower hB
  have hratio : (n : ℝ) / sampleColors n =
      8 * ((n : ℝ) / (8 * sampleColors n)) := by field_simp
  have htarget : sampleTarget n =
      4 * ((n : ℝ) / (8 * sampleColors n)) := by
    unfold sampleTarget
    field_simp
    ring
  refine ⟨hB, ?_, ?_⟩
  · unfold sampleTarget
    positivity
  · rw [htarget, hratio]
    have hq0 : (0 : ℝ) ≤ n / (8 * sampleColors n) := by positivity
    linarith

/-! ## The weighted contradiction inequality -/

lemma independenceCutoff_le_rpow {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    (independenceCutoff n : ℝ) ≤
      lowerConstant * (n : ℝ) ^ ((51 : ℝ) / 100) := by
  exact (independenceCutoff_upper hn).trans
    (mul_le_mul_of_nonneg_left (lowerScale_le_rpow hn hlog) lowerConstant_pos.le)

lemma independenceCutoff_le_plain_rpow {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    (independenceCutoff n : ℝ) ≤
      (n : ℝ) ^ ((51 : ℝ) / 100) := by
  have hc : lowerConstant ≤ 1 := by norm_num [lowerConstant]
  exact (independenceCutoff_le_rpow hn hlog).trans <| by
    exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) hc

lemma pivot_allocation {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    128 * (sampleColors n : ℝ) * independenceCutoff n *
        ((4 ^ weightCutoff n : ℕ) : ℝ) ≤ n := by
  let x : ℝ := n
  have hx : 1 ≤ x := by dsimp [x]; exact_mod_cast hn
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hK := (sampleColors_bounds hn).2
  have hA := independenceCutoff_le_rpow hn hlog
  have hfour := four_pow_weightCutoff_le hn
  have hK' : (sampleColors n : ℝ) ≤ 2 * x ^ ((9 : ℝ) / 20) := by
    simpa [x, sampleRoot] using hK
  have hA' : (independenceCutoff n : ℝ) ≤
      lowerConstant * x ^ ((51 : ℝ) / 100) := by simpa [x] using hA
  have hfour' : (((4 ^ weightCutoff n : ℕ) : ℝ)) ≤
      x ^ ((1 : ℝ) / 500) := by simpa [x] using hfour
  have hc0 : 0 ≤ lowerConstant := lowerConstant_pos.le
  have hpows :
      x ^ ((9 : ℝ) / 20) * x ^ ((51 : ℝ) / 100) *
          x ^ ((1 : ℝ) / 500) = x ^ ((481 : ℝ) / 500) := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    norm_num
  calc
    128 * (sampleColors n : ℝ) * independenceCutoff n *
        ((4 ^ weightCutoff n : ℕ) : ℝ) ≤
      128 * (2 * x ^ ((9 : ℝ) / 20)) *
        (lowerConstant * x ^ ((51 : ℝ) / 100)) *
          x ^ ((1 : ℝ) / 500) := by
            gcongr
    _ = (256 * lowerConstant) * x ^ ((481 : ℝ) / 500) := by
      rw [← hpows]
      ring
    _ ≤ x ^ ((481 : ℝ) / 500) := by
      have hc : 256 * lowerConstant ≤ 1 := by norm_num [lowerConstant]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hxpos.le _) hc
    _ ≤ x ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = n := by simp [x]

lemma square_allocation {n : ℕ} (hn : 1 ≤ n)
    (hlog : 2000 ≤ Real.log (n : ℝ)) :
    12800 * (independenceCutoff n : ℝ) ^ 2 ≤
      (weightCutoff n : ℝ) * n := by
  have hA := independenceCutoff_upper hn
  have hA0 : (0 : ℝ) ≤ independenceCutoff n := by positivity
  have hcscale0 : 0 ≤ lowerConstant * lowerScale n :=
    mul_nonneg lowerConstant_pos.le (lowerScale_nonneg n)
  have hsq : (independenceCutoff n : ℝ) ^ 2 ≤
      (lowerConstant * lowerScale n) ^ 2 := by
    nlinarith [sq_nonneg
      ((lowerConstant * lowerScale n) - independenceCutoff n)]
  have hB := weightCutoff_lower hlog
  have hlog0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  calc
    12800 * (independenceCutoff n : ℝ) ^ 2 ≤
        12800 * (lowerConstant * lowerScale n) ^ 2 := by gcongr
    _ = (12800 * lowerConstant ^ 2) *
        ((n : ℝ) * Real.log n) := by
      rw [mul_pow, lowerScale_sq hn]
      ring
    _ ≤ (1 / 2000 : ℝ) * ((n : ℝ) * Real.log n) := by
      have hc : 12800 * lowerConstant ^ 2 ≤ (1 / 2000 : ℝ) := by
        norm_num [lowerConstant]
      gcongr
    _ = (Real.log n / 2000) * n := by ring
    _ ≤ (weightCutoff n : ℝ) * n := by gcongr

lemma logarithmic_allocation {n : ℕ} (hn : 2 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100))
    (hpower : 10240 ≤ (n : ℝ) ^ ((3 : ℝ) / 100)) :
    1280 * (sampleColors n : ℝ) * (independenceCutoff n + 1 : ℕ) *
        Real.log (n + 1) ≤ n := by
  let x : ℝ := n
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast (show 1 ≤ n by omega)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hK := (sampleColors_bounds (show 1 ≤ n by omega)).2
  have hA := independenceCutoff_le_plain_rpow (show 1 ≤ n by omega) hlog
  have hxpow : 1 ≤ x ^ ((51 : ℝ) / 100) :=
    Real.one_le_rpow hx (by norm_num)
  have hAplus : ((independenceCutoff n + 1 : ℕ) : ℝ) ≤
      2 * x ^ ((51 : ℝ) / 100) := by
    push_cast
    dsimp [x] at hA ⊢
    linarith
  have hlogs : Real.log ((n + 1 : ℕ) : ℝ) ≤
      2 * x ^ ((1 : ℝ) / 100) := by
    calc
      Real.log ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.log n :=
        log_succ_le_two_mul_log hn
      _ ≤ 2 * x ^ ((1 : ℝ) / 100) := by
        dsimp [x]
        gcongr
  have hK' : (sampleColors n : ℝ) ≤ 2 * x ^ ((9 : ℝ) / 20) := by
    simpa [x, sampleRoot] using hK
  have hlognonneg : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hpows :
      x ^ ((9 : ℝ) / 20) * x ^ ((51 : ℝ) / 100) *
          x ^ ((1 : ℝ) / 100) = x ^ ((97 : ℝ) / 100) := by
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    norm_num
  calc
    1280 * (sampleColors n : ℝ) * (independenceCutoff n + 1 : ℕ) *
        Real.log (n + 1) ≤
      1280 * (2 * x ^ ((9 : ℝ) / 20)) *
        (2 * x ^ ((51 : ℝ) / 100)) *
          (2 * x ^ ((1 : ℝ) / 100)) := by
            gcongr
            · simpa using hlognonneg
            · simpa using hlogs
    _ = 10240 * x ^ ((97 : ℝ) / 100) := by
      rw [← hpows]
      ring
    _ ≤ x ^ ((3 : ℝ) / 100) * x ^ ((97 : ℝ) / 100) := by
      gcongr
    _ = x ^ (1 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num
    _ = n := by simp [x]

lemma ceiling_allocation {n : ℕ} (hn : 1 ≤ n)
    (hpower : 256 ≤ (n : ℝ) ^ ((11 : ℝ) / 20))
    (hB : 1 ≤ weightCutoff n) :
    128 * (sampleColors n : ℝ) ≤ (weightCutoff n : ℝ) * n := by
  have hK := (sampleColors_bounds hn).2
  have hroot : 256 * sampleRoot n ≤ n := by
    have hq := quotient_sampleRoot (by omega : 0 < n)
    have hrpos := sampleRoot_pos (by omega : 0 < n)
    rw [← hq] at hpower
    have := mul_le_mul_of_nonneg_right hpower hrpos.le
    have hncast : (n : ℝ) / sampleRoot n * sampleRoot n = n := by
      field_simp
    linarith
  have h128K : 128 * (sampleColors n : ℝ) ≤ n := by
    calc
      128 * (sampleColors n : ℝ) ≤ 128 * (2 * sampleRoot n) := by gcongr
      _ = 256 * sampleRoot n := by ring
      _ ≤ n := hroot
  have hBcast : (1 : ℝ) ≤ weightCutoff n := by exact_mod_cast hB
  exact h128K.trans <| by
    calc
      (n : ℝ) = 1 * n := by ring
      _ ≤ (weightCutoff n : ℝ) * n := by gcongr

theorem eventually_weighted_inequality :
    ∀ᶠ n : ℕ in atTop,
      ((8 * (independenceCutoff n *
          (weightCutoff n * 4 ^ weightCutoff n) + extensionCap n) : ℕ) : ℝ) <
        (weightCutoff n : ℝ) * sampleTarget n := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_log_le_rpow_nat (by norm_num : (0 : ℝ) < 1 / 100),
    eventually_two_thousand_le_log,
    eventually_const_le_rpow_nat 10240 (by norm_num : (0 : ℝ) < 3 / 100),
    eventually_const_le_rpow_nat 256 (by norm_num : (0 : ℝ) < 11 / 20)]
      with n hn hlog hlogLower h10240 h256
  let K : ℝ := sampleColors n
  let A : ℝ := independenceCutoff n
  let B : ℝ := weightCutoff n
  let P : ℝ := ((4 ^ weightCutoff n : ℕ) : ℝ)
  let T : ℝ := extensionCap n
  let x : ℝ := n
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast sampleColors_pos (by omega : 0 < n)
  have hBnat : 0 < weightCutoff n := by
    have hlower := weightCutoff_lower hlogLower
    have : (1 : ℝ) ≤ weightCutoff n := by linarith
    exact_mod_cast this
  have hB : 0 < B := by dsimp [B]; exact_mod_cast hBnat
  have hx : 0 < x := by dsimp [x]; positivity
  have hpivot := pivot_allocation (show 1 ≤ n by omega) hlog
  have hsquare := square_allocation (show 1 ≤ n by omega) hlogLower
  have hlogarithmic := logarithmic_allocation hn hlog h10240
  have hceiling := ceiling_allocation (show 1 ≤ n by omega) h256 hBnat
  have hTcap := (extensionCap_bounds (show 1 ≤ n by omega)).2
  have hTupper : T ≤
      100 * A ^ 2 / K + 10 * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
        Real.log (n + 1) + 1 := by
    simpa [T, extensionTarget, A, B, K] using hTcap
  have hsum :
      16 * K * (A * (B * P) + T) < B * x := by
    have hmajor :
        16 * K * (A * (B * P) + T) ≤
          16 * K * A * B * P + 1600 * A ^ 2 +
            160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
              Real.log (n + 1) + 16 * K := by
      calc
        16 * K * (A * (B * P) + T) ≤
            16 * K * (A * (B * P) +
              (100 * A ^ 2 / K +
                10 * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
                  Real.log (n + 1) + 1)) := by gcongr
        _ = 16 * K * A * B * P + 1600 * A ^ 2 +
            160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
              Real.log (n + 1) + 16 * K := by
          field_simp
          ring
    have hpivot' : 8 * (16 * K * A * B * P) ≤ B * x := by
      have hpivot0 : 128 * K * A * P ≤ x := by
        simpa [K, A, P, x] using hpivot
      calc
        8 * (16 * K * A * B * P) = B * (128 * K * A * P) := by ring
        _ ≤ B * x := mul_le_mul_of_nonneg_left hpivot0 hB.le
    have hsquare' : 8 * (1600 * A ^ 2) ≤ B * x := by
      calc
        8 * (1600 * A ^ 2) = 12800 * A ^ 2 := by ring
        _ ≤ B * x := by simpa [A, B, x] using hsquare
    have hlogarithmic' :
        8 * (160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
          Real.log (n + 1)) ≤ B * x := by
      have hlogarithmic0 :
          1280 * K * ((independenceCutoff n + 1 : ℕ) : ℝ) *
            Real.log (n + 1) ≤ x := by
        simpa [K, x] using hlogarithmic
      calc
        8 * (160 * K * B * ((independenceCutoff n + 1 : ℕ) : ℝ) *
            Real.log (n + 1)) =
          B * (1280 * K * ((independenceCutoff n + 1 : ℕ) : ℝ) *
            Real.log (n + 1)) := by ring
        _ ≤ B * x := mul_le_mul_of_nonneg_left hlogarithmic0 hB.le
    have hceiling' : 8 * (16 * K) ≤ B * x := by
      calc
        8 * (16 * K) = 128 * K := by ring
        _ ≤ B * x := by simpa [K, B, x] using hceiling
    have hBx : 0 < B * x := mul_pos hB hx
    nlinarith
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  change 8 * (A * (B * ((4 : ℝ) ^ weightCutoff n)) + T) <
    B * (x / (2 * K))
  rw [show B * (x / (2 * K)) = B * x / (2 * K) by ring,
    lt_div_iff₀ (mul_pos (by norm_num) hK)]
  have hpow : ((4 : ℝ) ^ weightCutoff n) = P := by
    simp [P]
  rw [hpow]
  nlinarith

lemma independenceCutoff_le_n {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    independenceCutoff n ≤ n := by
  have hA := independenceCutoff_le_plain_rpow hn hlog
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ ((51 : ℝ) / 100) ≤ (n : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
  have : (independenceCutoff n : ℝ) ≤ n := by
    simpa using hA.trans hpow
  exact_mod_cast this

/-- For every sufficiently large order, every linear triple system has an
independent set strictly larger than the explicit floor cutoff. -/
theorem eventually_exists_independent_gt :
    ∀ᶠ n : ℕ in atTop, ∀ H : System (Fin n),
      ThreeUniform H → Linear H →
        ∃ I : Finset (Fin n), Independent H I ∧
          independenceCutoff n < I.card := by
  filter_upwards [eventually_sampling_score, eventually_weighted_inequality,
    eventually_ge_atTop 1,
    eventually_log_le_rpow_nat (by norm_num : (0 : ℝ) < 1 / 100)]
      with n hscore hweighted hn hlog
  intro H h3 hlin
  let : NeZero (sampleColors n) :=
    ⟨(sampleColors_pos (by omega : 0 < n)).ne'⟩
  apply exists_independent_gt_of_parameters h3 hlin
    (K := sampleColors n) (A := independenceCutoff n)
    (B := weightCutoff n) (T := extensionCap n)
    (L := sampleTarget n)
  · exact hscore.1
  · simpa using independenceCutoff_le_n hn hlog
  · exact hscore.2.1
  · simpa using hscore.2.2
  · exact hweighted

end Lower
end Erdos1024
