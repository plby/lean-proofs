/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos1165.HLOZShellZeroCentralNumerics
import ErdosProblems.Erdos1165.HLOZShellZeroReplacementNumerics

/-!
# Summing the exact central shell-zero counts

The HLOZ replacement is performed separately after fixing the exact number
`r` of source-window coordinates.  Its retained source count is
`floor (C / (1 + C) * r)`.  This file proves that the resulting exact-count
coefficients have a geometric tail.  In particular, it does not replace the
fixed-count construction by the union over every mixture.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.HLOZShellZeroCentralTail

open HLOZShellZeroCentralCount HLOZShellZeroCentralNumerics
open HLOZShellZeroReplacementProduct HLOZShellZeroReplacementNumerics
open HLOZProposition48Candidates

noncomputable section

/-- The Bernoulli parameter corresponding to the one-coordinate comparison. -/
def centralParameter (C : ℝ) : ℝ := C / (1 + C)

lemma centralParameter_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ centralParameter C := by
  unfold centralParameter
  exact div_nonneg hC (by linarith)

lemma centralParameter_lt_one {C : ℝ} (hC : 0 ≤ C) :
    centralParameter C < 1 := by
  unfold centralParameter
  exact (div_lt_one₀ (by linarith)).2 (by linarith)

lemma replacementBase_eq_average (C : ℝ) :
    replacementBase C = (1 + centralParameter C) / 2 := rfl

lemma centralParameter_lt_replacementBase {C : ℝ} (hC : 0 ≤ C) :
    centralParameter C < replacementBase C := by
  rw [replacementBase_eq_average]
  linarith [centralParameter_lt_one hC]

lemma centralReplacementRatio_nonneg {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    0 ≤ centralReplacementRatio C r := by
  unfold centralReplacementRatio
  apply div_nonneg
  · exact pow_nonneg hC _
  · positivity

/-- The exact central coefficient is at most a linear factor times the
geometric parameter `C/(1+C)` to the exact source count. -/
theorem centralReplacementRatio_le_linear_geometric
    {C : ℝ} (hC : 0 < C) (r : ℕ) :
    centralReplacementRatio C r ≤
      (((r + 1 : ℕ) : ℝ) * (1 + C)) * centralParameter C ^ r := by
  let s := centralReplacementUpperCount C r
  have hs : s ≤ r := centralReplacementUpperCount_le hC.le r
  have hchooseNat : 0 < r.choose s := Nat.choose_pos hs
  have hchoose : (0 : ℝ) < r.choose s := by exact_mod_cast hchooseNat
  have hden : 0 < (1 + C) ^ r := pow_pos (by linarith) _
  have hmode := one_add_pow_le_central hC.le r
  unfold centralReplacementRatio
  change C ^ (r - s) / (r.choose s : ℝ) ≤ _
  rw [div_le_iff₀ hchoose]
  unfold centralParameter
  rw [div_pow]
  rw [show
      ((((r + 1 : ℕ) : ℝ) * (1 + C)) *
          (C ^ r / (1 + C) ^ r)) * (r.choose s : ℝ) =
        (((((r + 1 : ℕ) : ℝ) * (1 + C)) * C ^ r) *
          (r.choose s : ℝ)) / (1 + C) ^ r by ring]
  rw [le_div_iff₀ hden]
  have hmul := mul_le_mul_of_nonneg_left hmode (pow_nonneg hC.le (r - s))
  calc
    C ^ (r - s) * (1 + C) ^ r ≤
        C ^ (r - s) *
          ((((r + 1 : ℕ) : ℝ) * (1 + C)) *
            weightedChoose C r s) := hmul
    _ = ((((r + 1 : ℕ) : ℝ) * (1 + C)) * C ^ r) *
          (r.choose s : ℝ) := by
      unfold weightedChoose
      have hpow : C ^ (r - s) * C ^ s = C ^ r := by
        rw [← pow_add, Nat.sub_add_cancel hs]
      rw [show C ^ (r - s) *
          ((((r + 1 : ℕ) : ℝ) * (1 + C)) *
            ((r.choose s : ℝ) * C ^ s)) =
          (((r + 1 : ℕ) : ℝ) * (1 + C)) *
            (C ^ (r - s) * C ^ s) * (r.choose s : ℝ) by ring,
        hpow]

/-- Ratio between the true geometric parameter and the slightly larger
replacement base. -/
def centralBaseRatio (C : ℝ) : ℝ :=
  centralParameter C / replacementBase C

lemma centralBaseRatio_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ centralBaseRatio C := by
  unfold centralBaseRatio
  exact div_nonneg (centralParameter_nonneg hC)
    (replacementBase_pos hC).le

lemma centralBaseRatio_lt_one {C : ℝ} (hC : 0 ≤ C) :
    centralBaseRatio C < 1 := by
  unfold centralBaseRatio
  exact (div_lt_one₀ (replacementBase_pos hC)).2
    (centralParameter_lt_replacementBase hC)

/-- A fixed constant dominating the linear loss in the exact-count mode
estimate. -/
def centralTailConstant (C : ℝ) : ℝ :=
  (1 + C) / (1 - centralBaseRatio C) ^ 2

lemma centralTailConstant_nonneg {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ centralTailConstant C := by
  unfold centralTailConstant
  exact div_nonneg (by linarith) (sq_nonneg _)

lemma nat_succ_mul_pow_le_inv_one_sub_sq
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (r : ℕ) :
    (((r + 1 : ℕ) : ℝ) * q ^ r) ≤ 1 / (1 - q) ^ 2 := by
  have hnorm : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq0]
  have hsum := summable_choose_mul_geometric_of_norm_lt_one
    (R := ℝ) 1 hnorm
  have hterm := hsum.le_tsum r (fun n _ ↦ by positivity)
  rw [tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hnorm] at hterm
  have hpow : (1 - q) ^ (1 + 1) = (1 - q) ^ 2 := by norm_num
  rw [hpow] at hterm
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using hterm

/-- Uniform geometric majorant for every exact central-count coefficient. -/
theorem centralReplacementRatio_le_tailConstant_mul_pow
    {C : ℝ} (hC : 0 < C) (r : ℕ) :
    centralReplacementRatio C r ≤
      centralTailConstant C * replacementBase C ^ r := by
  let p := centralParameter C
  let b := replacementBase C
  let q := centralBaseRatio C
  have hb : 0 < b := replacementBase_pos hC.le
  have hq0 : 0 ≤ q := centralBaseRatio_nonneg hC.le
  have hq1 : q < 1 := centralBaseRatio_lt_one hC.le
  have hpqb : p = q * b := by
    dsimp only [p, q, b, centralBaseRatio]
    exact (div_mul_cancel₀ (centralParameter C)
      (replacementBase_pos hC.le).ne').symm
  have hlinear := centralReplacementRatio_le_linear_geometric hC r
  have hseries := nat_succ_mul_pow_le_inv_one_sub_sq hq0 hq1 r
  calc
    centralReplacementRatio C r ≤
        (((r + 1 : ℕ) : ℝ) * (1 + C)) * p ^ r := hlinear
    _ = (1 + C) * ((((r + 1 : ℕ) : ℝ) * q ^ r) * b ^ r) := by
      rw [hpqb, mul_pow]
      ring
    _ ≤ (1 + C) * ((1 / (1 - q) ^ 2) * b ^ r) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hseries (pow_nonneg hb.le _))
        (by linarith)
    _ = centralTailConstant C * replacementBase C ^ r := by
      dsimp only [centralTailConstant, q, b]
      ring

/-- Exact reindexed tail of the fixed-count coefficients, beginning at
`cut + 1`. -/
def centralReplacementTailCost (C : ℝ) (cut : ℕ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal
    (centralReplacementRatio C (cut + 1 + n))

/-- A closed geometric majorant for the exact-count tail. -/
def centralReplacementTailMajorant (C : ℝ) (cut : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (centralTailConstant C) *
    ENNReal.ofReal (replacementBase C) ^ (cut + 1) *
      (1 - ENNReal.ofReal (replacementBase C))⁻¹

/-- Real prefactor left after summing the geometric tail in the exact
source count. -/
def centralTailPrefactor (C : ℝ) : ℝ :=
  centralTailConstant C / (1 - replacementBase C)

lemma centralTailPrefactor_pos {C : ℝ} (hC : 0 < C) :
    0 < centralTailPrefactor C := by
  unfold centralTailPrefactor centralTailConstant
  have hq : centralBaseRatio C < 1 := centralBaseRatio_lt_one hC.le
  have hb : replacementBase C < 1 := replacementBase_lt_one hC.le
  positivity

lemma centralReplacementTailMajorant_initialBudget_eq_prefactor_mul
    {C : ℝ} (hC : 0 < C) (m : ℕ) :
    centralReplacementTailMajorant C (initialBudget48 m) =
      ENNReal.ofReal (centralTailPrefactor C) *
        fixedReplacementCost C m := by
  unfold centralReplacementTailMajorant centralTailPrefactor
    fixedReplacementCost
  have hb0 : 0 ≤ replacementBase C := replacementBase_nonneg hC.le
  have hb1 : replacementBase C < 1 := replacementBase_lt_one hC.le
  rw [ENNReal.ofReal_div_of_pos (sub_pos.mpr hb1),
    ENNReal.ofReal_sub 1 hb0, ENNReal.ofReal_one,
    ← ENNReal.ofReal_pow hb0]
  simp only [div_eq_mul_inv]
  ring

theorem centralReplacementTailCost_le_majorant
    {C : ℝ} (hC : 0 < C) (cut : ℕ) :
    centralReplacementTailCost C cut ≤
      centralReplacementTailMajorant C cut := by
  unfold centralReplacementTailCost centralReplacementTailMajorant
  calc
    (∑' n : ℕ, ENNReal.ofReal
        (centralReplacementRatio C (cut + 1 + n))) ≤
        ∑' n : ℕ, ENNReal.ofReal
          (centralTailConstant C *
            replacementBase C ^ (cut + 1 + n)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      exact ENNReal.ofReal_mono
        (centralReplacementRatio_le_tailConstant_mul_pow hC _)
    _ = ∑' n : ℕ,
          ENNReal.ofReal (centralTailConstant C) *
            ENNReal.ofReal (replacementBase C) ^ (cut + 1) *
              ENNReal.ofReal (replacementBase C) ^ n := by
      apply tsum_congr
      intro n
      rw [pow_add,
        ENNReal.ofReal_mul (centralTailConstant_nonneg hC.le),
        ENNReal.ofReal_mul (pow_nonneg (replacementBase_nonneg hC.le) _),
        ENNReal.ofReal_pow (replacementBase_nonneg hC.le),
        ENNReal.ofReal_pow (replacementBase_nonneg hC.le)]
      ring
    _ = ENNReal.ofReal (centralTailConstant C) *
          ENNReal.ofReal (replacementBase C) ^ (cut + 1) *
            ∑' n : ℕ, ENNReal.ofReal (replacementBase C) ^ n := by
      rw [← ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (centralTailConstant C) *
          ENNReal.ofReal (replacementBase C) ^ (cut + 1) *
            (1 - ENNReal.ofReal (replacementBase C))⁻¹ := by
      rw [ENNReal.tsum_geometric]

/-- The closed majorants are summable at the HLOZ logarithmic-square
initial cut. -/
theorem tsum_centralReplacementTailMajorant_ne_top {C : ℝ} (hC : 0 < C) :
    ∑' m : ℕ,
      centralReplacementTailMajorant C (initialBudget48 m) ≠ ∞ := by
  let K : ℝ≥0∞ := ENNReal.ofReal (centralTailConstant C) *
    (1 - ENNReal.ofReal (replacementBase C))⁻¹
  have hK : K ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.ofReal_ne_top
    · apply ENNReal.inv_ne_top.mpr
      exact ne_of_gt (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr
        (replacementBase_lt_one hC.le)))
  have hcost := tsum_fixedReplacementCost_ne_top hC.le
  have heq : ∀ m,
      centralReplacementTailMajorant C (initialBudget48 m) =
        K * fixedReplacementCost C m := by
    intro m
    unfold centralReplacementTailMajorant fixedReplacementCost K
    rw [← ENNReal.ofReal_pow (replacementBase_nonneg hC.le)]
    ring
  simp_rw [heq]
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top hK hcost

theorem tsum_centralReplacementTailCost_ne_top {C : ℝ} (hC : 0 < C) :
    ∑' m : ℕ, centralReplacementTailCost C (initialBudget48 m) ≠ ∞ := by
  apply ne_top_of_le_ne_top (tsum_centralReplacementTailMajorant_ne_top hC)
  exact ENNReal.tsum_le_tsum fun m ↦
    centralReplacementTailCost_le_majorant hC (initialBudget48 m)

/-- A named positive rate after absorbing the fixed exact-count tail
prefactor. -/
def centralTailRate (C : ℝ) : ℝ := fixedReplacementRate C / 2

lemma centralTailRate_pos {C : ℝ} (hC : 0 ≤ C) :
    0 < centralTailRate C := by
  unfold centralTailRate
  positivity [fixedReplacementRate_pos hC]

/-- Eventual pure logarithmic-square bound used when the shell-zero term is
combined with the positive-shell interface costs. -/
theorem eventually_centralReplacementTailCost_le_exp_neg_log_sq
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ m : ℕ in Filter.atTop,
      centralReplacementTailCost C (initialBudget48 m) ≤
        ENNReal.ofReal
          (Real.exp (-centralTailRate C * Real.log (m : ℝ) ^ 2)) := by
  let A := centralTailPrefactor C
  let R := fixedReplacementRate C
  have hA : 0 < A := centralTailPrefactor_pos hC
  have hR : 0 < R := fixedReplacementRate_pos hC.le
  have hlog : Filter.Tendsto
      (fun m : ℕ ↦ Real.log (m : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ m : ℕ in Filter.atTop,
      max 1 (2 * Real.log A / R) ≤ Real.log (m : ℝ) :=
    hlog.eventually (Filter.eventually_ge_atTop _)
  filter_upwards [hlarge] with m hm
  have hlogA : Real.log A ≤
      R / 2 * Real.log (m : ℝ) ^ 2 := by
    have hone : 1 ≤ Real.log (m : ℝ) := (le_max_left _ _).trans hm
    have hthreshold : 2 * Real.log A / R ≤ Real.log (m : ℝ) :=
      (le_max_right _ _).trans hm
    have hsq : Real.log (m : ℝ) ≤ Real.log (m : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (m : ℝ) - 1)]
    have hmul : 2 * Real.log A ≤ R * Real.log (m : ℝ) := by
      rw [div_le_iff₀ hR] at hthreshold
      simpa only [mul_comm] using hthreshold
    nlinarith
  have hAexp : A ≤
      Real.exp (R / 2 * Real.log (m : ℝ) ^ 2) := by
    rw [show A = Real.exp (Real.log A) by rw [Real.exp_log hA]]
    exact Real.exp_le_exp.mpr hlogA
  have hreal : A * fixedReplacementRealCost C m ≤
      Real.exp (-centralTailRate C * Real.log (m : ℝ) ^ 2) := by
    calc
      A * fixedReplacementRealCost C m ≤
          A * Real.exp (-R * Real.log (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (fixedReplacementRealCost_le_exp_neg_log_sq hC.le m) hA.le
      _ ≤ Real.exp (R / 2 * Real.log (m : ℝ) ^ 2) *
          Real.exp (-R * Real.log (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hAexp (Real.exp_pos _).le
      _ = Real.exp (-centralTailRate C * Real.log (m : ℝ) ^ 2) := by
        rw [← Real.exp_add]
        unfold centralTailRate
        congr 1
        ring
  calc
    centralReplacementTailCost C (initialBudget48 m) ≤
        centralReplacementTailMajorant C (initialBudget48 m) :=
      centralReplacementTailCost_le_majorant hC _
    _ = ENNReal.ofReal (A * fixedReplacementRealCost C m) := by
      rw [centralReplacementTailMajorant_initialBudget_eq_prefactor_mul hC]
      unfold A fixedReplacementCost fixedReplacementRealCost
      rw [ENNReal.ofReal_mul hA.le]
    _ ≤ ENNReal.ofReal
        (Real.exp (-centralTailRate C * Real.log (m : ℝ) ^ 2)) :=
      ENNReal.ofReal_mono hreal

end

end Erdos1165.HLOZShellZeroCentralTail
