/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.LowerAssemblyNumeric
import ErdosProblems.Erdos360.ControlledCapTwelve

/-!
# Canonical controlled parameters for the prime/random lower bound

This file fixes the parameters used by the controlled extraction route.  In
particular the random iteration length is no longer existential.  The cutoff
`controlledPrimeU` is a rounded constant multiple of `n^(1/8)`, the sieve
cutoff is exactly `y / U`, and the extraction diversity consists of a large
constant multiple of the fourth root of `y` together with the full cell
reserve.  The cardinal scales are the sound `V y / 12` scales from
`ControlledCapTwelve`: `5n/(4y)` before extraction and `6n/(5y)` after it.

The elementary lemmas below are deliberately stated before any asymptotic
assembly.  They record the exact rounding margins required by the final
ledger: positivity of `U` and `B`, the gap between the controlled class cap
and extracted floor, and the uniform `2*U` bound for the divisor-dependent
endpoint quotient.
-/

namespace Erdos360

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Fixed number of random pools in the controlled construction.  The large
absolute constant leaves the ambient sparsity margin required by the sharp
CFP inverse theorem; its size has no effect on the asymptotic order. -/
def controlledPrimeEll : ℕ := 1099511627776

/-- Total number of exact-split cells; only one eighth of them are used. -/
def controlledPrimeCells : ℕ := 8 * controlledPrimeEll

/-- Divisor-fibre cutoff, rounded upward from `1000*n^(1/8)`. -/
noncomputable def controlledPrimeU (n : ℕ) : ℕ :=
  ⌈1000 * Real.rpow (n : ℝ) (1 / 8 : ℝ)⌉₊

/-- The prime cutoff is the largest integral quotient allowed by `y / U`. -/
noncomputable def controlledPrimeB (n y : ℕ) : ℕ :=
  y / controlledPrimeU n

/-- Diversity before the cell reserve is removed.  The generous constant
also pays the four exact-split probability estimates. -/
noncomputable def controlledPrimeL (y : ℕ) : ℕ :=
  1000000 * fourthRootCeil y + (controlledPrimeCells - 1)

@[simp] lemma controlledPrimeEll_eq : controlledPrimeEll = 1099511627776 := rfl

@[simp] lemma controlledPrimeCells_eq : controlledPrimeCells = 8796093022208 := by
  norm_num [controlledPrimeCells, controlledPrimeEll]

lemma controlledPrimeU_pos {n : ℕ} (hn : 0 < n) :
    0 < controlledPrimeU n := by
  rw [controlledPrimeU, Nat.ceil_pos]
  exact mul_pos (by norm_num)
    (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)

lemma controlledPrimeU_cast_bounds (n : ℕ) :
    1000 * Real.rpow (n : ℝ) (1 / 8 : ℝ) ≤
        (controlledPrimeU n : ℝ) ∧
      (controlledPrimeU n : ℝ) <
        1000 * Real.rpow (n : ℝ) (1 / 8 : ℝ) + 1 := by
  constructor
  · simpa [controlledPrimeU] using
      Nat.le_ceil (1000 * Real.rpow (n : ℝ) (1 / 8 : ℝ))
  · simpa [controlledPrimeU] using Nat.ceil_lt_add_one
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))

@[simp] lemma controlledPrimeB_eq (n y : ℕ) :
    controlledPrimeB n y = y / controlledPrimeU n := rfl

lemma controlledPrimeB_pos {n y : ℕ}
    (hU : controlledPrimeU n ≤ y) (hn : 0 < n) :
    0 < controlledPrimeB n y := by
  exact Nat.div_pos hU (controlledPrimeU_pos hn)

lemma controlledPrimeB_le_cutoff (n y : ℕ) :
    controlledPrimeB n y ≤ y / controlledPrimeU n := by
  rfl

lemma controlledPrimeL_reserve (y : ℕ) :
    controlledPrimeCells - 1 ≤ controlledPrimeL y := by
  unfold controlledPrimeL
  omega

lemma controlledPrimeL_sub_reserve (y : ℕ) :
    controlledPrimeL y - (controlledPrimeCells - 1) =
      1000000 * fourthRootCeil y := by
  unfold controlledPrimeL
  omega

lemma controlledPrimeL_pos (y : ℕ) : 0 < controlledPrimeL y := by
  simp [controlledPrimeL, controlledPrimeCells, controlledPrimeEll]

/-! ## Exact integral rounding margins -/

lemma controlledPrime_loss_room
    {n y : ℕ} (hy : 0 < y)
    (hroom : 20 * y *
      (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) ≤ n) :
    controlledPrimeExtractedFloorTwelve n y +
        controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) ≤
      controlledPrimeClassCapTwelve n y :=
  controlledPrimeTwelve_loss_room hy hroom

/-- It is enough to fit `U+1` into the post-extraction density in order to
absorb the last division rounding. -/
lemma controlledPrimeU_le_extractedFloor
    {n y : ℕ} (hy : 0 < y)
    (hfit : 5 * y * (controlledPrimeU n + 1) ≤ 6 * n) :
    controlledPrimeU n ≤ controlledPrimeExtractedFloorTwelve n y := by
  unfold controlledPrimeExtractedFloorTwelve
  rw [Nat.le_div_iff_mul_le (by omega)]
  calc
    controlledPrimeU n * (5 * y) ≤
        (controlledPrimeU n + 1) * (5 * y) :=
      Nat.mul_le_mul_right (5 * y) (Nat.le_succ _)
    _ = 5 * y * (controlledPrimeU n + 1) := by ring
    _ ≤ 6 * n := hfit

/-- If extraction returns `d ≤ U`, then every endpoint estimate may use the
uniform post-extraction floor instead of `d`. -/
lemma extracted_scale_le_controlledFloor
    {n y d : ℕ} (hy : 0 < y) (hdU : d ≤ controlledPrimeU n)
    (hfit : 5 * y * (controlledPrimeU n + 1) ≤ 6 * n) :
    d ≤ controlledPrimeExtractedFloorTwelve n y :=
  hdU.trans (controlledPrimeU_le_extractedFloor hy hfit)

lemma controlledPrimeB_le_divisor_quotient
    {n y d : ℕ} (hd : 0 < d) (hdU : d ≤ controlledPrimeU n) :
    controlledPrimeB n y ≤ y / d := by
  unfold controlledPrimeB
  exact Nat.div_le_div_left hdU hd

/-- The apparently divisor-dependent term in the diversity ledger is in
fact at most `2*U`.  The proof retains all floor errors: both quotient
remainders are paid by the two displayed `+1`s. -/
lemma controlled_endpoint_quotient_le_two_mul_U
    {n y d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    (2 * y / d) / (controlledPrimeB n y / d + 1) ≤
      2 * controlledPrimeU n := by
  let U := controlledPrimeU n
  let B := controlledPrimeB n y
  let D := B / d + 1
  have hU : 0 < U := by simpa [U] using controlledPrimeU_pos hn
  have hB : B = y / U := by simp [B, U]
  have hyUB : y < U * (B + 1) := by
    rw [hB]
    simpa [mul_comm] using
      (Nat.lt_mul_of_div_lt (Nat.lt_succ_self (y / U)) hU)
  have hBd : B < d * D := by
    dsimp [D]
    simpa [mul_comm] using
      (Nat.lt_mul_of_div_lt (Nat.lt_succ_self (B / d)) hd)
  have hyUD : y ≤ U * (d * D) := by
    calc
      y ≤ U * (B + 1) := hyUB.le
      _ ≤ U * (d * D) := Nat.mul_le_mul_left U (by omega)
  have htwo : 2 * y / d ≤ (2 * U) * D := by
    apply Nat.div_le_of_le_mul
    calc
      2 * y ≤ 2 * (U * (d * D)) := Nat.mul_le_mul_left 2 hyUD
      _ = d * ((2 * U) * D) := by ring
  have hD : 0 < D := by simp [D]
  change (2 * y / d) / D ≤ 2 * U
  exact Nat.div_le_of_le_mul (by simpa [mul_comm] using htwo)

/-- The terminal unused-mass inequality for the fixed controlled floor. -/
lemma controlledPrime_unused_of_linear_room
    {n y : ℕ} (hy : 0 < y) (hlinear : 140 * y ≤ n) :
    n ≤ 7 * y * (controlledPrimeExtractedFloorTwelve n y / 8) :=
  controlledPrimeTwelve_unused_reserve hy hlinear

lemma natLogTwo_cast_le_two_mul_log {m : ℕ} (hm : 0 < m) :
    (Nat.log 2 m : ℝ) ≤ 2 * Real.log (m : ℝ) := by
  have hpow : 2 ^ Nat.log 2 m ≤ m :=
    Nat.pow_log_le_self 2 hm.ne'
  have hpowR : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    hpowR
  rw [Real.log_pow] at hlog
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hk : (0 : ℝ) ≤ Nat.log 2 m := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlogTwo hk]

lemma fourthRootCeil_cast_lt_two_mul_rpow {y : ℕ} (hy : 0 < y) :
    (fourthRootCeil y : ℝ) <
      2 * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hpOne : 1 ≤ Real.rpow (y : ℝ) (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hy) (by norm_num)
  have hceil : (fourthRootCeil y : ℝ) <
      Real.rpow (y : ℝ) (1 / 4 : ℝ) + 1 := by
    simpa [fourthRootCeil] using Nat.ceil_lt_add_one
      (Real.rpow_nonneg hyR.le (1 / 4 : ℝ))
  nlinarith

/-! ## Canonical eventual analytic input -/

/-- Public version of the upper half of the scale/totient identity used in
`LowerAssemblyNumeric`.  It is useful here because it gives a substantially
sharper upper bound for the canonical `y` than merely `y < n/2`. -/
lemma resolutionScale_mul_totient_le_rpow_four_thirds
    {n : ℕ} (hn : 0 < n)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hloglog : 1 ≤ Real.log (Real.log (n : ℝ))) :
    resolutionScale n * (Nat.totient n : ℝ) ≤
      Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  let D : ℝ := Real.rpow (Real.log (n : ℝ)) (1 / 3 : ℝ) *
    Real.rpow (Real.log (Real.log (n : ℝ))) (2 / 3 : ℝ)
  have hDone : 1 ≤ D := by
    dsimp [D]
    have h₁ := Real.one_le_rpow hlog (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have h₂ := Real.one_le_rpow hloglog (by norm_num : (0 : ℝ) ≤ 2 / 3)
    nlinarith
  have hDpos : 0 < D := zero_lt_one.trans_le hDone
  have heq : resolutionScale n * (Nat.totient n : ℝ) =
      Real.rpow (n : ℝ) (4 / 3 : ℝ) / D := by
    have hpow : Real.rpow (n : ℝ) (4 / 3 : ℝ) =
        Real.rpow (n : ℝ) (1 / 3 : ℝ) * (n : ℝ) := by
      calc
        Real.rpow (n : ℝ) (4 / 3 : ℝ) =
            Real.rpow (n : ℝ) ((1 / 3 : ℝ) + 1) := by norm_num
        _ = Real.rpow (n : ℝ) (1 / 3 : ℝ) *
            Real.rpow (n : ℝ) 1 := Real.rpow_add hnR _ _
        _ = Real.rpow (n : ℝ) (1 / 3 : ℝ) * (n : ℝ) := by
          congr 1
          exact Real.rpow_one (n : ℝ)
    rw [resolutionScale, hpow]
    dsimp [D]
    field_simp [hphi.ne']
  rw [heq]
  exact (div_le_iff₀ hDpos).2 <| by
    have hp : 0 ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
      Real.rpow_nonneg hnR.le _
    nlinarith [mul_le_mul_of_nonneg_left hDone hp]

/-- The canonical window is eventually below `n^(7/10)`.  The exponent is
chosen with room on both sides: the exact upper bound is
`O(n^(2/3) sqrt(log n))`, while `7/10 < 7/8` is already enough for all
`n^(1/8)` endpoint comparisons. -/
lemma eventually_initialLowerY_lt_rpow_seven_tenths :
    ∀ᶠ n : ℕ in atTop,
      (initialLowerY n (lowerColorCount 1 n) : ℝ) <
        Real.rpow (n : ℝ) (7 / 10 : ℝ) := by
  have hpowTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 30 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_three_le_lowerColorCount (c := (1 : ℝ)) (by norm_num),
    eventually_initialMissingMertensBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    hpowTop.eventually (eventually_ge_atTop (4000 : ℝ))] with
      n hn hlog hloglog hcolors hMertens hlarge
  let r := lowerColorCount 1 n
  let y := initialLowerY n r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; omega
  have hscalePos : 0 < resolutionScale n := by
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hnR _)
        (div_pos hnR (by exact_mod_cast Nat.totient_pos.mpr hn)))
      (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _)
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hloglog) _))
  have hrScale : (r : ℝ) ≤ resolutionScale n := by
    simpa [r] using
      (lowerColorCount_bounds (c := (1 : ℝ)) (n := n)
        (by norm_num) hscalePos.le).1
  have hphiOne : (1 : ℝ) ≤ Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hrPow : (r : ℝ) ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
    calc
      (r : ℝ) ≤ resolutionScale n := hrScale
      _ ≤ resolutionScale n * Nat.totient n := by
        nlinarith [mul_le_mul_of_nonneg_left hphiOne hscalePos.le]
      _ ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
        resolutionScale_mul_totient_le_rpow_four_thirds hn hlog hloglog
  have hlogr : Real.log (r : ℝ) ≤
      (4 / 3 : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log (r : ℝ) ≤
          Real.log (Real.rpow (n : ℝ) (4 / 3 : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hr) hrPow
      _ = (4 / 3 : ℝ) * Real.log (n : ℝ) :=
        Real.log_rpow hnR _
  have hlogPower : Real.log (n : ℝ) ≤
      30 * Real.rpow (n : ℝ) (1 / 30 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hnR.le
      (show (0 : ℝ) < 1 / 30 by norm_num)
  have hrphi : (r : ℝ) * Nat.totient n ≤
      Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
    calc
      (r : ℝ) * Nat.totient n ≤
          resolutionScale n * Nat.totient n :=
        mul_le_mul_of_nonneg_right hrScale (by positivity)
      _ ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
        resolutionScale_mul_totient_le_rpow_four_thirds hn hlog hloglog
  have hyWindow := initialLowerY_coarse_bounds hn hr hMertens
  have hySq : (y : ℝ) ^ 2 <
      4000 * (Real.rpow (n : ℝ) (4 / 3 : ℝ) *
        Real.rpow (n : ℝ) (1 / 30 : ℝ)) := by
    calc
      (y : ℝ) ^ 2 < 100 * r * Nat.totient n * Real.log (r : ℝ) :=
        by simpa [y, r] using hyWindow.2
      _ ≤ 100 * Real.rpow (n : ℝ) (4 / 3 : ℝ) *
          ((4 / 3 : ℝ) * Real.log (n : ℝ)) := by
        have hrlog0 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ r by omega))
        have hright0 : 0 ≤ 100 * Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _)
        have hleft : 100 * (r : ℝ) * Nat.totient n ≤
            100 * Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left hrphi (by norm_num : (0 : ℝ) ≤ 100))
        exact mul_le_mul
          hleft hlogr hrlog0 hright0
      _ ≤ 4000 * (Real.rpow (n : ℝ) (4 / 3 : ℝ) *
          Real.rpow (n : ℝ) (1 / 30 : ℝ)) := by
        have hp := Real.rpow_nonneg hnR.le (4 / 3 : ℝ)
        nlinarith [mul_le_mul_of_nonneg_left hlogPower hp]
  have hsplit : Real.rpow (n : ℝ) (7 / 5 : ℝ) =
      Real.rpow (n : ℝ) (4 / 3 : ℝ) *
        (Real.rpow (n : ℝ) (1 / 30 : ℝ) *
          Real.rpow (n : ℝ) (1 / 30 : ℝ)) := by
    calc
      Real.rpow (n : ℝ) (7 / 5 : ℝ) =
          Real.rpow (n : ℝ) (4 / 3 : ℝ) *
            Real.rpow (n : ℝ) (1 / 15 : ℝ) := by
        convert Real.rpow_add hnR (4 / 3 : ℝ) (1 / 15 : ℝ) using 1 <;>
          norm_num
      _ = Real.rpow (n : ℝ) (4 / 3 : ℝ) *
          (Real.rpow (n : ℝ) (1 / 30 : ℝ) *
            Real.rpow (n : ℝ) (1 / 30 : ℝ)) := by
        congr 1
        convert Real.rpow_add hnR (1 / 30 : ℝ) (1 / 30 : ℝ) using 1 <;>
          norm_num
  have hySq' : (y : ℝ) ^ 2 < Real.rpow (n : ℝ) (7 / 5 : ℝ) := by
    rw [hsplit]
    have hp0 := Real.rpow_pos_of_pos hnR (4 / 3 : ℝ)
    have hp1 := Real.rpow_pos_of_pos hnR (1 / 30 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hlarge
      (mul_nonneg hp0.le hp1.le)]
  have hsquare : (Real.rpow (n : ℝ) (7 / 10 : ℝ)) ^ 2 =
      Real.rpow (n : ℝ) (7 / 5 : ℝ) := by
    calc
      (Real.rpow (n : ℝ) (7 / 10 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (n : ℝ) (7 / 10 : ℝ)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (n : ℝ) ((7 / 10 : ℝ) * 2) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (7 / 5 : ℝ) := by norm_num
  rw [← hsquare] at hySq'
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hp0 : 0 ≤ Real.rpow (n : ℝ) (7 / 10 : ℝ) :=
    Real.rpow_nonneg hnR.le _
  nlinarith

/-- A near-optimal polynomial upper bound for the canonical initial window.
The exponent `267/400 = 2/3 + 1/1200` leaves a positive power margin in the
degree-100 inverse-theorem inequality. -/
lemma eventually_initialLowerY_lt_rpow_267_400 :
    ∀ᶠ n : ℕ in atTop,
      (initialLowerY n (lowerColorCount 1 n) : ℝ) <
        Real.rpow (n : ℝ) (267 / 400 : ℝ) := by
  have hpowTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 1200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_three_le_lowerColorCount (c := (1 : ℝ)) (by norm_num),
    eventually_initialMissingMertensBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    hpowTop.eventually (eventually_ge_atTop (160000 : ℝ))] with
      n hn hlog hloglog hcolors hMertens hlarge
  let r := lowerColorCount 1 n
  let y := initialLowerY n r
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := by dsimp [r]; omega
  have hscalePos : 0 < resolutionScale n := by
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hnR _)
        (div_pos hnR (by exact_mod_cast Nat.totient_pos.mpr hn)))
      (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hlog) _)
        (Real.rpow_pos_of_pos (zero_lt_one.trans_le hloglog) _))
  have hrScale : (r : ℝ) ≤ resolutionScale n := by
    simpa [r] using
      (lowerColorCount_bounds (c := (1 : ℝ)) (n := n)
        (by norm_num) hscalePos.le).1
  have hphiOne : (1 : ℝ) ≤ Nat.totient n := by
    exact_mod_cast Nat.totient_pos.mpr hn
  have hrPow : (r : ℝ) ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
    calc
      (r : ℝ) ≤ resolutionScale n := hrScale
      _ ≤ resolutionScale n * Nat.totient n := by
        nlinarith [mul_le_mul_of_nonneg_left hphiOne hscalePos.le]
      _ ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
        resolutionScale_mul_totient_le_rpow_four_thirds hn hlog hloglog
  have hlogr : Real.log (r : ℝ) ≤
      (4 / 3 : ℝ) * Real.log (n : ℝ) := by
    calc
      Real.log (r : ℝ) ≤
          Real.log (Real.rpow (n : ℝ) (4 / 3 : ℝ)) :=
        Real.log_le_log (by exact_mod_cast hr) hrPow
      _ = (4 / 3 : ℝ) * Real.log (n : ℝ) :=
        Real.log_rpow hnR _
  have hlogPower : Real.log (n : ℝ) ≤
      1200 * Real.rpow (n : ℝ) (1 / 1200 : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hnR.le
      (show (0 : ℝ) < 1 / 1200 by norm_num)
  have hrphi : (r : ℝ) * Nat.totient n ≤
      Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
    calc
      (r : ℝ) * Nat.totient n ≤
          resolutionScale n * Nat.totient n :=
        mul_le_mul_of_nonneg_right hrScale (by positivity)
      _ ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
        resolutionScale_mul_totient_le_rpow_four_thirds hn hlog hloglog
  have hyWindow := initialLowerY_coarse_bounds hn hr hMertens
  have hySq : (y : ℝ) ^ 2 <
      160000 * (Real.rpow (n : ℝ) (4 / 3 : ℝ) *
        Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by
    calc
      (y : ℝ) ^ 2 < 100 * r * Nat.totient n * Real.log (r : ℝ) :=
        by simpa [y, r] using hyWindow.2
      _ ≤ 100 * Real.rpow (n : ℝ) (4 / 3 : ℝ) *
          ((4 / 3 : ℝ) * Real.log (n : ℝ)) := by
        have hrlog0 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by
          exact_mod_cast (show 1 ≤ r by omega))
        have hright0 : 0 ≤ 100 * Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
          mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _)
        have hleft : 100 * (r : ℝ) * Nat.totient n ≤
            100 * Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left hrphi (by norm_num : (0 : ℝ) ≤ 100))
        exact mul_le_mul hleft hlogr hrlog0 hright0
      _ ≤ 160000 * (Real.rpow (n : ℝ) (4 / 3 : ℝ) *
          Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by
        have hp := Real.rpow_nonneg hnR.le (4 / 3 : ℝ)
        nlinarith [mul_le_mul_of_nonneg_left hlogPower hp]
  have hsplit : Real.rpow (n : ℝ) (267 / 200 : ℝ) =
      Real.rpow (n : ℝ) (4 / 3 : ℝ) *
        (Real.rpow (n : ℝ) (1 / 1200 : ℝ) *
          Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by
    calc
      Real.rpow (n : ℝ) (267 / 200 : ℝ) =
          Real.rpow (n : ℝ) (4 / 3 : ℝ) *
            Real.rpow (n : ℝ) (1 / 600 : ℝ) := by
        convert Real.rpow_add hnR (4 / 3 : ℝ) (1 / 600 : ℝ) using 1 <;>
          norm_num
      _ = Real.rpow (n : ℝ) (4 / 3 : ℝ) *
          (Real.rpow (n : ℝ) (1 / 1200 : ℝ) *
            Real.rpow (n : ℝ) (1 / 1200 : ℝ)) := by
        congr 1
        convert Real.rpow_add hnR (1 / 1200 : ℝ) (1 / 1200 : ℝ) using 1 <;>
          norm_num
  have hySq' : (y : ℝ) ^ 2 <
      Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
    rw [hsplit]
    have hp0 := Real.rpow_pos_of_pos hnR (4 / 3 : ℝ)
    have hp1 := Real.rpow_pos_of_pos hnR (1 / 1200 : ℝ)
    nlinarith [mul_le_mul_of_nonneg_left hlarge
      (mul_nonneg hp0.le hp1.le)]
  have hsquare : (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 =
      Real.rpow (n : ℝ) (267 / 200 : ℝ) := by
    calc
      (Real.rpow (n : ℝ) (267 / 400 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (n : ℝ) (267 / 400 : ℝ)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (n : ℝ) ((267 / 400 : ℝ) * 2) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (267 / 200 : ℝ) := by norm_num
  rw [← hsquare] at hySq'
  have hy0 : (0 : ℝ) ≤ y := by positivity
  have hp0 : 0 ≤ Real.rpow (n : ℝ) (267 / 400 : ℝ) :=
    Real.rpow_nonneg hnR.le _
  nlinarith

/-- The canonical lower window `y ≥ n^(3/5)`, together with the preceding
upper bound, makes `U` both nonzero and negligible compared with `y` and
with `n/y`.  This is the exact endpoint bundle used after extraction. -/
lemma eventually_controlledPrime_endpoint_parameters :
    ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount 1 n
      let y := initialLowerY n colors
      0 < controlledPrimeU n ∧
      controlledPrimeU n ≤ y ∧
      0 < controlledPrimeB n y ∧
      controlledPrimeB n y ≤ y / controlledPrimeU n ∧
      5 * y * (controlledPrimeU n + 1) ≤ 6 * n ∧
      controlledPrimeU n ≤ controlledPrimeExtractedFloorTwelve n y ∧
      140 * y ≤ n := by
  have hp8Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hp192Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (19 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpQuarterTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    eventually_initialLowerY_lt_rpow_seven_tenths,
    eventually_initialMissingMertensBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    eventually_CFPDiagonalNumericBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    eventually_three_le_lowerColorCount (c := (1 : ℝ)) (by norm_num),
    hp8Top.eventually (eventually_ge_atTop (1002 : ℝ)),
    hp192Top.eventually (eventually_ge_atTop (1002 : ℝ)),
    hpQuarterTop.eventually (eventually_ge_atTop (140 : ℝ))] with
      n hn hyUpper hMertens hnum hcolors hp8 hp192 hpQuarter
  let colors := lowerColorCount 1 n
  let y := initialLowerY n colors
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcolor : 0 < colors := by dsimp [colors]; omega
  have hyLower := (initialLowerY_range_of_numeric_bounds hn hcolor
    hMertens hnum.1 hnum.2.1 hnum.2.2).2.1
  have hUpos := controlledPrimeU_pos hn
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8pos := Real.rpow_pos_of_pos hnR (1 / 8 : ℝ)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    nlinarith
  have hthreeFifths : Real.rpow (n : ℝ) (3 / 5 : ℝ) =
      Real.rpow (n : ℝ) (1 / 8 : ℝ) *
        Real.rpow (n : ℝ) (19 / 40 : ℝ) := by
    convert Real.rpow_add hnR (1 / 8 : ℝ) (19 / 40 : ℝ) using 1 <;>
      norm_num
  have hUyR : (controlledPrimeU n : ℝ) < (y : ℝ) := by
    calc
      (controlledPrimeU n : ℝ) <
          1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := hUrough
      _ ≤ Real.rpow (n : ℝ) (3 / 5 : ℝ) := by
        rw [hthreeFifths]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hp192 hp8pos.le
      _ ≤ (y : ℝ) := by simpa [y, colors] using hyLower
  have hUy : controlledPrimeU n ≤ y := by exact_mod_cast hUyR.le
  have hy : 0 < y := hUpos.trans_le hUy
  have hBpos := controlledPrimeB_pos hUy hn
  have hsevenEighths : Real.rpow (n : ℝ) (7 / 8 : ℝ) =
      Real.rpow (n : ℝ) (7 / 10 : ℝ) *
        Real.rpow (n : ℝ) (7 / 40 : ℝ) := by
    convert Real.rpow_add hnR (7 / 10 : ℝ) (7 / 40 : ℝ) using 1 <;>
      norm_num
  have hpSevenForty : (835 : ℝ) ≤
      Real.rpow (n : ℝ) (7 / 40 : ℝ) := by
    have hpowMono := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ n by exact_mod_cast hn) (by norm_num :
        (1 / 8 : ℝ) ≤ 7 / 40)
    exact (by norm_num : (835 : ℝ) ≤ 1002).trans (hp8.trans hpowMono)
  have hUone : ((controlledPrimeU n + 1 : ℕ) : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    push_cast
    nlinarith
  have hfitR : (5 : ℝ) * y * (controlledPrimeU n + 1) < 6 * n := by
    have hyU : (y : ℝ) * ((controlledPrimeU n + 1 : ℕ) : ℝ) <
        Real.rpow (n : ℝ) (7 / 10 : ℝ) *
          (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) := by
      calc
        (y : ℝ) * ((controlledPrimeU n + 1 : ℕ) : ℝ) <
            Real.rpow (n : ℝ) (7 / 10 : ℝ) *
              ((controlledPrimeU n + 1 : ℕ) : ℝ) :=
          mul_lt_mul_of_pos_right hyUpper (by positivity)
        _ < Real.rpow (n : ℝ) (7 / 10 : ℝ) *
            (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) :=
          mul_lt_mul_of_pos_left hUone (Real.rpow_pos_of_pos hnR _)
    have hnSplit : (n : ℝ) =
        Real.rpow (n : ℝ) (7 / 8 : ℝ) *
          Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
      calc
        (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
        _ = Real.rpow (n : ℝ) ((7 / 8 : ℝ) + (1 / 8 : ℝ)) := by norm_num
        _ = Real.rpow (n : ℝ) (7 / 8 : ℝ) *
            Real.rpow (n : ℝ) (1 / 8 : ℝ) := Real.rpow_add hnR _ _
    rw [hnSplit, hsevenEighths]
    have hp7 := Real.rpow_pos_of_pos hnR (7 / 10 : ℝ)
    have hcoeff : (5010 : ℝ) * Real.rpow (n : ℝ) (7 / 10 : ℝ) ≤
        6 * (Real.rpow (n : ℝ) (7 / 10 : ℝ) *
          Real.rpow (n : ℝ) (7 / 40 : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hpSevenForty hp7.le]
    nlinarith [mul_le_mul_of_nonneg_right hcoeff hp8pos.le]
  have hfit : 5 * y * (controlledPrimeU n + 1) ≤ 6 * n := by
    exact_mod_cast hfitR.le
  have hlinearR : (140 : ℝ) * y < n := by
    have hnSplit : (n : ℝ) =
        Real.rpow (n : ℝ) (7 / 10 : ℝ) *
          Real.rpow (n : ℝ) (3 / 10 : ℝ) := by
      calc
        (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
        _ = Real.rpow (n : ℝ) ((7 / 10 : ℝ) + (3 / 10 : ℝ)) := by norm_num
        _ = Real.rpow (n : ℝ) (7 / 10 : ℝ) *
            Real.rpow (n : ℝ) (3 / 10 : ℝ) := Real.rpow_add hnR _ _
    have hpThreeTenths : (140 : ℝ) ≤
        Real.rpow (n : ℝ) (3 / 10 : ℝ) := by
      exact hpQuarter.trans (Real.rpow_le_rpow_of_exponent_le
        (show (1 : ℝ) ≤ n by exact_mod_cast hn)
        (by norm_num : (1 / 4 : ℝ) ≤ 3 / 10))
    rw [hnSplit]
    exact (mul_lt_mul_of_pos_left hyUpper (by norm_num)).trans_le
      (by simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hpThreeTenths
          (Real.rpow_nonneg hnR.le (7 / 10 : ℝ))))
  have hlinear : 140 * y ≤ n := by exact_mod_cast hlinearR.le
  exact ⟨hUpos, hUy, hBpos, controlledPrimeB_le_cutoff n y,
    hfit, controlledPrimeU_le_extractedFloor hy hfit, hlinear⟩

/-- The fixed fourth-root diversity and the binary-log extraction loss fit
inside the exact `1/20` gap between the two sound controlled cardinal scales. -/
lemma eventually_controlledPrime_loss_room :
    ∀ᶠ n : ℕ in atTop,
      let colors := lowerColorCount 1 n
      let y := initialLowerY n colors
      20 * y *
        (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) ≤ n := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (13 / 160 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  let CL : ℕ := controlledPrimeCells + 2000000
  let CC : ℕ := 33 * CL
  filter_upwards [eventually_controlledPrime_endpoint_parameters,
    eventually_initialLowerY_lt_rpow_seven_tenths,
    hpTop.eventually (eventually_ge_atTop ((20 * CC : ℕ) : ℝ))] with
      n hend hyUpper hpLarge
  dsimp only at hend ⊢
  let colors := lowerColorCount 1 n
  let y := initialLowerY n colors
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    have hCCpos : 0 < CC := by
      dsimp [CC, CL]
      positivity
    have hpos : (0 : ℝ) < (20 * CC : ℕ) := by exact_mod_cast
      (Nat.mul_pos (by norm_num) hCCpos)
    norm_num at hpLarge
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hUpos : 0 < controlledPrimeU n := hend.1
  have hUy : controlledPrimeU n ≤ y := hend.2.1
  have hy : 0 < y := hUpos.trans_le hUy
  have hBpos : 0 < controlledPrimeB n y := hend.2.2.1
  have hBy : controlledPrimeB n y ≤ y := by
    unfold controlledPrimeB
    exact Nat.div_le_self y (controlledPrimeU n)
  have hlogB : (Nat.log 2 (controlledPrimeB n y) : ℝ) ≤
      32 * Real.rpow (y : ℝ) (1 / 16 : ℝ) := by
    have hlogMono : Real.log (controlledPrimeB n y : ℝ) ≤
        Real.log (y : ℝ) := by
      exact Real.log_le_log (by exact_mod_cast hBpos) (by exact_mod_cast hBy)
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    have hlogPower : Real.log (y : ℝ) ≤
        16 * Real.rpow (y : ℝ) (1 / 16 : ℝ) := by
      simpa [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hyR.le
        (show (0 : ℝ) < 1 / 16 by norm_num)
    nlinarith [natLogTwo_cast_le_two_mul_log hBpos]
  have hyQuarterOne : 1 ≤ Real.rpow (y : ℝ) (1 / 4 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hy) (by norm_num)
  have hL : (controlledPrimeL y : ℝ) ≤
      CL * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
    have hroot := fourthRootCeil_cast_lt_two_mul_rpow hy
    have hcells : ((controlledPrimeCells - 1 : ℕ) : ℝ) ≤
        controlledPrimeCells * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
      have hcast : ((controlledPrimeCells - 1 : ℕ) : ℝ) ≤
          (controlledPrimeCells : ℝ) := by exact_mod_cast Nat.sub_le _ _
      exact hcast.trans (by
        simpa using mul_le_mul_of_nonneg_left hyQuarterOne
          (by positivity : (0 : ℝ) ≤ controlledPrimeCells))
    calc
      (controlledPrimeL y : ℝ) =
          1000000 * (fourthRootCeil y : ℝ) +
            (controlledPrimeCells - 1 : ℕ) := by
        rw [controlledPrimeL]
        push_cast
        rfl
      _ ≤ 2000000 * Real.rpow (y : ℝ) (1 / 4 : ℝ) +
          controlledPrimeCells * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
        exact add_le_add (by nlinarith) hcells
      _ = CL * Real.rpow (y : ℝ) (1 / 4 : ℝ) := by
        dsimp [CL]
        push_cast
        ring
  have hpowFiveSixteenths :
      Real.rpow (y : ℝ) (5 / 16 : ℝ) =
        Real.rpow (y : ℝ) (1 / 4 : ℝ) *
          Real.rpow (y : ℝ) (1 / 16 : ℝ) := by
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    convert Real.rpow_add hyR (1 / 4 : ℝ) (1 / 16 : ℝ) using 1 <;>
      norm_num
  have hpFiveOne : 1 ≤ Real.rpow (y : ℝ) (5 / 16 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hy) (by norm_num)
  have hloss :
      ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) + 1 : ℕ) : ℝ) ≤
        CC * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
    push_cast
    have hmul := mul_le_mul hL hlogB
      (by positivity : (0 : ℝ) ≤ (Nat.log 2 (controlledPrimeB n y) : ℝ))
      (by positivity : (0 : ℝ) ≤
        CL * Real.rpow (y : ℝ) (1 / 4 : ℝ))
    have hCLone : (1 : ℝ) ≤ CL := by
      exact_mod_cast (show 1 ≤ CL by dsimp [CL]; omega)
    have hprodOne : (1 : ℝ) ≤ CL *
        (Real.rpow (y : ℝ) (1 / 4 : ℝ) *
          Real.rpow (y : ℝ) (1 / 16 : ℝ)) := by
      rw [← hpowFiveSixteenths]
      simpa using mul_le_mul hCLone hpFiveOne
        (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ CL)
    calc
      (controlledPrimeL y : ℝ) * Nat.log 2 (controlledPrimeB n y) + 1 ≤
          (CL * Real.rpow (y : ℝ) (1 / 4 : ℝ)) *
            (32 * Real.rpow (y : ℝ) (1 / 16 : ℝ)) + 1 :=
        by simpa [add_comm] using add_le_add_right hmul 1
      _ = 32 * (CL * (Real.rpow (y : ℝ) (1 / 4 : ℝ) *
            Real.rpow (y : ℝ) (1 / 16 : ℝ))) + 1 := by ring
      _ ≤ 33 * (CL * (Real.rpow (y : ℝ) (1 / 4 : ℝ) *
            Real.rpow (y : ℝ) (1 / 16 : ℝ))) := by
        linarith
      _ = CC * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
        rw [hpowFiveSixteenths]
        dsimp [CC]
        push_cast
        ring
  have hloss0 :
      ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) : ℕ) : ℝ) ≤
        CC * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
    have hleNat :
        controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) ≤
          controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) + 1 :=
      Nat.le_add_right _ _
    have hleReal :
        ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) : ℕ) : ℝ) ≤
          ((controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hleNat
    exact hleReal.trans hloss
  have hpowY : (y : ℝ) * Real.rpow (y : ℝ) (5 / 16 : ℝ) =
      Real.rpow (y : ℝ) (21 / 16 : ℝ) := by
    have hyR : (0 : ℝ) < y := by exact_mod_cast hy
    calc
      (y : ℝ) * Real.rpow (y : ℝ) (5 / 16 : ℝ) =
          Real.rpow (y : ℝ) 1 * Real.rpow (y : ℝ) (5 / 16 : ℝ) := by
        congr 1
        exact (Real.rpow_one (y : ℝ)).symm
      _ = Real.rpow (y : ℝ) (1 + (5 / 16 : ℝ)) :=
        (Real.rpow_add hyR _ _).symm
      _ = Real.rpow (y : ℝ) (21 / 16 : ℝ) := by norm_num
  have hYPow : Real.rpow (y : ℝ) (21 / 16 : ℝ) ≤
      Real.rpow (n : ℝ) (147 / 160 : ℝ) := by
    have hbase : (y : ℝ) ≤ Real.rpow (n : ℝ) (7 / 10 : ℝ) :=
      hyUpper.le
    calc
      Real.rpow (y : ℝ) (21 / 16 : ℝ) ≤
          Real.rpow (Real.rpow (n : ℝ) (7 / 10 : ℝ))
            (21 / 16 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = Real.rpow (n : ℝ) ((7 / 10 : ℝ) * (21 / 16 : ℝ)) :=
        (Real.rpow_mul hnR.le _ _).symm
      _ = Real.rpow (n : ℝ) (147 / 160 : ℝ) := by norm_num
  have hnSplit : (n : ℝ) =
      Real.rpow (n : ℝ) (147 / 160 : ℝ) *
        Real.rpow (n : ℝ) (13 / 160 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ)
          ((147 / 160 : ℝ) + (13 / 160 : ℝ)) := by norm_num
      _ = Real.rpow (n : ℝ) (147 / 160 : ℝ) *
          Real.rpow (n : ℝ) (13 / 160 : ℝ) := Real.rpow_add hnR _ _
  have hroomR :
      ((20 * y *
        (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) : ℕ) : ℝ) ≤
        (n : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hloss0
    push_cast
    rw [hnSplit]
    calc
      (20 : ℝ) * y *
          (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) ≤
          20 * y * (CC * Real.rpow (y : ℝ) (5 / 16 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hloss0 (by positivity)
      _ = (20 * CC) * Real.rpow (y : ℝ) (21 / 16 : ℝ) := by
        rw [← hpowY]
        ring
      _ ≤ (20 * CC) * Real.rpow (n : ℝ) (147 / 160 : ℝ) :=
        mul_le_mul_of_nonneg_left hYPow (by norm_num)
      _ ≤ Real.rpow (n : ℝ) (147 / 160 : ℝ) *
          Real.rpow (n : ℝ) (13 / 160 : ℝ) := by
        norm_num only [Nat.cast_mul] at hpLarge
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge
          (Real.rpow_nonneg hnR.le (147 / 160 : ℝ))
  exact_mod_cast hroomR

/-- Compact extraction-facing record for the sound `V y / 12` choices above. -/
structure ControlledPrimeTwelveChoiceNumerics (n y : ℕ) : Prop where
  U_pos : 0 < controlledPrimeU n
  U_le_y : controlledPrimeU n ≤ y
  B_pos : 0 < controlledPrimeB n y
  B_cutoff : controlledPrimeB n y ≤ y / controlledPrimeU n
  loss_room : controlledPrimeExtractedFloorTwelve n y +
      controlledPrimeL y * Nat.log 2 (controlledPrimeB n y) ≤
    controlledPrimeClassCapTwelve n y
  U_le_floor : controlledPrimeU n ≤ controlledPrimeExtractedFloorTwelve n y
  unused : n ≤ 7 * y * (controlledPrimeExtractedFloorTwelve n y / 8)
  divisor_endpoint : ∀ d : ℕ, 0 < d → d ≤ controlledPrimeU n →
    d ≤ controlledPrimeExtractedFloorTwelve n y ∧
      (2 * y / d) / (controlledPrimeB n y / d + 1) ≤
        2 * controlledPrimeU n

/-- Every elementary controlled-extraction parameter condition holds
eventually at the canonical diagonal value of `y`. -/
lemma eventually_controlledPrimeTwelve_choice_numerics :
    ∀ᶠ n : ℕ in atTop,
      ControlledPrimeTwelveChoiceNumerics n
        (initialLowerY n (lowerColorCount 1 n)) := by
  filter_upwards [eventually_controlledPrime_endpoint_parameters,
    eventually_controlledPrime_loss_room] with n hend hloss
  dsimp only at hend hloss ⊢
  let y := initialLowerY n (lowerColorCount 1 n)
  have hn : 0 < n := by
    have hU := hend.1
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hU
  have hy : 0 < y := hend.1.trans_le hend.2.1
  refine ⟨hend.1, hend.2.1, hend.2.2.1, hend.2.2.2.1,
    controlledPrime_loss_room hy hloss, hend.2.2.2.2.2.1,
    controlledPrime_unused_of_linear_room hy hend.2.2.2.2.2.2, ?_⟩
  intro d hd hdU
  exact ⟨extracted_scale_le_controlledFloor hy hdU hend.2.2.2.2.1,
    controlled_endpoint_quotient_le_two_mul_U hn hd⟩

end Erdos360

#print axioms Erdos360.controlled_endpoint_quotient_le_two_mul_U
#print axioms Erdos360.eventually_controlledPrime_endpoint_parameters
#print axioms Erdos360.eventually_controlledPrime_loss_room
#print axioms Erdos360.eventually_controlledPrimeTwelve_choice_numerics
