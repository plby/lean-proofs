import ErdosProblems.Erdos308.LargePrime
import ErdosProblems.Erdos308.Candidates

/-!
# Uniform numerical estimates for Martin's Lemma 12

This file contains the elementary (but rather exponent-heavy) estimates which
put the four-prime family from `Lemma12Candidates` into the hypotheses of the
dispersion/subset-sum theorem.  All estimates are uniform in the prime power
`q` in the enlarged elimination range

`x^(1/5) <= q <= x * log(x)^(-30)`.

The exponent `30` leaves enough slack to use the explicit PNT lower bound in
`Lemma12Candidates` without formalising a sharper smooth-number estimate.
-/

namespace Erdos308.Numerics

open Filter Finset Real
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos308.Candidates

/-- The enlarged-log-saving range used by the Lean implementation of Lemma 12. -/
def InStrongEliminationRange (x q : ℕ) : Prop :=
  (x : ℝ) ^ ((1 : ℝ) / 5) ≤ q ∧
    (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ)

/-- The upper endpoint of the strong elimination range is equivalently a
uniform lower bound `log(x)^30 <= x/q`. -/
lemma log_pow_thirty_le_div {x q : ℕ} (hq : 0 < q)
    (hlog : 0 < Real.log (x : ℝ))
    (hupper : (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ)) :
    Real.log (x : ℝ) ^ (30 : ℕ) ≤ (x : ℝ) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : 0 < Real.log (x : ℝ) ^ (30 : ℕ) := pow_pos hlog _
  rw [show (-30 : ℝ) = -(30 : ℝ) by norm_num,
    Real.rpow_neg hlog.le] at hupper
  rw [show (30 : ℝ) = ((30 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast] at hupper
  rw [le_div_iff₀ hqR]
  calc
    Real.log (x : ℝ) ^ (30 : ℕ) * q
        ≤ Real.log (x : ℝ) ^ (30 : ℕ) *
            ((x : ℝ) * (Real.log (x : ℝ) ^ (30 : ℕ))⁻¹) := by
          exact mul_le_mul_of_nonneg_left hupper hpow.le
    _ = (x : ℝ) := by field_simp [hpow.ne']

/-- A convenient integral-power lower bound for the candidate-prime scale. -/
lemma log_pow_seven_le_fourthRoot_div {x q : ℕ} (hq : 0 < q)
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hupper : (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ)) :
    Real.log (x : ℝ) ^ (7 : ℕ) ≤
      fourthRoot ((x : ℝ) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxR : (0 : ℝ) < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hlog
    have hxone : 1 < (x : ℝ) :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hlogpos
    linarith
  have hratio : 0 ≤ (x : ℝ) / q := (div_pos hxR hqR).le
  have h30 := log_pow_thirty_le_div hq (lt_of_lt_of_le (by norm_num) hlog) hupper
  have h28_30 : Real.log (x : ℝ) ^ (28 : ℕ) ≤
      Real.log (x : ℝ) ^ (30 : ℕ) := by
    exact pow_le_pow_right₀ hlog (by norm_num)
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
      (fourthRoot_nonneg _)
  rw [← pow_mul, show 7 * 4 = 28 by norm_num, fourthRoot_pow_four hratio]
  exact h28_30.trans h30

/-! ## Power bookkeeping -/

lemma log_pow_ten_le_rpow_one_third {L y : ℝ}
    (hL : 0 ≤ L) (_hy : 0 ≤ y) (h30 : L ^ (30 : ℕ) ≤ y) :
    L ^ (10 : ℕ) ≤ y ^ ((1 : ℝ) / 3) := by
  calc
    L ^ (10 : ℕ) = (L ^ (30 : ℕ)) ^ ((1 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast]
      rw [← Real.rpow_mul hL]
      norm_num
    _ ≤ y ^ ((1 : ℝ) / 3) :=
      Real.rpow_le_rpow (pow_nonneg hL 30) h30 (by norm_num)

lemma rpow_two_thirds_mul_log_pow_ten_le {L y : ℝ}
    (hL : 0 ≤ L) (hy : 0 ≤ y) (h30 : L ^ (30 : ℕ) ≤ y) :
    y ^ ((2 : ℝ) / 3) * L ^ (10 : ℕ) ≤ y := by
  rcases hy.eq_or_lt with rfl | hypos
  · simp
  calc
    y ^ ((2 : ℝ) / 3) * L ^ (10 : ℕ) ≤
        y ^ ((2 : ℝ) / 3) * y ^ ((1 : ℝ) / 3) := by
      exact mul_le_mul_of_nonneg_left
        (log_pow_ten_le_rpow_one_third hL hy h30)
        (Real.rpow_nonneg hy _)
    _ = y ^ (((2 : ℝ) / 3) + (1 : ℝ) / 3) :=
      (Real.rpow_add hypos _ _).symm
    _ = y := by norm_num

lemma rpow_two_thirds_log_bound {a L y : ℝ}
    (ha : 0 ≤ a) (hL : 1 ≤ L) (hy : 0 ≤ y)
    (h30 : L ^ (30 : ℕ) ≤ y) (hconst : 4800 ≤ a ^ 4 * L ^ 3) :
    200 * y ^ ((2 : ℝ) / 3) * L ^ 3 ≤
      a ^ 4 * y / (24 * L ^ 4) := by
  have hpow7_10 : L ^ (7 : ℕ) ≤ L ^ (10 : ℕ) :=
    pow_le_pow_right₀ hL (by norm_num)
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hycore := rpow_two_thirds_mul_log_pow_ten_le hL0 hy h30
  have hscaled : 4800 * (y ^ ((2 : ℝ) / 3) * L ^ 7) ≤ a ^ 4 * y := by
    calc
      4800 * (y ^ ((2 : ℝ) / 3) * L ^ 7) ≤
          (a ^ 4 * L ^ 3) * (y ^ ((2 : ℝ) / 3) * L ^ 7) := by
        exact mul_le_mul_of_nonneg_right hconst
          (mul_nonneg (Real.rpow_nonneg hy _) (pow_nonneg hL0 7))
      _ = a ^ 4 * (y ^ ((2 : ℝ) / 3) * L ^ 10) := by ring
      _ ≤ a ^ 4 * y := mul_le_mul_of_nonneg_left hycore (pow_nonneg ha 4)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hLpos 4))).2
  calc
    (200 * y ^ ((2 : ℝ) / 3) * L ^ 3) * (24 * L ^ 4) =
        4800 * (y ^ ((2 : ℝ) / 3) * L ^ 7) := by ring
    _ ≤ a ^ 4 * y := hscaled

/-- The numerical block size is eventually below the explicit PNT lower
bound for the four-prime candidate family, uniformly in `q`. -/
theorem eventually_martinBlockBound_le_candidateLower {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    ∀ᶠ x : ℕ in atTop, ∀ q : ℕ, 0 < q → InStrongEliminationRange x q →
      (Erdos308.LargePrime.martinBlockBound x q : ℝ) ≤
        (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
            (80 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 := by
  let a : ℝ := (1 - fourthRoot ξ) / 80
  have hc1 : fourthRoot ξ < 1 := fourthRoot_lt_one hξ1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha4 : 0 < a ^ (4 : ℕ) := pow_pos ha _
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually_ge_atTop
    (max 2 (4800 / a ^ (4 : ℕ)))] with x hlogLarge
  intro q hq hrange
  let L : ℝ := Real.log (x : ℝ)
  let y : ℝ := (x : ℝ) / q
  let t : ℝ := fourthRoot y
  have hL2 : 2 ≤ L := (le_max_left 2 (4800 / a ^ (4 : ℕ))).trans hlogLarge
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hxpos : (0 : ℝ) < x := by
    have hxone : 1 < (x : ℝ) :=
      (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hLpos
    linarith
  have hxNat : 0 < x := by exact_mod_cast hxpos
  have hypos : 0 < y := div_pos hxpos hqR
  have htpos : 0 < t := fourthRoot_pos hypos
  have h30 : L ^ (30 : ℕ) ≤ y := by
    exact log_pow_thirty_le_div hq hLpos hrange.2
  have hconst0 : 4800 / a ^ (4 : ℕ) ≤ L :=
    (le_max_right 2 (4800 / a ^ (4 : ℕ))).trans hlogLarge
  have hconstLinear : 4800 ≤ a ^ (4 : ℕ) * L := by
    rw [div_le_iff₀ ha4] at hconst0
    nlinarith
  have hL_le_cube : L ≤ L ^ (3 : ℕ) := by
    simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (3 : ℕ))
  have hconst : 4800 ≤ a ^ (4 : ℕ) * L ^ (3 : ℕ) :=
    hconstLinear.trans (mul_le_mul_of_nonneg_left hL_le_cube ha4.le)
  have hrealBound :
      200 * y ^ ((2 : ℝ) / 3) * L ^ 3 ≤
        a ^ 4 * y / (24 * L ^ 4) :=
    rpow_two_thirds_log_bound ha.le hL1 hypos.le h30 hconst
  have hqleX : (q : ℝ) ≤ x := by
    calc
      (q : ℝ) ≤ (x : ℝ) * L ^ (-30 : ℝ) := hrange.2
      _ ≤ (x : ℝ) * 1 := mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)) hxpos.le
      _ = x := mul_one _
  have htq : t ≤ (q : ℝ) := by
    simpa [t, y] using
      (Erdos308.LargePrime.fourthRoot_div_le_of_fifthRoot_le hq hrange.1)
  have htx : t ≤ (x : ℝ) := htq.trans hqleX
  have hlogtpos : 0 < Real.log t := by
    have htlog7 : L ^ (7 : ℕ) ≤ t := by
      simpa [L, y, t] using
        (log_pow_seven_le_fourthRoot_div hq hL1 hrange.2)
    have hLlt : 1 < L := by linarith
    have hOnePow : (1 : ℝ) < L ^ (7 : ℕ) := by
      calc
        (1 : ℝ) < L := hLlt
        _ ≤ L ^ (7 : ℕ) := by
          simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ (7 : ℕ))
    have htone : 1 < t := hOnePow.trans_le htlog7
    exact Real.log_pos htone
  have hlogtle : Real.log t ≤ L := by
    exact Real.log_le_log htpos htx
  have hfrac : a * t / L ≤ a * t / Real.log t :=
    div_le_div_of_nonneg_left (mul_nonneg ha.le htpos.le) hlogtpos hlogtle
  have hpowfrac : (a * t / L) ^ (4 : ℕ) ≤
      (a * t / Real.log t) ^ (4 : ℕ) := by
    exact pow_le_pow_left₀ (by positivity) hfrac _
  have ht4 : t ^ (4 : ℕ) = y := fourthRoot_pow_four hypos.le
  calc
    (Erdos308.LargePrime.martinBlockBound x q : ℝ) ≤
        200 * y ^ ((2 : ℝ) / 3) * L ^ 3 := by
      simpa [L, y] using Erdos308.LargePrime.martinBlockBound_cast_le
        (x := x) (q := q) hxNat
    _ ≤ a ^ 4 * y / (24 * L ^ 4) := hrealBound
    _ = (a * t / L) ^ 4 / 24 := by
      have heq : (a * t / L) ^ 4 / 24 =
          a ^ 4 * y / (24 * L ^ 4) := by
        rw [div_pow, mul_pow, ht4]
        ring
      exact heq.symm
    _ ≤ (a * t / Real.log t) ^ 4 / 24 := by gcongr
    _ = (((1 - fourthRoot ξ) * t / (80 * Real.log t)) ^ 4) / 24 := by
      dsimp [a]
      congr 2
      ring
    _ = (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
          (80 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 := by
      rfl

lemma q_cast_le_x_of_strongRange {x q : ℕ}
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hrange : InStrongEliminationRange x q) : (q : ℝ) ≤ x := by
  calc
    (q : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ (-30 : ℝ) := hrange.2
    _ ≤ (x : ℝ) * 1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_one_of_one_le_of_nonpos hlog (by norm_num)) (by positivity)
    _ = x := mul_one _

/-- The stronger logarithmic cutoff used for the uniform construction implies
the `log⁻²²` range in the statement of Lemma 12. -/
lemma strongRange_to_eliminationRange {x q : ℕ}
    (hlog : 1 ≤ Real.log (x : ℝ))
    (hrange : InStrongEliminationRange x q) :
    Erdos308.LargePrime.InEliminationRange x q := by
  refine ⟨hrange.1, hrange.2.trans ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by positivity
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num : (-30 : ℝ) ≤ -22)) hx0

/-- The two numerical hypotheses in Martin's prescribed subset-sum lemma,
plus the older dispersion threshold, in the concrete `k = 4` form. -/
lemma fourPrime_subsetSum_and_dispersion_thresholds
    {x q : ℕ} (hq : 0 < q) (hL2 : 2 ≤ Real.log (x : ℝ))
    (hLLq2 : 2 ≤ Real.log (Real.log (q : ℝ)))
    (hrange : InStrongEliminationRange x q) :
    let B : ℝ := (x : ℝ) / q
    Real.log q ^ ((3 : ℝ) / 2) /
          Real.log (Real.log q) ^ (2 : ℝ) < B ∧
      200 * (B ^ ((2 : ℝ) / 3) * Real.log q ^ (3 : ℝ) /
          Real.log (Real.log q) ^ ((8 : ℝ) / 3)) <
        Erdos308.LargePrime.martinBlockBound x q ∧
      200 * (Real.log q / Real.log (Real.log q)) ^ (4 : ℕ) <
        Erdos308.LargePrime.martinBlockBound x q := by
  dsimp only
  let L : ℝ := Real.log (x : ℝ)
  let lq : ℝ := Real.log (q : ℝ)
  let llq : ℝ := Real.log lq
  let y : ℝ := (x : ℝ) / q
  let A : ℝ := 200 * y ^ ((2 : ℝ) / 3) * L ^ (3 : ℕ)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLLq : 2 ≤ llq := by simpa [llq, lq] using hLLq2
  have hLLqpos : 0 < llq := by linarith
  have hlqone : 1 < lq := by
    have : 0 < Real.log lq := by simpa [llq] using hLLqpos
    exact (Real.log_pos_iff (by positivity)).mp this
  have hlqpos : 0 < lq := by linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hqleX := q_cast_le_x_of_strongRange hL1 hrange
  have hlqL : lq ≤ L := by
    simpa [lq, L] using Real.log_le_log hqR hqleX
  have hypos : 0 < y := by
    dsimp [y]
    exact div_pos (by
      have hxone : 1 < (x : ℝ) :=
        (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hLpos
      linarith) hqR
  have h30 : L ^ (30 : ℕ) ≤ y := by
    simpa [L, y] using log_pow_thirty_le_div hq hLpos hrange.2
  have hyone : 1 ≤ y := by
    calc
      (1 : ℝ) ≤ L ^ (30 : ℕ) := by
        simpa using pow_le_pow_right₀ hL1 (by norm_num : 0 ≤ (30 : ℕ))
      _ ≤ y := h30
  have hlqPow : lq ^ ((3 : ℝ) / 2) ≤ L ^ (2 : ℕ) := by
    calc
      lq ^ ((3 : ℝ) / 2) ≤ L ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hlqpos.le hlqL (by norm_num)
      _ ≤ L ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
  have hLLqPowOne : 1 ≤ llq ^ (2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hBsourceLe :
      lq ^ ((3 : ℝ) / 2) / llq ^ (2 : ℝ) ≤ L ^ (2 : ℕ) := by
    calc
      lq ^ ((3 : ℝ) / 2) / llq ^ (2 : ℝ) ≤
          lq ^ ((3 : ℝ) / 2) :=
        div_le_self (Real.rpow_nonneg hlqpos.le _) hLLqPowOne
      _ ≤ L ^ (2 : ℕ) := hlqPow
  have hLpowStrict : L ^ (2 : ℕ) < L ^ (30 : ℕ) :=
    pow_lt_pow_right₀ (by linarith : 1 < L) (by norm_num)
  have hBsource : lq ^ ((3 : ℝ) / 2) / llq ^ (2 : ℝ) < y :=
    hBsourceLe.trans_lt (hLpowStrict.trans_le h30)
  have hlq3 : lq ^ (3 : ℕ) ≤ L ^ (3 : ℕ) :=
    pow_le_pow_left₀ hlqpos.le hlqL _
  have hLLq83 : 2 ≤ llq ^ ((8 : ℝ) / 3) := by
    calc
      (2 : ℝ) ≤ llq := hLLq
      _ = llq ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ ≤ llq ^ ((8 : ℝ) / 3) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsourceHalf :
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) ≤ A / 2 := by
    have hnum : 0 ≤ 200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ)) := by positivity
    calc
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) =
          (200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ))) /
            llq ^ ((8 : ℝ) / 3) := by ring
      _ ≤ (200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ))) / 2 :=
        div_le_div_of_nonneg_left hnum (by norm_num) hLLq83
      _ ≤ (200 * (y ^ ((2 : ℝ) / 3) * L ^ (3 : ℕ))) / 2 := by
        gcongr
      _ = A / 2 := by dsimp [A]; ring
  have hA2 : 2 ≤ A := by
    have hy23 : 1 ≤ y ^ ((2 : ℝ) / 3) :=
      Real.one_le_rpow hyone (by norm_num)
    have hL3 : 1 ≤ L ^ (3 : ℕ) := by
      simpa using pow_le_pow_right₀ hL1 (by norm_num : 0 ≤ (3 : ℕ))
    dsimp [A]
    nlinarith [mul_le_mul hy23 hL3 (by norm_num : (0 : ℝ) ≤ 1)
      (Real.rpow_nonneg hypos.le _)]
  have hfloor : A <
      (Erdos308.LargePrime.martinBlockBound x q : ℝ) + 1 := by
    simpa only [A, L, y, Erdos308.LargePrime.martinBlockBound]
      using Nat.lt_floor_add_one A
  have hcardSource :
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) <
        Erdos308.LargePrime.martinBlockBound x q := by
    calc
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) ≤ A / 2 := hsourceHalf
      _ ≤ A - 1 := by linarith
      _ < Erdos308.LargePrime.martinBlockBound x q := by linarith
  have hL20 : L ^ (20 : ℕ) ≤ y ^ ((2 : ℝ) / 3) := by
    calc
      L ^ (20 : ℕ) = (L ^ (30 : ℕ)) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast]
        rw [← Real.rpow_mul hLpos.le]
        norm_num
      _ ≤ y ^ ((2 : ℝ) / 3) :=
        Real.rpow_le_rpow (pow_nonneg hLpos.le 30) h30 (by norm_num)
  have htwoL : 2 * L ≤ y ^ ((2 : ℝ) / 3) := by
    calc
      2 * L ≤ L ^ (20 : ℕ) := by
        have hLpow : L ^ (2 : ℕ) ≤ L ^ (20 : ℕ) :=
          pow_le_pow_right₀ hL1 (by norm_num)
        nlinarith [sq_nonneg (L - 1)]
      _ ≤ y ^ ((2 : ℝ) / 3) := hL20
  have hquot : 0 ≤ lq / llq ∧ lq / llq ≤ L := by
    constructor
    · positivity
    · calc
        lq / llq ≤ lq := div_le_self hlqpos.le (by linarith)
        _ ≤ L := hlqL
  have hdispLe : 200 * (lq / llq) ^ (4 : ℕ) ≤ A / 2 := by
    have hpowq : (lq / llq) ^ (4 : ℕ) ≤ L ^ (4 : ℕ) :=
      pow_le_pow_left₀ hquot.1 hquot.2 _
    calc
      200 * (lq / llq) ^ (4 : ℕ) ≤ 200 * L ^ (4 : ℕ) := by gcongr
      _ ≤ A / 2 := by
        dsimp [A]
        have hL3pos : 0 < L ^ (3 : ℕ) := pow_pos hLpos _
        calc
          200 * L ^ (4 : ℕ) = (200 * L ^ 3) * L := by ring
          _ ≤ (200 * L ^ 3) * (y ^ ((2 : ℝ) / 3) / 2) := by
            gcongr
            rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
            simpa [mul_comm] using htwoL
          _ = 200 * y ^ ((2 : ℝ) / 3) * L ^ 3 / 2 := by ring
  have hdisp : 200 * (lq / llq) ^ (4 : ℕ) <
      Erdos308.LargePrime.martinBlockBound x q := by
    exact hdispLe.trans_lt ((show A / 2 <
      (Erdos308.LargePrime.martinBlockBound x q : ℝ) by
        calc
          A / 2 ≤ A - 1 := by linarith
          _ < _ := by linarith))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [lq, llq, y,
      show Real.log (Real.log (q : ℝ)) ^ (2 : ℝ) =
          Real.log (Real.log (q : ℝ)) ^ (2 : ℕ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]] using hBsource
  · simpa only [lq, llq, y,
      show Real.log (q : ℝ) ^ (3 : ℝ) =
          Real.log (q : ℝ) ^ (3 : ℕ) by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]] using hcardSource
  · simpa only [lq, llq] using hdisp

/-! ## A Chebyshev-width candidate band

For Problem 308 we only need a fixed, very wide multiplicative prime band.
This avoids importing the effective prime-number-theorem package used by the
sharper `Erdos285` development. -/

/-- Lower endpoint for the auxiliary-prime band. -/
def crootCandidateRatio : ℝ := 2 / 5

/-- Corresponding lower endpoint for the products of four primes. -/
def crootIntervalRatio : ℝ := crootCandidateRatio ^ 4

lemma fourthRoot_crootIntervalRatio :
    fourthRoot crootIntervalRatio = crootCandidateRatio := by
  norm_num [crootIntervalRatio, crootCandidateRatio, fourthRoot]

lemma primeBand_card_eq {c t : ℝ} (_hc : 0 ≤ c) (hc1 : c ≤ 1)
    (ht : 0 ≤ t) :
    ((primeBand c t).card : ℝ) =
      Nat.primeCounting ⌊t⌋₊ - Nat.primeCounting ⌊c * t⌋₊ := by
  have hct : c * t ≤ t := by nlinarith
  have hfloor : ⌊c * t⌋₊ ≤ ⌊t⌋₊ := Nat.floor_mono hct
  have hsub : Nat.primesLE ⌊c * t⌋₊ ⊆ Nat.primesLE ⌊t⌋₊ :=
    Nat.primesLE_mono hfloor
  rw [primeBand, Finset.card_sdiff_of_subset hsub,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  rw [Nat.cast_sub (Nat.monotone_primeCounting hfloor)]

lemma primeBand_card_le_candidatePrimes_card_add_one (p : ℕ) (c t : ℝ) :
    (primeBand c t).card ≤ (candidatePrimes p c t).card + 1 := by
  by_cases hp : p ∈ primeBand c t
  · rw [candidatePrimes, Finset.card_erase_of_mem hp]
    have := Finset.card_pos.mpr ⟨p, hp⟩
    omega
  · simp [candidatePrimes, hp]

lemma eventually_log_add_two_le_one_hundredth :
    ∀ᶠ t : ℝ in atTop, Real.log (t + 2) ≤ t / 100 := by
  filter_upwards [eventually_ge_atTop (50000 : ℝ)] with t ht
  have ht2 : 0 ≤ t + 2 := by linarith
  have hlog : Real.log (t + 2) ≤ (t + 2) ^ ((1 : ℝ) / 2) / ((1 : ℝ) / 2) :=
    Real.log_le_rpow_div ht2 (by norm_num)
  rw [show (t + 2) ^ ((1 : ℝ) / 2) = Real.sqrt (t + 2) by
    rw [Real.sqrt_eq_rpow]] at hlog
  have hsqrt : 0 ≤ Real.sqrt (t + 2) := Real.sqrt_nonneg _
  have hsqrtSq : Real.sqrt (t + 2) ^ 2 = t + 2 := Real.sq_sqrt ht2
  have hquad : 200 * Real.sqrt (t + 2) ≤ t := by
    nlinarith [sq_nonneg (t - 50000)]
  norm_num at hlog
  linarith

/-- Chebyshev's elementary bounds give enough primes in the fixed interval
`(2t/5,t]` for the qualitative Croot construction. -/
theorem eventually_primeBand_card_lower_croot :
    ∀ᶠ t : ℝ in atTop,
      (1 - crootCandidateRatio) * t / (20 * Real.log t) ≤
        ((primeBand crootCandidateRatio t).card : ℝ) := by
  have hscale : Tendsto (fun t : ℝ ↦ crootCandidateRatio * t) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num [crootCandidateRatio])
  have hupper := hscale.eventually
    (Chebyshev.eventually_primeCounting_le (ε := (1 / 100 : ℝ)) (by norm_num))
  filter_upwards [eventually_ge_atTop (50000 : ℝ),
    eventually_log_add_two_le_one_hundredth,
    Real.tendsto_log_atTop.eventually_ge_atTop (14 : ℝ), hupper]
      with t ht hlogadd hlogt hpiUpper
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := by linarith
  have hpiLowerRaw := Chebyshev.pi_ge' (show 1 < t by linarith)
  have htminus : (99 / 100 : ℝ) * t ≤ t - 1 := by nlinarith
  have hlowerNumerator : (2 / 3 : ℝ) * t ≤
      (t - 1) * Real.log 2 - Real.log (t + 2) := by
    have hlog2 := Real.log_two_gt_d9
    nlinarith
  have hpiLower : (2 / 3 : ℝ) * (t / Real.log t) ≤
      Nat.primeCounting ⌊t⌋₊ := by
    calc
      (2 / 3 : ℝ) * (t / Real.log t) =
          ((2 / 3 : ℝ) * t) / Real.log t := by ring
      _ ≤ (((t - 1) * Real.log 2 - Real.log (t + 2)) / Real.log t) :=
        (div_le_div_iff_of_pos_right hlogpos).2 hlowerNumerator
      _ ≤ Nat.primeCounting ⌊t⌋₊ := hpiLowerRaw
  have hlogFiveHalves : Real.log (5 / 2 : ℝ) < 7 / 5 := by
    have hlt : Real.log (5 / 2 : ℝ) < Real.log 4 := by
      exact Real.strictMonoOn_log
        (by norm_num) (by norm_num) (by norm_num)
    rw [Real.log_four_eq] at hlt
    nlinarith [Real.log_two_lt_d9]
  have hlogScaled : (9 / 10 : ℝ) * Real.log t ≤
      Real.log (crootCandidateRatio * t) := by
    rw [show crootCandidateRatio * t = t / (5 / 2 : ℝ) by
      simp [crootCandidateRatio]; ring,
      Real.log_div htpos.ne' (by norm_num : (5 / 2 : ℝ) ≠ 0)]
    linarith
  have hlogScaledPos : 0 < Real.log (crootCandidateRatio * t) :=
    (mul_pos (by norm_num) hlogpos).trans_le hlogScaled
  have hcoeff : Real.log 4 + 1 / 100 < (7 / 5 : ℝ) := by
    rw [Real.log_four_eq]
    nlinarith [Real.log_two_lt_d9]
  have hpiUpper' : (Nat.primeCounting
      ⌊crootCandidateRatio * t⌋₊ : ℝ) ≤
      (28 / 45 : ℝ) * (t / Real.log t) := by
    calc
      (Nat.primeCounting ⌊crootCandidateRatio * t⌋₊ : ℝ) ≤
          (Real.log 4 + 1 / 100) * (crootCandidateRatio * t) /
            Real.log (crootCandidateRatio * t) := hpiUpper
      _ ≤ (Real.log 4 + 1 / 100) * (crootCandidateRatio * t) /
            ((9 / 10 : ℝ) * Real.log t) := by
        have hnum : 0 ≤ (Real.log 4 + 1 / 100) *
            (crootCandidateRatio * t) := by
          have : 0 ≤ Real.log 4 + 1 / 100 := by
            rw [Real.log_four_eq]
            nlinarith [Real.log_two_gt_d9]
          exact mul_nonneg this
            (mul_nonneg (by norm_num [crootCandidateRatio]) htpos.le)
        exact div_le_div_of_nonneg_left
          hnum
          (mul_pos (by norm_num) hlogpos) hlogScaled
      _ ≤ (28 / 45 : ℝ) * (t / Real.log t) := by
        rw [crootCandidateRatio]
        have ht0 : 0 ≤ t := htpos.le
        have hden : 0 < (9 / 10 : ℝ) * Real.log t :=
          mul_pos (by norm_num) hlogpos
        rw [div_le_iff₀ hden]
        field_simp [hlogpos.ne']
        nlinarith
  rw [primeBand_card_eq (by norm_num [crootCandidateRatio])
    (by norm_num [crootCandidateRatio]) htpos.le]
  calc
    (1 - crootCandidateRatio) * t / (20 * Real.log t) ≤
        ((2 / 3 : ℝ) - 28 / 45) * (t / Real.log t) := by
      calc
        (1 - crootCandidateRatio) * t / (20 * Real.log t) =
            ((1 - crootCandidateRatio) / 20) * (t / Real.log t) := by ring
        _ ≤ ((2 / 3 : ℝ) - 28 / 45) * (t / Real.log t) := by
          gcongr
          norm_num [crootCandidateRatio]
    _ = (2 / 3 : ℝ) * (t / Real.log t) -
        (28 / 45 : ℝ) * (t / Real.log t) := by ring
    _ ≤ (Nat.primeCounting ⌊t⌋₊ : ℝ) -
        Nat.primeCounting ⌊crootCandidateRatio * t⌋₊ :=
      sub_le_sub hpiLower hpiUpper'

theorem eventually_candidatePrimes_card_lower_croot :
    ∀ᶠ t : ℝ in atTop, ∀ p : ℕ,
      (1 - crootCandidateRatio) * t / (40 * Real.log t) ≤
        ((candidatePrimes p crootCandidateRatio t).card : ℝ) := by
  have hgrowth : Tendsto
      (fun t : ℝ ↦ (1 - crootCandidateRatio) * t / (40 * Real.log t))
      atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show 0 < (1 - crootCandidateRatio) / 40 by
        norm_num [crootCandidateRatio])
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log ht]
    ring
  filter_upwards [eventually_primeBand_card_lower_croot,
    hgrowth.eventually_ge_atTop 1, eventually_gt_atTop 2]
      with t hband hgrow ht
  intro p
  have hcardRel : ((primeBand crootCandidateRatio t).card : ℝ) ≤
      (candidatePrimes p crootCandidateRatio t).card + 1 := by
    exact_mod_cast primeBand_card_le_candidatePrimes_card_add_one p
      crootCandidateRatio t
  have htwice :
      2 * ((1 - crootCandidateRatio) * t / (40 * Real.log t)) =
        (1 - crootCandidateRatio) * t / (20 * Real.log t) := by ring
  rw [← htwice] at hband
  linarith

theorem eventually_rawCandidates_card_lower_croot :
    ∀ᶠ t : ℝ in atTop, ∀ p : ℕ,
      (((1 - crootCandidateRatio) * t / (80 * Real.log t)) ^ 4) / 24 ≤
        ((rawCandidates p crootCandidateRatio t).card : ℝ) := by
  have hgrowth : Tendsto
      (fun t : ℝ ↦ (1 - crootCandidateRatio) * t / (40 * Real.log t))
      atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show 0 < (1 - crootCandidateRatio) / 40 by
        norm_num [crootCandidateRatio])
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log ht]
    ring
  filter_upwards [eventually_candidatePrimes_card_lower_croot,
    hgrowth.eventually_ge_atTop 8, eventually_gt_atTop 2]
      with t hprime hgrowth8 ht
  intro p
  let A : ℝ := (1 - crootCandidateRatio) * t / (40 * Real.log t)
  have hcard8 : 8 ≤ (candidatePrimes p crootCandidateRatio t).card := by
    exact_mod_cast hgrowth8.trans (hprime p)
  have hhalf : (1 - crootCandidateRatio) * t / (80 * Real.log t) ≤
      (((candidatePrimes p crootCandidateRatio t).card + 1 - 4 : ℕ) : ℝ) := by
    have hhalfCard : (1 - crootCandidateRatio) * t / (80 * Real.log t) ≤
        ((candidatePrimes p crootCandidateRatio t).card : ℝ) / 2 := by
      calc
        _ = A / 2 := by dsimp [A]; ring
        _ ≤ _ := by gcongr; exact hprime p
    rw [show (candidatePrimes p crootCandidateRatio t).card + 1 - 4 =
      (candidatePrimes p crootCandidateRatio t).card - 3 by omega,
      Nat.cast_sub (by omega)]
    push_cast
    have hc8 : (8 : ℝ) ≤ (candidatePrimes p crootCandidateRatio t).card := by
      exact_mod_cast hcard8
    nlinarith
  calc
    (((1 - crootCandidateRatio) * t / (80 * Real.log t)) ^ 4) / 24 ≤
        (((((candidatePrimes p crootCandidateRatio t).card + 1 - 4 : ℕ) : ℝ) ^ 4) /
          24) := by
      have hbase : 0 ≤
          (1 - crootCandidateRatio) * t / (80 * Real.log t) := by
        exact div_nonneg
          (mul_nonneg (by norm_num [crootCandidateRatio]) (by linarith))
          (mul_nonneg (by norm_num) (Real.log_pos (by linarith)).le)
      gcongr
    _ ≤ ((rawCandidates p crootCandidateRatio t).card : ℝ) := by
      have hraw := rawCandidates_card_lower p crootCandidateRatio t
      norm_num at hraw
      exact hraw

theorem eventually_exists_rawCandidates_subset_croot :
    ∀ᶠ t : ℝ in atTop, ∀ (p C : ℕ),
      (C : ℝ) ≤
        (((1 - crootCandidateRatio) * t / (80 * Real.log t)) ^ 4) / 24 →
      ∃ M ⊆ rawCandidates p crootCandidateRatio t, M.card = C := by
  filter_upwards [eventually_rawCandidates_card_lower_croot] with t ht
  intro p C hC
  apply Finset.exists_subset_card_eq
  exact_mod_cast hC.trans (ht p)

theorem eventually_rawCandidates_subset_at_elimination_scale_croot :
    ∀ᶠ x : ℕ in atTop, ∀ (q p C : ℕ), 0 < q →
      (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ) →
      (C : ℝ) ≤
        (((1 - fourthRoot crootIntervalRatio) * fourthRoot ((x : ℝ) / q) /
            (80 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 →
      ∃ M ⊆ rawCandidates p (fourthRoot crootIntervalRatio)
          (fourthRoot ((x : ℝ) / q)), M.card = C := by
  obtain ⟨T, hT⟩ := eventually_atTop.1
    eventually_exists_rawCandidates_subset_croot
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlogTop.eventually_ge_atTop (max T 1)] with x hlogMax
  intro q p C hq hupper hC
  have hlog : 1 ≤ Real.log (x : ℝ) := (le_max_right T 1).trans hlogMax
  have hxT : T ≤ Real.log (x : ℝ) ^ (7 : ℕ) := by
    calc
      T ≤ Real.log (x : ℝ) := (le_max_left T 1).trans hlogMax
      _ ≤ Real.log (x : ℝ) ^ (7 : ℕ) := by
        simpa using pow_le_pow_right₀ hlog (by norm_num : 1 ≤ (7 : ℕ))
  have htT : T ≤ fourthRoot ((x : ℝ) / q) :=
    hxT.trans (log_pow_seven_le_fourthRoot_div hq hlog hupper)
  rw [fourthRoot_crootIntervalRatio] at hC ⊢
  exact hT _ htT p C hC

/-! ## Final fixed-band candidate family -/

theorem eventually_exists_croot_candidate_family :
    ∀ᶠ x : ℕ in atTop, ∀ (p ν : ℕ), p.Prime → 0 < ν →
      InStrongEliminationRange x (p ^ ν) →
      ∃ M : Finset ℕ,
        M.card = Erdos308.LargePrime.martinBlockBound x (p ^ ν) ∧
        M ⊆ rawCandidates p (fourthRoot crootIntervalRatio)
          (fourthRoot ((x : ℝ) / (p ^ ν : ℕ))) ∧
        ∀ residue : ZMod (p ^ ν), ∃ K : Finset ℕ,
          K ⊆ M ∧
          K.card ≤ Erdos308.LargePrime.martinBlockBound x (p ^ ν) ∧
          K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = residue := by
  have hExtract := eventually_rawCandidates_subset_at_elimination_scale_croot
  have hCandidateBound :=
    eventually_martinBlockBound_le_candidateLower (ξ := crootIntervalRatio)
      (by norm_num [crootIntervalRatio, crootCandidateRatio])
      (by norm_num [crootIntervalRatio, crootCandidateRatio])
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllTop : Tendsto
      (fun q : ℕ ↦ Real.log (Real.log (q : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨Qll, hQll⟩ := eventually_atTop.1
    (hllTop.eventually_ge_atTop (2 : ℝ))
  obtain ⟨Qsubset, hQsubset⟩ := eventually_atTop.1
    (Erdos285.SubsetSum.eventually_bounded_inverse_subset_sum_of_martin_hypotheses
      4 (by omega))
  let Q : ℕ := max Qll Qsubset
  have hrootTop : Tendsto (fun x : ℕ ↦
      (x : ℝ) ^ ((1 : ℝ) / 5)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 5)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hExtract, hCandidateBound,
    hlogTop.eventually_ge_atTop 2,
    hrootTop.eventually_ge_atTop (Q : ℝ)]
      with x hExtractX hBoundX hlogX hrootQ
  intro p ν hp hν hrange
  let q : ℕ := p ^ ν
  have hq : 0 < q := pow_pos hp.pos ν
  have hQq : Q ≤ q := by exact_mod_cast (hrootQ.trans hrange.1)
  have hllq : 2 ≤ Real.log (Real.log (q : ℝ)) :=
    hQll q ((le_max_left Qll Qsubset).trans hQq)
  have hthreshold := fourPrime_subsetSum_and_dispersion_thresholds
    hq hlogX hllq hrange
  obtain ⟨M, hM, hMcard⟩ := hExtractX q p
    (Erdos308.LargePrime.martinBlockBound x q) hq hrange.2
      (hBoundX q hq hrange)
  have hx : 0 < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := by linarith
    have hxone : 1 < x := by
      exact_mod_cast ((Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hlogpos)
    omega
  have hMsource : ∀ m ∈ M,
      (m : ℝ) < (x : ℝ) / q ∧
        Erdos285.Dispersion.IsKPrimeProductAway 4 q m := by
    intro m hm
    exact ⟨rawCandidate_lt_eliminationScale hx hp (hM hm),
      rawCandidate_isKPrimeProductAway (ν := ν) hp (hM hm)⟩
  have hBpos : 0 < (x : ℝ) / q := by positivity
  have hsurj := hQsubset q ((le_max_right Qll Qsubset).trans hQq)
    (Erdos308.LargePrime.martinBlockBound x q) ((x : ℝ) / q) M
    (by simp [hMcard]) hBpos
    (by convert hthreshold.1 using 1 <;> norm_num [Real.rpow_natCast])
    (by
      rw [hMcard]
      convert hthreshold.2.1 using 1 <;> norm_num [Real.rpow_natCast])
    hMsource
  exact ⟨M, hMcard, hM, hsurj⟩

theorem eventually_crootStepData :
    ∀ᶠ x : ℕ in atTop, ∀ (q : ℕ) (r : ℚ), IsPrimePow q →
      InStrongEliminationRange x q →
      q ∈ Erdos285.PrimePowers.primePowerParts r.den →
      (∀ ℓ : ℕ, IsPrimePow ℓ → ℓ ∣ r.den / q → ℓ < q) →
      ∃ M : Finset ℕ,
        Erdos308.LargePrime.CandidateData crootIntervalRatio x q r M ∧
        Erdos308.LargePrime.BoundedInverseSubsetSurjective
          q (Erdos308.LargePrime.martinBlockBound x q) M := by
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_exists_croot_candidate_family,
    eventually_ge_atTop 1, hlogTop.eventually_ge_atTop 1]
      with x hfamily hx hlog
  intro q r hqpp hrange hqpart hcofactor
  rcases (isPrimePow_nat_iff q).mp hqpp with ⟨p, ν, hp, hν, rfl⟩
  obtain ⟨M, hcard, hM, hsurj⟩ :=
    hfamily p ν hp hν hrange
  refine ⟨M, ?_, ?_⟩
  · exact Erdos308.LargePrime.candidateData_of_rawCandidateFamily
      (by norm_num [crootIntervalRatio, crootCandidateRatio])
      (by norm_num [crootIntervalRatio, crootCandidateRatio])
      (by omega) hp hν
      (strongRange_to_eliminationRange hlog hrange)
      hqpart hM hcofactor
  · exact hsurj

end

end Erdos308.Numerics

#print axioms Erdos308.Numerics.eventually_crootStepData
