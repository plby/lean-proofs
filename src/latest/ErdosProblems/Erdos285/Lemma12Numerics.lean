import ErdosProblems.Erdos285.Lemma12
import ErdosProblems.Erdos285.Lemma12Candidates

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

namespace Erdos285.Lemma12Numerics

open Filter Finset Real
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

open Erdos285.Lemma12Candidates

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

/-- The candidate-prime PNT estimate can be made uniform in the single prime
which is erased from the band.  This uniformity is needed because the base
prime of `q` varies with `x`. -/
theorem eventually_candidatePrimes_card_lower_uniform {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t : ℝ in atTop, ∀ p : ℕ,
      (1 - c) * t / (8 * Real.log t) ≤
        ((candidatePrimes p c t).card : ℝ) := by
  have hgrowth : Tendsto (fun t : ℝ ↦ (1 - c) * t / (8 * Real.log t))
      atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show 0 < (1 - c) / 8 by positivity)
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log ht]
    ring
  filter_upwards [eventually_primeBand_card_lower hc hc1,
    hgrowth.eventually_ge_atTop 1, eventually_gt_atTop 2]
      with t hband hgrow ht
  intro p
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  let A : ℝ := (1 - c) * t / (8 * Real.log t)
  have htwice : 2 * A = (1 - c) * t / (4 * Real.log t) := by
    dsimp [A]
    ring
  have hband2 : 2 * A ≤ ((primeBand c t).card : ℝ) := by
    rwa [htwice]
  have hcardRel : ((primeBand c t).card : ℝ) ≤
      (candidatePrimes p c t).card + 1 := by
    exact_mod_cast primeBand_card_le_candidatePrimes_card_add_one p c t
  have hA : 1 ≤ A := by simpa [A] using hgrow
  dsimp [A] at *
  linarith

/-- Uniform PNT lower bound for four-prime products. -/
theorem eventually_rawCandidates_card_lower_uniform {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t : ℝ in atTop, ∀ p : ℕ,
      (((1 - c) * t / (16 * Real.log t)) ^ 4) / 24 ≤
        ((rawCandidates p c t).card : ℝ) := by
  have hgrowth : Tendsto (fun t : ℝ ↦ (1 - c) * t / (8 * Real.log t))
      atTop atTop := by
    have h := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop
      (show 0 < (1 - c) / 8 by positivity)
    refine (h.comp Real.tendsto_log_atTop).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [Function.comp_apply, pow_one]
    rw [Real.exp_log ht]
    ring
  filter_upwards [eventually_candidatePrimes_card_lower_uniform hc hc1,
    hgrowth.eventually_ge_atTop 8, eventually_gt_atTop 2]
      with t hprime hgrowth8 ht
  intro p
  let A : ℝ := (1 - c) * t / (8 * Real.log t)
  have hcard8 : 8 ≤ (candidatePrimes p c t).card := by
    exact_mod_cast hgrowth8.trans (hprime p)
  have hhalf : (1 - c) * t / (16 * Real.log t) ≤
      (((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) := by
    have hhalfCard : (1 - c) * t / (16 * Real.log t) ≤
        ((candidatePrimes p c t).card : ℝ) / 2 := by
      calc
        (1 - c) * t / (16 * Real.log t) = A / 2 := by dsimp [A]; ring
        _ ≤ ((candidatePrimes p c t).card : ℝ) / 2 := by gcongr; exact hprime p
    have hfour : 4 ≤ (candidatePrimes p c t).card := by omega
    calc
      (1 - c) * t / (16 * Real.log t) ≤
          ((candidatePrimes p c t).card : ℝ) / 2 := hhalfCard
      _ ≤ (((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) := by
        rw [show (candidatePrimes p c t).card + 1 - 4 =
          (candidatePrimes p c t).card - 3 by omega, Nat.cast_sub (by omega)]
        push_cast
        have hc8 : (8 : ℝ) ≤ (candidatePrimes p c t).card := by
          exact_mod_cast hcard8
        nlinarith
  have hbaseNonneg : 0 ≤ (1 - c) * t / (16 * Real.log t) := by
    exact (div_nonneg
      (mul_nonneg (sub_nonneg.mpr hc1.le) (by linarith))
      (mul_nonneg (by norm_num) (Real.log_pos (by linarith)).le))
  calc
    (((1 - c) * t / (16 * Real.log t)) ^ 4) / 24 ≤
        (((((candidatePrimes p c t).card + 1 - 4 : ℕ) : ℝ) ^ 4) / 24) := by
      gcongr
    _ ≤ ((rawCandidates p c t).card : ℝ) := by
      have hraw := rawCandidates_card_lower p c t
      norm_num at hraw
      exact hraw

/-- Uniform extraction form of the preceding PNT estimate. -/
theorem eventually_exists_rawCandidates_subset_uniform {c : ℝ}
    (hc : 0 < c) (hc1 : c < 1) :
    ∀ᶠ t : ℝ in atTop, ∀ (p C : ℕ),
      (C : ℝ) ≤ (((1 - c) * t / (16 * Real.log t)) ^ 4) / 24 →
      ∃ M ⊆ rawCandidates p c t, M.card = C := by
  filter_upwards [eventually_rawCandidates_card_lower_uniform hc hc1]
    with t ht
  intro p C hC
  apply Finset.exists_subset_card_eq
  exact_mod_cast hC.trans (ht p)

/-- In the strong elimination range the fourth-root scale eventually lies in
the (uniform-in-the-erased-prime) PNT regime. -/
theorem eventually_rawCandidates_subset_at_elimination_scale {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    ∀ᶠ x : ℕ in atTop, ∀ (q p C : ℕ), 0 < q →
      (q : ℝ) ≤ x * Real.log x ^ (-30 : ℝ) →
      (C : ℝ) ≤
        (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
            (16 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 →
      ∃ M ⊆ rawCandidates p (fourthRoot ξ)
          (fourthRoot ((x : ℝ) / q)), M.card = C := by
  have hc : 0 < fourthRoot ξ := fourthRoot_pos hξ
  have hc1 : fourthRoot ξ < 1 := fourthRoot_lt_one hξ1
  obtain ⟨T, hT⟩ := (eventually_atTop.1
    (eventually_exists_rawCandidates_subset_uniform hc hc1))
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
  exact hT _ htT p C hC

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
      (Erdos285.Lemma12.martinBlockBound x q : ℝ) ≤
        (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
            (16 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 := by
  let a : ℝ := (1 - fourthRoot ξ) / 16
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
      (Erdos285.Lemma12.fourthRoot_div_le_of_fifthRoot_le hq hrange.1)
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
    (Erdos285.Lemma12.martinBlockBound x q : ℝ) ≤
        200 * y ^ ((2 : ℝ) / 3) * L ^ 3 := by
      simpa [L, y] using Erdos285.Lemma12.martinBlockBound_cast_le
        (x := x) (q := q) hxNat
    _ ≤ a ^ 4 * y / (24 * L ^ 4) := hrealBound
    _ = (a * t / L) ^ 4 / 24 := by
      have heq : (a * t / L) ^ 4 / 24 =
          a ^ 4 * y / (24 * L ^ 4) := by
        rw [div_pow, mul_pow, ht4]
        ring
      exact heq.symm
    _ ≤ (a * t / Real.log t) ^ 4 / 24 := by gcongr
    _ = (((1 - fourthRoot ξ) * t / (16 * Real.log t)) ^ 4) / 24 := by
      dsimp [a]
      congr 2
      ring
    _ = (((1 - fourthRoot ξ) * fourthRoot ((x : ℝ) / q) /
          (16 * Real.log (fourthRoot ((x : ℝ) / q)))) ^ 4) / 24 := by
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
    Erdos285.Lemma12.InEliminationRange x q := by
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
        Erdos285.Lemma12.martinBlockBound x q ∧
      200 * (Real.log q / Real.log (Real.log q)) ^ (4 : ℕ) <
        Erdos285.Lemma12.martinBlockBound x q := by
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
      (Erdos285.Lemma12.martinBlockBound x q : ℝ) + 1 := by
    simpa only [A, L, y, Erdos285.Lemma12.martinBlockBound]
      using Nat.lt_floor_add_one A
  have hcardSource :
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) <
        Erdos285.Lemma12.martinBlockBound x q := by
    calc
      200 * (y ^ ((2 : ℝ) / 3) * lq ^ (3 : ℕ) /
          llq ^ ((8 : ℝ) / 3)) ≤ A / 2 := hsourceHalf
      _ ≤ A - 1 := by linarith
      _ < Erdos285.Lemma12.martinBlockBound x q := by linarith
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
      Erdos285.Lemma12.martinBlockBound x q := by
    exact hdispLe.trans_lt ((show A / 2 <
      (Erdos285.Lemma12.martinBlockBound x q : ℝ) by
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

/-- Fully assembled candidate-family interface for Lemma 12.  Besides the
structural properties of the four-prime products, this theorem applies
Martin's subset-sum lemma and hence supplies a bounded inverse subset sum for
every residue modulo the varying prime power. -/
theorem eventually_exists_martin_candidate_family {ξ : ℝ}
    (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    ∀ᶠ x : ℕ in atTop, ∀ (p ν : ℕ), p.Prime → 0 < ν →
      InStrongEliminationRange x (p ^ ν) →
      ∃ M : Finset ℕ,
        M.card = Erdos285.Lemma12.martinBlockBound x (p ^ ν) ∧
        M ⊆ rawCandidates p (fourthRoot ξ)
          (fourthRoot ((x : ℝ) / (p ^ ν : ℕ))) ∧
        fourthRoot ((x : ℝ) / (p ^ ν : ℕ)) ≤ (p ^ ν : ℕ) ∧
        (∀ m ∈ M,
          (m : ℝ) < (x : ℝ) / (p ^ ν : ℕ) ∧
          Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) m) ∧
        (Real.log (p ^ ν : ℕ) ^ ((3 : ℝ) / 2) /
            Real.log (Real.log (p ^ ν : ℕ)) ^ (2 : ℝ) <
              (x : ℝ) / (p ^ ν : ℕ)) ∧
        (200 * ((((x : ℝ) / (p ^ ν : ℕ)) ^ ((2 : ℝ) / 3)) *
              Real.log (p ^ ν : ℕ) ^ (3 : ℝ) /
            Real.log (Real.log (p ^ ν : ℕ)) ^ ((8 : ℝ) / 3)) <
              Erdos285.Lemma12.martinBlockBound x (p ^ ν)) ∧
        (200 * (Real.log (p ^ ν : ℕ) /
              Real.log (Real.log (p ^ ν : ℕ))) ^ (4 : ℕ) <
              Erdos285.Lemma12.martinBlockBound x (p ^ ν)) ∧
        ∀ residue : ZMod (p ^ ν), ∃ K : Finset ℕ,
          K ⊆ M ∧
          K.card ≤ Erdos285.Lemma12.martinBlockBound x (p ^ ν) ∧
          K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = residue := by
  have hExtract :=
    eventually_rawCandidates_subset_at_elimination_scale hξ hξ1
  have hCandidateBound :=
    eventually_martinBlockBound_le_candidateLower hξ hξ1
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
  have hQq : Q ≤ q := by
    exact_mod_cast (hrootQ.trans hrange.1)
  have hllq : 2 ≤ Real.log (Real.log (q : ℝ)) :=
    hQll q ((le_max_left Qll Qsubset).trans hQq)
  have hthreshold := fourPrime_subsetSum_and_dispersion_thresholds
    hq hlogX hllq hrange
  obtain ⟨M, hM, hMcard⟩ := hExtractX q p
    (Erdos285.Lemma12.martinBlockBound x q) hq hrange.2 (hBoundX q hq hrange)
  have htq : fourthRoot ((x : ℝ) / q) ≤ (q : ℝ) :=
    Erdos285.Lemma12.fourthRoot_div_le_of_fifthRoot_le hq hrange.1
  have hx : 0 < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := by linarith
    have hxR : (0 : ℝ) < x := by
      have hxone : 1 < (x : ℝ) :=
        (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hlogpos
      linarith
    exact_mod_cast hxR
  have hMsource : ∀ m ∈ M,
      (m : ℝ) < (x : ℝ) / q ∧
        Erdos285.Dispersion.IsKPrimeProductAway 4 q m := by
    intro m hm
    exact ⟨rawCandidate_lt_eliminationScale hx hp (hM hm),
      rawCandidate_isKPrimeProductAway (ν := ν) hp (hM hm)⟩
  have hBpos : 0 < (x : ℝ) / q := by positivity
  have hsurj := hQsubset q
    ((le_max_right Qll Qsubset).trans hQq)
    (Erdos285.Lemma12.martinBlockBound x q)
    ((x : ℝ) / q) M (by simp [hMcard]) hBpos
    (by
      convert hthreshold.1 using 1 <;> norm_num [Real.rpow_natCast])
    (by
      rw [hMcard]
      convert hthreshold.2.1 using 1 <;> norm_num [Real.rpow_natCast])
    hMsource
  refine ⟨M, hMcard, hM, ?_, hMsource, ?_, ?_, ?_, hsurj⟩
  · simpa [q] using htq
  · simpa [q] using hthreshold.1
  · simpa [q] using hthreshold.2.1
  · simpa [q] using hthreshold.2.2

/-- A version uniform in the interval parameter.  The proof constructs the
family in the fixed narrower prime band belonging to `ξ = 9/10`; monotonicity
of the bands then embeds it in the candidate family for every `0 < ξ ≤ 9/10`.
This is the form needed when Proposition 6 lets `ξ` vary with `x`. -/
theorem eventually_exists_martin_candidate_family_uniform :
    ∀ᶠ x : ℕ in atTop, ∀ (ξ : ℝ), 0 < ξ → ξ ≤ (9 : ℝ) / 10 →
      ∀ (p ν : ℕ), p.Prime → 0 < ν →
      InStrongEliminationRange x (p ^ ν) →
      ∃ M : Finset ℕ,
        M.card = Erdos285.Lemma12.martinBlockBound x (p ^ ν) ∧
        M ⊆ rawCandidates p (fourthRoot ξ)
          (fourthRoot ((x : ℝ) / (p ^ ν : ℕ))) ∧
        fourthRoot ((x : ℝ) / (p ^ ν : ℕ)) ≤ (p ^ ν : ℕ) ∧
        (∀ m ∈ M,
          (m : ℝ) < (x : ℝ) / (p ^ ν : ℕ) ∧
          Erdos285.Dispersion.IsKPrimeProductAway 4 (p ^ ν) m) ∧
        (Real.log (p ^ ν : ℕ) ^ ((3 : ℝ) / 2) /
            Real.log (Real.log (p ^ ν : ℕ)) ^ (2 : ℝ) <
              (x : ℝ) / (p ^ ν : ℕ)) ∧
        (200 * ((((x : ℝ) / (p ^ ν : ℕ)) ^ ((2 : ℝ) / 3)) *
              Real.log (p ^ ν : ℕ) ^ (3 : ℝ) /
            Real.log (Real.log (p ^ ν : ℕ)) ^ ((8 : ℝ) / 3)) <
              Erdos285.Lemma12.martinBlockBound x (p ^ ν)) ∧
        (200 * (Real.log (p ^ ν : ℕ) /
              Real.log (Real.log (p ^ ν : ℕ))) ^ (4 : ℕ) <
              Erdos285.Lemma12.martinBlockBound x (p ^ ν)) ∧
        ∀ residue : ZMod (p ^ ν), ∃ K : Finset ℕ,
          K ⊆ M ∧
          K.card ≤ Erdos285.Lemma12.martinBlockBound x (p ^ ν) ∧
          K.sum (fun m ↦ ((m : ZMod (p ^ ν))⁻¹)) = residue := by
  have hfixed := eventually_exists_martin_candidate_family
    (ξ := (9 : ℝ) / 10) (by norm_num) (by norm_num)
  filter_upwards [hfixed] with x hx
  intro ξ hξ hξupper p ν hp hν hrange
  obtain ⟨M, hcard, hM, htq, hsource, hBsource, hcardSource,
    hdispersion, hsurj⟩ := hx p ν hp hν hrange
  have hc : fourthRoot ξ ≤ fourthRoot ((9 : ℝ) / 10) :=
    fourthRoot_mono hξupper
  have ht : 0 ≤ fourthRoot ((x : ℝ) / (p ^ ν : ℕ)) :=
    fourthRoot_nonneg _
  refine ⟨M, hcard, hM.trans ?_, htq, hsource, hBsource, hcardSource,
    hdispersion, hsurj⟩
  exact rawCandidates_mono_lowerEndpoint hc ht

/-- The unconditional provider consumed by the descending Proposition 6
recursion.  The prime-power representation of `q` is extracted internally;
the only residual-dependent input is the elementary bound on prime powers in
the old denominator cofactor. -/
theorem eventually_exists_candidateData_and_surjective_uniform :
    ∀ᶠ x : ℕ in atTop, ∀ (ξ : ℝ), 0 < ξ → ξ ≤ (9 : ℝ) / 10 →
      ∀ (q : ℕ) (r : ℚ), IsPrimePow q →
      InStrongEliminationRange x q →
      q ∈ Erdos285.PrimePowers.primePowerParts r.den →
      (∀ ℓ : ℕ, IsPrimePow ℓ → ℓ ∣ r.den / q → ℓ < q) →
      ∃ M : Finset ℕ,
        Erdos285.Lemma12.CandidateData ξ x q r M ∧
        Erdos285.Lemma12.BoundedInverseSubsetSurjective q
          (Erdos285.Lemma12.martinBlockBound x q) M := by
  have hfamilies := eventually_exists_martin_candidate_family_uniform
  have hlogTop : Tendsto (fun x : ℕ ↦ Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hfamilies, hlogTop.eventually_ge_atTop 2]
      with x hfamily hlog
  intro ξ hξ hξupper q r hqpp hrange hqpart hcofactor
  obtain ⟨p, ν, hp, hν, rfl⟩ := (isPrimePow_nat_iff q).mp hqpp
  obtain ⟨M, hcard, hM, -, -, -, -, -, hsurj⟩ :=
    hfamily ξ hξ hξupper p ν hp hν hrange
  have hx : 0 < x := by
    have hlogpos : 0 < Real.log (x : ℝ) := by linarith
    have hxR : (0 : ℝ) < x := by
      have hxone : 1 < (x : ℝ) :=
        (Real.log_pos_iff (by positivity : (0 : ℝ) ≤ x)).mp hlogpos
      linarith
    exact_mod_cast hxR
  have hweak : Erdos285.Lemma12.InEliminationRange x (p ^ ν) :=
    strongRange_to_eliminationRange (by linarith) hrange
  refine ⟨M, ?_, ?_⟩
  · exact Erdos285.Lemma12.candidateData_of_rawCandidateFamily
      hξ (hξupper.trans_lt (by norm_num)) hx hp hν hweak hqpart hM hcofactor
  · exact hsurj

end

end Erdos285.Lemma12Numerics

#print axioms Erdos285.Lemma12Numerics.eventually_exists_martin_candidate_family
#print axioms Erdos285.Lemma12Numerics.eventually_exists_martin_candidate_family_uniform
#print axioms Erdos285.Lemma12Numerics.eventually_exists_candidateData_and_surjective_uniform
