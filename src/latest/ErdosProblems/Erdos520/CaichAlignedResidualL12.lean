import ErdosProblems.Erdos520.CaichAlignedResidualTail
import ErdosProblems.Erdos520.CaichResidualFirstMomentBounds
import ErdosProblems.Erdos520.CaichAlignedScheduledMainPNTSpecialization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology Interval

namespace Erdos
namespace Problem520

/-!
# Unconditional Rankin bound for the aligned long-ratio residual

The `L12` residual only contains blocks for which the test point is
logarithmically very far from the left endpoint.  On those blocks the
unconditional Chebyshev--Rankin smooth-number estimate gives a saving far
larger than the smoothing parameter, the number of blocks, and the finite
test entropy.
-/

/-- Rounding loses at most a factor two once the quotient is at least two. -/
theorem log_natFloor_natDiv_lower
    {x b : ℕ} {t : ℝ} (hb : 0 < b) (ht : 0 < t)
    (htb : t ≤ (b : ℝ)) (hxb : 2 * b ≤ x) :
    Real.log (x : ℝ) - Real.log (2 * b : ℕ) ≤
      Real.log (Nat.floor ((x : ℝ) / t) : ℝ) := by
  let z := Nat.floor ((x : ℝ) / t)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hxR : (0 : ℝ) < x := by
    exact_mod_cast (show 0 < x by omega)
  have hquotTwo : (2 : ℝ) ≤ (x : ℝ) / t := by
    rw [le_div_iff₀ ht]
    have htb' : 2 * t ≤ 2 * (b : ℝ) := by linarith
    have hxb' : (2 : ℝ) * b ≤ x := by exact_mod_cast hxb
    linarith
  have hzpos : 0 < z := by
    rw [Nat.floor_pos]
    linarith
  have hquotLt : (x : ℝ) / t < (z : ℝ) + 1 := by
    simpa only [z] using! Nat.lt_floor_add_one ((x : ℝ) / t)
  have hone : (z : ℝ) + 1 ≤ 2 * z := by
    have hzOne : (1 : ℝ) ≤ z := by exact_mod_cast hzpos
    linarith
  have hquotLe : (x : ℝ) / t ≤ 2 * z := (le_of_lt hquotLt).trans hone
  have hxt : (x : ℝ) / (2 * t) ≤ (z : ℝ) := by
    calc
      (x : ℝ) / (2 * t) = ((x : ℝ) / t) / 2 := by ring
      _ ≤ (2 * (z : ℝ)) / 2 := by gcongr
      _ = (z : ℝ) := by ring
  have hleft : (x : ℝ) / (2 * b) ≤ (x : ℝ) / (2 * t) := by
    exact div_le_div_of_nonneg_left hxR.le (by positivity) (by linarith)
  have hratio : (x : ℝ) / (2 * b) ≤ (z : ℝ) := hleft.trans hxt
  have hratioPos : (0 : ℝ) < (x : ℝ) / (2 * b) := by positivity
  have hlog := Real.log_le_log hratioPos hratio
  rw [Real.log_div hxR.ne' (by positivity : (2 * (b : ℝ)) ≠ 0)] at hlog
  norm_cast at hlog ⊢

/-- A block excluded by the literal near predicate has an enormous Rankin
saving even after one aligned step and the loss from taking a floor. -/
theorem alignedFar_floor_rankin_saving
    {K L x j : ℕ} (hK : 1 ≤ K) (hL : 5 ≤ L)
    (hfar : ¬ caichAlignedNearRatio K L x j)
    {t : ℝ} (ht : t ∈ Ioc
      (alignedThinEndpoint K L j : ℝ)
      (alignedThinEndpoint K L (j + 1) : ℝ)) :
    let z := Nat.floor ((x : ℝ) / t)
    2 * alignedThinEndpoint K L (j + 1) ≤ x ∧
      0 < z ∧
      (L : ℝ) ^ (50 * K) *
          (alignedThinExponent K L (j + 1) : ℝ) ≤
        Real.log (z : ℝ) := by
  let a := alignedThinEndpoint K L j
  let b := alignedThinEndpoint K L (j + 1)
  let E := alignedThinExponent K L (j + 1)
  let U : ℝ := (L : ℝ) ^ (50 * K)
  let Q : ℝ := (L : ℝ) ^ (100 * K)
  let z := Nat.floor ((x : ℝ) / t)
  have ha : 2 ≤ a := by
    dsimp only [a]
    exact two_le_alignedThinEndpoint K L j
  have hb : 2 ≤ b := by
    dsimp only [b]
    exact two_le_alignedThinEndpoint K L (j + 1)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogb : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hstep : Real.log (b : ℝ) ≤
      (3 / 2 : ℝ) * Real.log (a : ℝ) := by
    dsimp only [a, b]
    exact log_alignedThinEndpoint_succ_le_three_halves hK (by omega)
  have hfar' : Q < Real.log (x : ℝ) / Real.log (a : ℝ) := by
    simpa only [caichAlignedNearRatio, a, Q, not_le] using! hfar
  have hlogx : Q * Real.log (a : ℝ) < Real.log (x : ℝ) :=
    (lt_div_iff₀ hloga).mp hfar'
  have hLcast : (5 : ℝ) ≤ L := by exact_mod_cast hL
  have hexpPos : 0 < 50 * K := by omega
  have hLU : (L : ℝ) ≤ U := by
    dsimp only [U]
    exact le_self_pow₀ (by linarith) (by omega)
  have hUfive : (5 : ℝ) ≤ U := hLcast.trans hLU
  have hQU : Q = U ^ 2 := by
    dsimp only [Q, U]
    rw [show 100 * K = (50 * K) * 2 by omega, pow_mul]
  have hcoef : 3 * U + 5 / 2 ≤ Q := by
    rw [hQU]
    nlinarith
  have hlogTwoLe : Real.log (2 : ℝ) ≤ Real.log (a : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast ha)
  have hlogbE : Real.log (b : ℝ) = (E : ℝ) * Real.log 2 := by
    dsimp only [b, E]
    exact log_alignedThinEndpoint K L (j + 1)
  have hE : (E : ℝ) ≤ 2 * Real.log (b : ℝ) := by
    have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
      exact (by norm_num : (1 / 2 : ℝ) ≤ 0.6931471803).trans
        Real.log_two_gt_d9.le
    have hEnonneg : (0 : ℝ) ≤ E := by positivity
    rw [hlogbE]
    nlinarith
  have hUE : U * (E : ℝ) ≤ 3 * U * Real.log (a : ℝ) := by
    have hUnonneg : 0 ≤ U := by dsimp [U]; positivity
    have := mul_le_mul_of_nonneg_left hE hUnonneg
    nlinarith
  have hlogTwoB : Real.log (2 * b : ℕ) ≤
      (5 / 2 : ℝ) * Real.log (a : ℝ) := by
    rw [show ((2 * b : ℕ) : ℝ) = (2 : ℝ) * b by norm_cast,
      Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hsum : U * (E : ℝ) + Real.log (2 * b : ℕ) ≤
      Q * Real.log (a : ℝ) := by
    calc
      U * (E : ℝ) + Real.log (2 * b : ℕ) ≤
          (3 * U + 5 / 2) * Real.log (a : ℝ) := by
        nlinarith
      _ ≤ Q * Real.log (a : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef hloga.le
  have hlogTwoBLt : Real.log (2 * b : ℕ) < Real.log (x : ℝ) :=
    lt_of_le_of_lt (by nlinarith [show 0 ≤ U * (E : ℝ) by positivity])
      hlogx
  have hxb : 2 * b ≤ x := by
    by_contra hnot
    have hxle : x < 2 * b := Nat.lt_of_not_ge hnot
    have hxpos : (0 : ℝ) < x := by
      have hxnat : 0 < x := by
        by_contra hx0
        have hxzero : x = 0 := Nat.eq_zero_of_not_pos hx0
        subst x
        have hlogTwoBpos : 0 < Real.log (2 * b : ℕ) :=
          Real.log_pos (by exact_mod_cast (show 1 < 2 * b by omega))
        have hlogTwoBpos' : 0 < Real.log (2 * (b : ℝ)) := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using! hlogTwoBpos
        norm_num at hlogTwoBLt
        linarith
      exact_mod_cast hxnat
    have hlogle : Real.log (x : ℝ) ≤ Real.log (2 * b : ℕ) :=
      Real.log_le_log hxpos (by exact_mod_cast hxle.le)
    linarith
  have htpos : 0 < t := by
    have haR : (0 : ℝ) < a := by positivity
    exact lt_trans haR ht.1
  have hzlog := log_natFloor_natDiv_lower
    (x := x) (b := b) (t := t) (by omega) htpos
    (by simpa only [b] using! ht.2) hxb
  have hzpos : 0 < z := by
    rw [Nat.floor_pos]
    have htwo : (2 : ℝ) ≤ (x : ℝ) / t := by
      rw [le_div_iff₀ htpos]
      have htb : t ≤ (b : ℝ) := by simpa only [b] using! ht.2
      have hxbR : (2 : ℝ) * b ≤ x := by exact_mod_cast hxb
      nlinarith
    linarith
  refine ⟨by simpa only [b] using! hxb, hzpos, ?_⟩
  have : U * (E : ℝ) ≤
      Real.log (x : ℝ) - Real.log (2 * b : ℕ) := by
    linarith
  exact this.trans (by simpa only [z] using! hzlog)

/-- Uniformly over the whole aligned block range, the logarithmic Euler
factor in Rankin's estimate is negligible compared with `L^(50K)`. -/
theorem eventually_alignedResidualRankinEulerGeometry
    {C : ℝ} {N K : ℕ} (hC : 0 ≤ C) (hN : 2 ≤ N) (hK : 1 ≤ K) :
    ∀ᶠ L : ℕ in atTop, ∀ j : ℕ,
      j + 1 ≤ alignedThinBlockCount K L →
        N ≤ alignedThinExponent K L (j + 1) ∧
          smoothRankinScheduleExponent C N
              (alignedThinExponent K L (j + 1)) ≤
            (L : ℝ) ^ (50 * K) / 4 := by
  let D := smoothRankinLogConstant C N
  have hD : 0 < D := smoothRankinLogConstant_pos hC hN
  have hpowPos : 0 < 49 * K := by omega
  have ht : Tendsto (fun L : ℕ ↦ (L : ℝ) ^ (49 * K)) atTop atTop :=
    (Filter.tendsto_pow_atTop (show 49 * K ≠ 0 by omega)).comp
      tendsto_natCast_atTop_atTop
  have hlargePow : ∀ᶠ L : ℕ in atTop,
      16 * D ≤ (L : ℝ) ^ (49 * K) :=
    ht.eventually (eventually_ge_atTop (16 * D))
  filter_upwards [eventually_le_alignedThinInitialExponent hK N,
      hlargePow, eventually_ge_atTop (5 : ℕ)] with L hNinitial hpow hL
  intro j hj
  let E0 := alignedThinExponent K L 0
  let E := alignedThinExponent K L (j + 1)
  have hE0E : E0 ≤ E := by
    dsimp only [E0, E]
    exact alignedThinExponent_mono K L (Nat.zero_le _)
  have hNE : N ≤ E := hNinitial.trans hE0E
  refine ⟨hNE, ?_⟩
  have hdiff := alignedThinEndpoint_logLog_diff_zero_le
    (K := K) (ell := L) (j := j + 1) hK (by omega : 4 ≤ L)
  have hE0pos : 0 < E0 := by
    dsimp only [E0]
    exact alignedThinExponent_pos K L 0
  have hEpos : 0 < E := by
    dsimp only [E]
    exact alignedThinExponent_pos K L (j + 1)
  have hdiffE : Real.log (E : ℝ) - Real.log (E0 : ℝ) ≤
      ((j + 1 : ℕ) : ℝ) * (2 / (L : ℝ)) := by
    rw [alignedThinEndpoint, alignedThinEndpoint,
      logLogNat_two_pow_eq hEpos, logLogNat_two_pow_eq hE0pos] at hdiff
    dsimp only [E, E0]
    linarith
  have hLpos : (0 : ℝ) < L := by positivity
  have hjcast : ((j + 1 : ℕ) : ℝ) ≤
      (alignedThinBlockCount K L : ℝ) := by exact_mod_cast hj
  have hwidth : ((j + 1 : ℕ) : ℝ) * (2 / (L : ℝ)) ≤
      2 * (L : ℝ) ^ K := by
    calc
      ((j + 1 : ℕ) : ℝ) * (2 / (L : ℝ)) ≤
          (alignedThinBlockCount K L : ℝ) * (2 / (L : ℝ)) := by
        gcongr
      _ = ((L : ℝ) ^ (K + 1)) * (2 / (L : ℝ)) := by
        rw [alignedThinBlockCount]
        norm_cast
      _ = 2 * (L : ℝ) ^ K := by
        rw [pow_succ]
        field_simp
  have hlogE0 : Real.log (E0 : ℝ) ≤ (L : ℝ) ^ K := by
    dsimp only [E0]
    rw [alignedThinExponent_zero, log_alignedOuterExponent]
    have hpowNat : (L - 2) ^ K ≤ L ^ K :=
      Nat.pow_le_pow_left (Nat.sub_le L 2) K
    have hpowCast : (((L - 2) ^ K : ℕ) : ℝ) ≤ (L ^ K : ℕ) := by
      exact_mod_cast hpowNat
    have hlogTwo : Real.log (2 : ℝ) ≤ 1 :=
      Real.log_two_lt_d9.le.trans (by norm_num)
    have hnonneg : (0 : ℝ) ≤ ((L - 2 : ℕ) : ℝ) ^ K := by positivity
    calc
      ((L - 2 : ℕ) : ℝ) ^ K * Real.log 2 ≤
          ((L - 2 : ℕ) : ℝ) ^ K * 1 :=
        mul_le_mul_of_nonneg_left hlogTwo hnonneg
      _ ≤ (L : ℝ) ^ K := by
        simp only [mul_one]
        exact_mod_cast hpowNat
  have hlogE : Real.log (E : ℝ) ≤ 3 * (L : ℝ) ^ K := by
    linarith [hdiffE.trans hwidth]
  have hpowOne : (1 : ℝ) ≤ (L : ℝ) ^ K := by
    exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ L by omega))
  have hlogTotal : 1 + Real.log (E : ℝ) ≤ 4 * (L : ℝ) ^ K := by
    linarith
  have heuler := smoothRankinScheduleExponent_le_log_bound hC hN hNE
  have hDnonneg : 0 ≤ D := hD.le
  have heuler' : smoothRankinScheduleExponent C N E ≤
      4 * D * (L : ℝ) ^ K := by
    calc
      smoothRankinScheduleExponent C N E ≤
          D * (1 + Real.log (E : ℝ)) := by
        simpa only [D] using! heuler
      _ ≤ D * (4 * (L : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_left hlogTotal hDnonneg
      _ = 4 * D * (L : ℝ) ^ K := by ring
  have hLK : 0 < (L : ℝ) ^ K := by positivity
  have habsorb : 4 * D * (L : ℝ) ^ K ≤
      (L : ℝ) ^ (50 * K) / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hpow hLK.le
    rw [show 50 * K = 49 * K + K by omega, pow_add]
    nlinarith
  exact heuler'.trans habsorb

theorem caichTimeWindowReciprocalMass_le_freshReciprocalSum
    (X : ℝ) (a b : ℕ) (t : ℝ) :
    caichTimeWindowReciprocalMass X a b t ≤ freshReciprocalSum a b := by
  classical
  unfold caichTimeWindowReciprocalMass freshReciprocalSum
  apply Finset.sum_le_sum
  intro p hp
  split_ifs <;> simp <;> positivity

theorem alignedThinEndpoint_lt_succ
    {K L j : ℕ} (hL : 0 < L) :
    alignedThinEndpoint K L j < alignedThinEndpoint K L (j + 1) := by
  have hE : 0 < alignedThinExponent K L j :=
    alignedThinExponent_pos K L j
  have hceil : 0 < alignedThinExponent K L j ⌈/⌉ L := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    apply Nat.div_pos
    · omega
    · omega
  apply Nat.pow_lt_pow_right (by norm_num)
  change alignedThinExponent K L j <
    ceilThinStep L (alignedThinExponent K L j)
  unfold ceilThinStep
  omega

theorem two_mul_alignedThinEndpoint_succ_le_of_far
    {K L x j : ℕ} (hK : 1 ≤ K) (hL : 5 ≤ L)
    (hfar : ¬ caichAlignedNearRatio K L x j) :
    2 * alignedThinEndpoint K L (j + 1) ≤ x := by
  have ht : (alignedThinEndpoint K L (j + 1) : ℝ) ∈ Ioc
      (alignedThinEndpoint K L j : ℝ)
      (alignedThinEndpoint K L (j + 1) : ℝ) := by
    constructor
    · exact_mod_cast alignedThinEndpoint_lt_succ (K := K) (L := L)
        (j := j) (by omega)
    · exact le_rfl
  exact (alignedFar_floor_rankin_saving hK hL hfar ht).1

theorem freshReciprocalSum_alignedThin_le_four_mul_div
    {C : ℝ} {N K L j : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hK : 1 ≤ K) (hL : 5 ≤ L)
    (hNE : N ≤ alignedThinExponent K L j) :
    freshReciprocalSum (alignedThinEndpoint K L j)
        (alignedThinEndpoint K L (j + 1)) ≤
      4 * C / (L : ℝ) := by
  let a := alignedThinEndpoint K L j
  let b := alignedThinEndpoint K L (j + 1)
  have hNa : N ≤ a := by
    dsimp only [a, alignedThinEndpoint]
    exact hNE.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n :=
      alignedThinExponent K L j)))
  have ha : 2 ≤ a := by
    dsimp only [a]
    exact two_le_alignedThinEndpoint K L j
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact alignedThinEndpoint_mono K L (Nat.le_succ j)
  have hraw := freshReciprocalSum_le_of_primeCountingUpperBound
    hC hP hNa ha hab
  have hwidth := alignedThinEndpoint_logLog_width
    (K := K) (ell := L) (j := j) hK (by omega : 4 ≤ L)
  have hlarge : (L : ℝ) ≤ Real.log (a : ℝ) := by
    dsimp only [a]
    exact scale_le_log_alignedThinEndpoint hK hL
  have hLpos : (0 : ℝ) < L := by positivity
  calc
    freshReciprocalSum a b ≤
        C * (logLogNat b - logLogNat a) +
          2 * C / Real.log (a : ℝ) := hraw
    _ ≤ C * (2 / (L : ℝ)) + 2 * C / (L : ℝ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (by simpa only [a, b] using! hwidth) hC
      · exact div_le_div_of_nonneg_left (by positivity) hLpos hlarge
    _ = 4 * C / (L : ℝ) := by ring

/-- Pointwise first-moment kernel bound on one far aligned block. -/
theorem caichAlignedFarCoreTimeFirstMomentKernel_le
    {C X : ℝ} {N K L x j : ℕ}
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hK : 1 ≤ K) (hL : 5 ≤ L)
    (hEN : N ≤ alignedThinExponent K L (j + 1))
    (heuler : smoothRankinScheduleExponent C N
        (alignedThinExponent K L (j + 1)) ≤
      (L : ℝ) ^ (50 * K) / 4)
    (hfar : ¬ caichAlignedNearRatio K L x j)
    {t : ℝ} (ht : t ∈ Ioc
      (alignedThinEndpoint K L j : ℝ)
      (alignedThinEndpoint K L (j + 1) : ℝ)) :
    caichCoreTimeFirstMomentKernel X x
        (alignedThinEndpoint K L j)
        (alignedThinEndpoint K L (j + 1)) t ≤
      ((x : ℝ) / t) *
          Real.exp (-3 * (L : ℝ) ^ (50 * K) / 4) *
        freshReciprocalSum
          (alignedThinEndpoint K L j)
          (alignedThinEndpoint K L (j + 1)) := by
  let a := alignedThinEndpoint K L j
  let b := alignedThinEndpoint K L (j + 1)
  let E := alignedThinExponent K L (j + 1)
  let U : ℝ := (L : ℝ) ^ (50 * K)
  let z := Nat.floor ((x : ℝ) / t)
  have hgeom := alignedFar_floor_rankin_saving hK hL hfar ht
  have hz : 0 < z := by simpa only [z] using! hgeom.2.1
  have hsaving : U * (E : ℝ) ≤ Real.log (z : ℝ) := by
    simpa only [U, E, z] using! hgeom.2.2
  have hcardPower := card_smoothNumbersUpTo_two_pow_succ_le_exp_decay
    hC hP hN (by simpa only [E] using! hEN) hz hsaving
      (by simpa only [U, E] using! heuler)
  have htpos : 0 < t := by
    have ha : (0 : ℝ) < alignedThinEndpoint K L j := by
      exact_mod_cast (show 0 < alignedThinEndpoint K L j by
        exact Nat.zero_lt_of_lt (two_le_alignedThinEndpoint K L j))
    exact lt_trans ha ht.1
  have hzle : (z : ℝ) ≤ (x : ℝ) / t := by
    simpa only [z] using! Nat.floor_le (by positivity : 0 ≤ (x : ℝ) / t)
  have hcardActual : ∀ p ∈ freshPrimes a b,
      t / (1 + 1 / X) < (p : ℝ) ∧ (p : ℝ) ≤ t →
        ((Nat.smoothNumbersUpTo z p).card : ℝ) ≤
          ((x : ℝ) / t) * Real.exp (-3 * U / 4) := by
    intro p hp hwindow
    have hpB : p ≤ b := (mem_freshPrimes.mp hp).2.2
    have hpCut : p ≤ 2 ^ E + 1 := by
      dsimp only [b, E] at hpB ⊢
      unfold alignedThinEndpoint at hpB
      omega
    calc
      ((Nat.smoothNumbersUpTo z p).card : ℝ) ≤
          (Nat.smoothNumbersUpTo z (2 ^ E + 1)).card := by
        exact_mod_cast card_smoothNumbersUpTo_mono_smoothness z hpCut
      _ ≤ (z : ℝ) * Real.exp (-3 * U / 4) := by
        simpa only [E, U] using! hcardPower
      _ ≤ ((x : ℝ) / t) * Real.exp (-3 * U / 4) :=
        mul_le_mul_of_nonneg_right hzle (Real.exp_pos _).le
  have hkernel := caichCoreTimeFirstMomentKernel_le_mul_timeWindowMass
    (X := X) (t := t)
    (Z := ((x : ℝ) / t) * Real.exp (-3 * U / 4))
    (x := x) (a := a) (b := b) (by positivity) hcardActual
  have hmass := caichTimeWindowReciprocalMass_le_freshReciprocalSum X a b t
  have hZnonneg : 0 ≤ ((x : ℝ) / t) * Real.exp (-3 * U / 4) := by
    positivity
  calc
    caichCoreTimeFirstMomentKernel X x a b t ≤
        (((x : ℝ) / t) * Real.exp (-3 * U / 4)) *
          caichTimeWindowReciprocalMass X a b t := hkernel
    _ ≤ (((x : ℝ) / t) * Real.exp (-3 * U / 4)) *
          freshReciprocalSum a b :=
      mul_le_mul_of_nonneg_left hmass hZnonneg
    _ = ((x : ℝ) / t) * Real.exp (-3 * U / 4) *
          freshReciprocalSum a b := rfl

/-- First moment of one far core block after inserting both Rankin decay
and the unconditional Chebyshev reciprocal-prime estimate. -/
theorem caichAlignedFarCoreAveragedBlockFirstMoment_le
    {C X : ℝ} {N K L x j : ℕ}
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    (hK : 1 ≤ K) (hL : 5 ≤ L)
    (hENleft : N ≤ alignedThinExponent K L j)
    (hENright : N ≤ alignedThinExponent K L (j + 1))
    (heuler : smoothRankinScheduleExponent C N
        (alignedThinExponent K L (j + 1)) ≤
      (L : ℝ) ^ (50 * K) / 4)
    (hX : 0 ≤ X)
    (hfar : ¬ caichAlignedNearRatio K L x j) :
    caichCoreAveragedBlockFirstMoment X x
        (alignedThinEndpoint K L j)
        (alignedThinEndpoint K L (j + 1)) ≤
      X * ((x : ℝ) * Real.exp (-3 * (L : ℝ) ^ (50 * K) / 4) *
          (4 * C / (L : ℝ))) *
        Real.log
          ((alignedThinEndpoint K L (j + 1) : ℝ) /
            (alignedThinEndpoint K L j : ℝ)) := by
  let a := alignedThinEndpoint K L j
  let b := alignedThinEndpoint K L (j + 1)
  let U : ℝ := (L : ℝ) ^ (50 * K)
  have ha : 1 ≤ a := by
    dsimp only [a]
    exact (by norm_num : 1 ≤ 2).trans (two_le_alignedThinEndpoint K L j)
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact alignedThinEndpoint_mono K L (Nat.le_succ j)
  have hrecip := freshReciprocalSum_alignedThin_le_four_mul_div
    hC hP hK hL hENleft
  have hpoint : ∀ t ∈ Ioc (a : ℝ) (b : ℝ),
      caichCoreTimeFirstMomentKernel X x a b t ≤
        ((x : ℝ) * Real.exp (-3 * U / 4) * (4 * C / (L : ℝ))) / t := by
    intro t ht
    have hraw := caichAlignedFarCoreTimeFirstMomentKernel_le
      (X := X) hC hP hN hK hL hENright heuler hfar
      (by simpa only [a, b] using! ht)
    have hxt : 0 ≤ (x : ℝ) / t := by
      have htpos : 0 < t := by
        have haR : (0 : ℝ) < a := by positivity
        exact lt_trans haR ht.1
      positivity
    calc
      caichCoreTimeFirstMomentKernel X x a b t ≤
          ((x : ℝ) / t) * Real.exp (-3 * U / 4) *
            freshReciprocalSum a b := by
        simpa only [a, b, U] using! hraw
      _ ≤ ((x : ℝ) / t) * Real.exp (-3 * U / 4) *
            (4 * C / (L : ℝ)) := by
        gcongr
      _ = ((x : ℝ) * Real.exp (-3 * U / 4) *
            (4 * C / (L : ℝ))) / t := by ring
  simpa only [a, b, U] using!
    (caichCoreAveragedBlockFirstMoment_le_mul_log hX
      (by positivity) ha hab hpoint)

/-- Aggregate first-moment bound for the literal far-block scheduled sum. -/
theorem caichAlignedFarScheduledL12FirstMoment_le
    {C X : ℝ} {N0 K L x NB : ℕ}
    [DecidablePred (caichAlignedNearRatio K L x)]
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N0) (hN0 : 2 ≤ N0)
    (hK : 1 ≤ K) (hL : 5 ≤ L) (hx : 2 ≤ x) (hX : 0 ≤ X)
    (hNB : NB ≤ alignedThinBlockCount K L)
    (hNinitial : N0 ≤ alignedThinExponent K L 0)
    (heuler : ∀ j : ℕ, j + 1 ≤ alignedThinBlockCount K L →
      smoothRankinScheduleExponent C N0
          (alignedThinExponent K L (j + 1)) ≤
        (L : ℝ) ^ (50 * K) / 4) :
    caichScheduledL12FirstMoment X x (Finset.range NB)
        (alignedThinEndpoint K L)
        (fun j ↦ alignedThinEndpoint K L (j + 1))
        (caichAlignedNearRatio K L x) ≤
      (alignedThinBlockCount K L : ℝ) * X *
        Real.exp (-3 * (L : ℝ) ^ (50 * K) / 4) *
        (4 * C / (L : ℝ)) * Real.log (x : ℝ) := by
  classical
  let blocks := (Finset.range NB).filter fun j ↦
    ¬ caichAlignedNearRatio K L x j
  let B : ℝ := X * ((x : ℝ) *
      Real.exp (-3 * (L : ℝ) ^ (50 * K) / 4) *
        (4 * C / (L : ℝ))) * Real.log (x : ℝ)
  have hxR : (0 : ℝ) < x := by positivity
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm : ∀ j ∈ blocks,
      caichCoreAveragedBlockFirstMoment X x
          (alignedThinEndpoint K L j)
          (alignedThinEndpoint K L (j + 1)) ≤ B := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    have hjNB : j < NB := Finset.mem_range.mp hj'.1
    have hjCount : j + 1 ≤ alignedThinBlockCount K L :=
      (Nat.lt_iff_add_one_le.mp hjNB).trans hNB
    have hNleft : N0 ≤ alignedThinExponent K L j :=
      hNinitial.trans (alignedThinExponent_mono K L (Nat.zero_le j))
    have hNright : N0 ≤ alignedThinExponent K L (j + 1) :=
      hNinitial.trans (alignedThinExponent_mono K L (Nat.zero_le (j + 1)))
    have hblock := caichAlignedFarCoreAveragedBlockFirstMoment_le
      hC hP hN0 hK hL hNleft hNright (heuler j hjCount) hX hj'.2
    have hfarRight := two_mul_alignedThinEndpoint_succ_le_of_far
      hK hL hj'.2
    have hbX : alignedThinEndpoint K L (j + 1) ≤ x := by omega
    have hlogb : Real.log (alignedThinEndpoint K L (j + 1) : ℝ) ≤
        Real.log (x : ℝ) := by
      apply Real.log_le_log (by
        exact_mod_cast (show 0 < alignedThinEndpoint K L (j + 1) by
          exact Nat.zero_lt_of_lt
            (two_le_alignedThinEndpoint K L (j + 1))))
      exact_mod_cast hbX
    have hloga : 0 ≤ Real.log (alignedThinEndpoint K L j : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast
        (show 1 ≤ alignedThinEndpoint K L j by
          exact (by norm_num : 1 ≤ 2).trans
            (two_le_alignedThinEndpoint K L j)))
    have hratio : Real.log
        ((alignedThinEndpoint K L (j + 1) : ℝ) /
          (alignedThinEndpoint K L j : ℝ)) ≤ Real.log (x : ℝ) := by
      rw [Real.log_div
        (by exact_mod_cast
          (show alignedThinEndpoint K L (j + 1) ≠ 0 by
            exact Nat.ne_of_gt (Nat.zero_lt_of_lt
              (two_le_alignedThinEndpoint K L (j + 1)))))
        (by exact_mod_cast
          (show alignedThinEndpoint K L j ≠ 0 by
            exact Nat.ne_of_gt (Nat.zero_lt_of_lt
              (two_le_alignedThinEndpoint K L j))))]
      linarith
    calc
      caichCoreAveragedBlockFirstMoment X x
          (alignedThinEndpoint K L j)
          (alignedThinEndpoint K L (j + 1)) ≤
        X * ((x : ℝ) *
            Real.exp (-3 * (L : ℝ) ^ (50 * K) / 4) *
              (4 * C / (L : ℝ))) *
          Real.log
            ((alignedThinEndpoint K L (j + 1) : ℝ) /
              (alignedThinEndpoint K L j : ℝ)) := hblock
      _ ≤ B := by
        dsimp only [B]
        gcongr
  have hcard : (blocks.card : ℝ) ≤
      (alignedThinBlockCount K L : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((Finset.card_range NB).le.trans hNB)
  unfold caichScheduledL12FirstMoment caichLongRatioFirstMoment
  change (∑ j ∈ blocks,
      caichCoreAveragedBlockFirstMoment X x
        (alignedThinEndpoint K L j)
        (alignedThinEndpoint K L (j + 1))) / (x : ℝ) ≤ _
  calc
    (∑ j ∈ blocks,
        caichCoreAveragedBlockFirstMoment X x
          (alignedThinEndpoint K L j)
          (alignedThinEndpoint K L (j + 1))) / (x : ℝ) ≤
        (∑ _j ∈ blocks, B) / (x : ℝ) := by
      gcongr with j hj
      exact hterm j hj
    _ = (blocks.card : ℝ) * B / (x : ℝ) := by simp
    _ ≤ (alignedThinBlockCount K L : ℝ) * B / (x : ℝ) := by
      gcongr
    _ = (alignedThinBlockCount K L : ℝ) * X *
        Real.exp (-3 * (L : ℝ) ^ (50 * K) / 4) *
        (4 * C / (L : ℝ)) * Real.log (x : ℝ) := by
      dsimp only [B]
      field_simp
      <;> ring

/-- Literal selected first moments satisfy the displayed Rankin-decay
majorant uniformly over every test point at all sufficiently large scales. -/
theorem eventually_selectedAlignedHarperL12FirstMoment_le_rankin
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      selectedAlignedHarperL12FirstMoment hK hHarper q m ell i ≤
        (alignedThinBlockCount K ell : ℝ) *
          caichWSmoothingParameterNatCast q
            (alignedRootExpTestPoint m i) *
          Real.exp (-3 * (ell : ℝ) ^ (50 * K) / 4) *
          (4 * C / (ell : ℝ)) *
          Real.log (alignedRootExpTestPoint m i : ℝ) := by
  classical
  let w := selectedClampedAlignedHarperBlockCertificate hK hHarper
  have hEuler := eventually_alignedResidualRankinEulerGeometry
    hC hN (by omega : 1 ≤ K)
  have hInitial := eventually_le_alignedThinInitialExponent
    (by omega : 1 ≤ K) N
  filter_upwards [hEuler, hInitial, eventually_ge_atTop w.clamp,
      eventually_ge_atTop (5 : ℕ)] with ell hEulerEll hInitialEll
      hclamp hell
  intro i hi
  let x := alignedRootExpTestPoint m i
  let NB := caichAlignedFirstReachingBlock K ell x
  have hscale : clampedAlignedScale w.clamp ell = ell :=
    clampedAlignedScale_eq_of_ge hclamp
  have hxUpper : x ≤ alignedOuterEndpoint K ell := by
    unfold alignedRootExpTests at hi
    rw [if_neg (by omega : ¬ell < 5)] at hi
    exact (Finset.mem_filter.mp hi).2.2
  have hNB : NB ≤ alignedThinBlockCount K ell := by
    dsimp only [NB]
    exact caichAlignedFirstReachingBlock_le_blockCount
      (by omega) hxUpper
  have hx : 2 ≤ x := by
    exact (two_le_alignedThinEndpoint K ell 0).trans
      (alignedThinInitial_lt_testPoint_of_mem hi).le
  have hraw := caichAlignedFarScheduledL12FirstMoment_le
    hC hP hN (by omega : 1 ≤ K) hell hx
    (caichWSmoothingParameterNatCast_pos q x).le hNB hInitialEll
    (fun j hj ↦ (hEulerEll j hj).2)
  have hendpoint : selectedAlignedHarperEndpoint hK hHarper ell =
      alignedThinEndpoint K ell := by
    funext j
    simp [selectedAlignedHarperEndpoint, w, hscale]
  have hblock : selectedAlignedHarperBlockCount hK hHarper m ell i = NB := by
    simp [selectedAlignedHarperBlockCount, w, hscale, NB, x]
  have hnear : selectedAlignedHarperNear hK hHarper m ell i =
      caichAlignedNearRatio K ell x := by
    funext j
    simp [selectedAlignedHarperNear, w, hscale, x]
  unfold selectedAlignedHarperL12FirstMoment
  simp only [hendpoint, hblock, hnear, x]
  exact hraw

theorem alignedRootExpTestPoint_log_le_exp_scale
    {K m ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    Real.log (alignedRootExpTestPoint m i : ℝ) ≤
      Real.exp ((ell : ℝ) ^ K) := by
  have hxUpper : alignedRootExpTestPoint m i ≤ alignedOuterEndpoint K ell := by
    unfold alignedRootExpTests at hi
    split at hi
    · simp at hi
    · exact (Finset.mem_filter.mp hi).2.2
  have hxpos : (0 : ℝ) < alignedRootExpTestPoint m i := by
    exact_mod_cast (show 0 < alignedRootExpTestPoint m i by
      exact Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi))
  have hxUpperR : (alignedRootExpTestPoint m i : ℝ) ≤
      (alignedOuterEndpoint K ell : ℝ) := by exact_mod_cast hxUpper
  have hlog := Real.log_le_log hxpos hxUpperR
  rw [log_alignedOuterEndpoint] at hlog
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hE : (alignedOuterExponent K ell : ℝ) ≤
      Real.exp ((ell : ℝ) ^ K) := by
    unfold alignedOuterExponent
    rw [show (((2 ^ ell ^ K : ℕ) : ℝ)) = (2 : ℝ) ^ (ell ^ K) by
      norm_cast]
    have hbase : (2 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    calc
      (2 : ℝ) ^ (ell ^ K) ≤ Real.exp 1 ^ (ell ^ K) :=
        pow_le_pow_left₀ (by norm_num) hbase _
      _ = Real.exp ((ell ^ K : ℕ) : ℝ) := by
        simpa using! (Real.exp_nat_mul 1 (ell ^ K)).symm
      _ = Real.exp ((ell : ℝ) ^ K) := by norm_cast
  have hEnonneg : (0 : ℝ) ≤ alignedOuterExponent K ell := by positivity
  calc
    Real.log (alignedRootExpTestPoint m i : ℝ) ≤
        (alignedOuterExponent K ell : ℝ) * Real.log 2 := hlog
    _ ≤ (alignedOuterExponent K ell : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlogTwo hEnonneg
    _ ≤ Real.exp ((ell : ℝ) ^ K) := by simpa using! hE

theorem selectedAlignedSmoothing_mul_log_le_exp
    {K m ell i q : ℕ} (hK : 1 ≤ K)
    (hi : i ∈ alignedRootExpTests K m ell) :
    caichWSmoothingParameterNatCast q (alignedRootExpTestPoint m i) *
        Real.log (alignedRootExpTestPoint m i : ℝ) ≤
      Real.exp (((caichWSmoothingExponent q + 1 : ℕ) : ℝ) *
        (ell : ℝ) ^ K) := by
  let x := alignedRootExpTestPoint m i
  let R := caichWSmoothingExponent q
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hlogInitial : (ell : ℝ) ≤
      Real.log (alignedThinEndpoint K ell 0 : ℝ) :=
    scale_le_log_alignedThinEndpoint hK hell
  have hinitialX : alignedThinEndpoint K ell 0 < x := by
    simpa only [x] using! alignedThinInitial_lt_testPoint_of_mem hi
  have hlogMono : Real.log (alignedThinEndpoint K ell 0 : ℝ) ≤
      Real.log (x : ℝ) := by
    apply Real.log_le_log (by
      exact_mod_cast (show 0 < alignedThinEndpoint K ell 0 by
        exact Nat.zero_lt_of_lt (two_le_alignedThinEndpoint K ell 0)))
    exact_mod_cast hinitialX.le
  have hlogOne : 1 ≤ Real.log (x : ℝ) := by
    have : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
    linarith
  have hX := caichWSmoothingParameterNat_cast_le
    (r := q) (x := x) hlogOne
  have hlogUpper := alignedRootExpTestPoint_log_le_exp_scale hi
  have hlogNonneg : 0 ≤ Real.log (x : ℝ) := zero_le_one.trans hlogOne
  have hpow : Real.log (x : ℝ) ^ R ≤
      Real.exp ((ell : ℝ) ^ K) ^ R :=
    pow_le_pow_left₀ hlogNonneg hlogUpper R
  calc
    caichWSmoothingParameterNatCast q x * Real.log (x : ℝ) ≤
        caichWSmoothingParameter q x * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_right
        (by simpa only [caichWSmoothingParameterNatCast] using! hX)
        hlogNonneg
    _ = Real.log (x : ℝ) ^ (R + 1) := by
      simp only [caichWSmoothingParameter, R, pow_succ]
    _ ≤ Real.exp ((ell : ℝ) ^ K) ^ (R + 1) :=
      pow_le_pow_left₀ hlogNonneg hlogUpper (R + 1)
    _ = Real.exp (((R + 1 : ℕ) : ℝ) * (ell : ℝ) ^ K) := by
      rw [← Real.exp_nat_mul]
    _ = Real.exp (((caichWSmoothingExponent q + 1 : ℕ) : ℝ) *
        (ell : ℝ) ^ K) := rfl

theorem selectedAlignedLargeSafeThreshold_inv_le_pow
    {K ell : ℕ} (hell : 5 ≤ ell) :
    1 / selectedAlignedLargeSafeThreshold K ell ≤ (ell : ℝ) ^ K := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hellPos : (0 : ℝ) < ell := by positivity
  have hhalf : (K : ℝ) / 2 ≤ (K : ℝ) := by
    have : (0 : ℝ) ≤ K := by positivity
    linarith
  have haux : caichAuxiliaryPower K ell ≤ (ell : ℝ) ^ K := by
    unfold caichAuxiliaryPower
    simpa only [Real.rpow_natCast] using!
      Real.rpow_le_rpow_of_exponent_le hellR hhalf
  unfold selectedAlignedLargeSafeThreshold caichLargeAuxThreshold
  rw [if_neg (by omega : ¬ell < 5)]
  unfold caichAuxiliaryPower at haux ⊢
  rw [one_div_div]
  calc
    (ell : ℝ) ^ ((K : ℝ) / 2) / (ell : ℝ) ^ 10 ≤
        (ell : ℝ) ^ ((K : ℝ) / 2) := by
      apply div_le_self (by positivity)
      exact one_le_pow₀ hellR
    _ ≤ (ell : ℝ) ^ K := haux

theorem eventually_const_mul_pow_le_exp_nat
    (A : ℝ) (d : ℕ) :
    ∀ᶠ ell : ℕ in atTop,
      A * (ell : ℝ) ^ d ≤ Real.exp (ell : ℝ) := by
  have ht : Tendsto
      (fun x : ℝ ↦ Real.exp (1 * x) / x ^ (d : ℝ)) atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop (d : ℝ) 1 (by norm_num)
  have htNat := ht.comp tendsto_natCast_atTop_atTop
  filter_upwards [htNat.eventually (eventually_ge_atTop A),
      eventually_ge_atTop (1 : ℕ)] with ell hell hellOne
  have hellPos : (0 : ℝ) < ell := by positivity
  have hden : 0 < (ell : ℝ) ^ d := by positivity
  change A ≤ Real.exp (1 * (ell : ℝ)) /
    (ell : ℝ) ^ (d : ℝ) at hell
  rw [Real.rpow_natCast] at hell
  rw [le_div_iff₀ hden] at hell
  simpa only [one_mul] using! hell

/-- After division by the original `L12` threshold, every selected point has
enough decay to pay twice the complete test entropy. -/
theorem eventually_selectedAlignedHarperSafeL12Moment_term_le_exp
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hP : PrimeCountingUpperBound C N) (hN : 2 ≤ N)
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      selectedAlignedHarperSafeL12Moment hK hHarper q m ell i /
          selectedAlignedLargeSafeThreshold K ell ≤
        Real.exp (-(2 * (2 * m + 2 : ℕ) : ℝ) * (ell : ℝ) ^ K) := by
  classical
  let R : ℕ := caichWSmoothingExponent q + 1
  let D : ℝ := (2 * m + 2 : ℕ)
  have hmoment := eventually_selectedAlignedHarperL12FirstMoment_le_rankin
    hC hP hN hK hHarper q m
  have hpoly := eventually_const_mul_pow_le_exp_nat (4 * C) (2 * K + 1)
  have hpowT : Tendsto (fun ell : ℕ ↦ (ell : ℝ) ^ (49 * K)) atTop atTop :=
    (Filter.tendsto_pow_atTop (show 49 * K ≠ 0 by omega)).comp
      tendsto_natCast_atTop_atTop
  have hDpow : ∀ᶠ ell : ℕ in atTop,
      8 * D ≤ (ell : ℝ) ^ (49 * K) :=
    hpowT.eventually (eventually_ge_atTop (8 * D))
  apply Filter.Eventually.mono
    (hmoment.and (hpoly.and (hDpow.and
      ((eventually_ge_atTop R).and (eventually_ge_atTop (8 : ℕ))))))
  intro ell h
  rcases h with ⟨hmomentEll, hpolyEll, hDpowEll, hRell, hell⟩
  intro i hi
  let T : ℝ := (ell : ℝ) ^ K
  let V : ℝ := (ell : ℝ) ^ (2 * K)
  let U : ℝ := (ell : ℝ) ^ (50 * K)
  have hellFive : 5 ≤ ell := by omega
  have hellOne : (1 : ℝ) ≤ ell := by exact_mod_cast (show 1 ≤ ell by omega)
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hUp : 0 < U := by dsimp [U]; positivity
  have hRleT : (R : ℝ) ≤ T := by
    have hRnat : R ≤ ell ^ K :=
      hRell.trans (le_self_pow₀ (by omega : 1 ≤ ell) (by omega : K ≠ 0))
    dsimp only [T]
    exact_mod_cast hRnat
  have hTV : T * T = V := by
    dsimp only [T, V]
    rw [← pow_add]
    congr 2
    omega
  have hRexp : Real.exp ((R : ℝ) * T) ≤ Real.exp V := by
    apply Real.exp_le_exp.mpr
    calc
      (R : ℝ) * T ≤ T * T := mul_le_mul_of_nonneg_right hRleT hTpos.le
      _ = V := hTV
  have hellV : (ell : ℝ) ≤ V := by
    have hnat : ell ≤ ell ^ (2 * K) :=
      le_self_pow₀ (by omega : 1 ≤ ell) (by omega : 2 * K ≠ 0)
    dsimp only [V]
    exact_mod_cast hnat
  have hpolyV : 4 * C * (ell : ℝ) ^ (2 * K + 1) ≤ Real.exp V :=
    hpolyEll.trans (Real.exp_le_exp.mpr hellV)
  have hthresholdInv := selectedAlignedLargeSafeThreshold_inv_le_pow
    (K := K) hellFive
  have hsmooth := selectedAlignedSmoothing_mul_log_le_exp
    (q := q) (by omega : 1 ≤ K) hi
  have hraw := hmomentEll i hi
  have hmomentNonneg : 0 ≤
      selectedAlignedHarperL12FirstMoment hK hHarper q m ell i :=
    caichScheduledL12FirstMoment_nonneg
      (caichWSmoothingParameterNatCast_pos q
        (alignedRootExpTestPoint m i)).le
      (Nat.zero_lt_of_lt (alignedThinInitial_lt_testPoint_of_mem hi))
      _ _ _ _
  have hthresholdPos := selectedAlignedLargeSafeThreshold_pos K ell
  have hrawBoundNonneg : 0 ≤
      (alignedThinBlockCount K ell : ℝ) *
          caichWSmoothingParameterNatCast q
            (alignedRootExpTestPoint m i) *
          Real.exp (-3 * (ell : ℝ) ^ (50 * K) / 4) *
          (4 * C / (ell : ℝ)) *
          Real.log (alignedRootExpTestPoint m i : ℝ) := by
    have hlog : 0 ≤ Real.log (alignedRootExpTestPoint m i : ℝ) := by
      exact (Real.log_pos (by exact_mod_cast
        (show 1 < alignedRootExpTestPoint m i by
          exact Nat.one_lt_two.trans_le
            ((two_le_alignedThinEndpoint K ell 0).trans
              (alignedThinInitial_lt_testPoint_of_mem hi).le)))).le
    have hXnonneg : 0 ≤ caichWSmoothingParameterNatCast q
        (alignedRootExpTestPoint m i) :=
      (caichWSmoothingParameterNatCast_pos q _).le
    have hratioNonneg : 0 ≤ 4 * C / (ell : ℝ) := by positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) hXnonneg)
          (Real.exp_pos _).le)
        hratioNonneg)
      hlog
  have hcoarse :
      selectedAlignedHarperSafeL12Moment hK hHarper q m ell i /
          selectedAlignedLargeSafeThreshold K ell ≤
        (4 * C * (ell : ℝ) ^ (2 * K + 1)) *
          Real.exp ((R : ℝ) * T) * Real.exp (-3 * U / 4) := by
    rw [selectedAlignedHarperSafeL12Moment, if_pos hi]
    rw [div_eq_mul_inv]
    exact (calc
      selectedAlignedHarperL12FirstMoment hK hHarper q m ell i *
          (selectedAlignedLargeSafeThreshold K ell)⁻¹ ≤
        ((alignedThinBlockCount K ell : ℝ) *
          caichWSmoothingParameterNatCast q
            (alignedRootExpTestPoint m i) *
          Real.exp (-3 * (ell : ℝ) ^ (50 * K) / 4) *
          (4 * C / (ell : ℝ)) *
          Real.log (alignedRootExpTestPoint m i : ℝ)) *
            (ell : ℝ) ^ K := by
        exact mul_le_mul hraw
          (by simpa only [one_div] using! hthresholdInv)
          (inv_nonneg.mpr hthresholdPos.le) hrawBoundNonneg
      _ ≤ (4 * C * (ell : ℝ) ^ (2 * K + 1)) *
          Real.exp ((R : ℝ) * T) * Real.exp (-3 * U / 4) := by
        rw [alignedThinBlockCount, Nat.cast_pow]
        have hellPos : (0 : ℝ) < ell := by positivity
        have hfour : 4 * C / (ell : ℝ) ≤ 4 * C := by
          exact div_le_self (by positivity) hellOne
        have hsmooth' :
            caichWSmoothingParameterNatCast q
                (alignedRootExpTestPoint m i) *
              Real.log (alignedRootExpTestPoint m i : ℝ) ≤
            Real.exp ((R : ℝ) * T) := by
          simpa only [R, T] using! hsmooth
        have hpolyFactor :
            (ell : ℝ) ^ (K + 1) * (ell : ℝ) ^ K *
                (4 * C / (ell : ℝ)) ≤
              4 * C * (ell : ℝ) ^ (2 * K + 1) := by
          have hpowNonneg : 0 ≤
              (ell : ℝ) ^ (K + 1) * (ell : ℝ) ^ K := by positivity
          calc
            (ell : ℝ) ^ (K + 1) * (ell : ℝ) ^ K *
                (4 * C / (ell : ℝ)) ≤
              (ell : ℝ) ^ (K + 1) * (ell : ℝ) ^ K * (4 * C) :=
                mul_le_mul_of_nonneg_left hfour hpowNonneg
            _ = 4 * C *
                ((ell : ℝ) ^ (K + 1) * (ell : ℝ) ^ K) := by ring
            _ = 4 * C * (ell : ℝ) ^ (2 * K + 1) := by
              rw [← pow_add]
              congr 2
              omega
        dsimp only [U, T, R] at *
        calc
          (ell : ℝ) ^ (K + 1) *
                caichWSmoothingParameterNatCast q
                  (alignedRootExpTestPoint m i) *
              Real.exp (-3 * (ell : ℝ) ^ (50 * K) / 4) *
            (4 * C / (ell : ℝ)) *
              Real.log (alignedRootExpTestPoint m i : ℝ) *
                (ell : ℝ) ^ K ≤
            (4 * C * (ell : ℝ) ^ (2 * K + 1)) *
              Real.exp ((R : ℝ) * (ell : ℝ) ^ K) *
                Real.exp (-3 * (ell : ℝ) ^ (50 * K) / 4) := by
            calc
              _ = ((ell : ℝ) ^ (K + 1) * (ell : ℝ) ^ K *
                    (4 * C / (ell : ℝ))) *
                  (caichWSmoothingParameterNatCast q
                    (alignedRootExpTestPoint m i) *
                    Real.log (alignedRootExpTestPoint m i : ℝ)) *
                  Real.exp (-3 * (ell : ℝ) ^ (50 * K) / 4) := by ring
              _ ≤ (4 * C * (ell : ℝ) ^ (2 * K + 1)) *
                  Real.exp ((R : ℝ) * (ell : ℝ) ^ K) *
                  Real.exp (-3 * (ell : ℝ) ^ (50 * K) / 4) := by
                exact mul_le_mul
                  (mul_le_mul hpolyFactor hsmooth'
                    (mul_nonneg
                      (caichWSmoothingParameterNatCast_pos q
                        (alignedRootExpTestPoint m i)).le
                      (Real.log_nonneg (by
                        exact_mod_cast
                          (one_lt_alignedRootExpTestPoint_of_mem hi).le)))
                    (by positivity))
                  le_rfl (by positivity) (by positivity))
  have hpref :
      (4 * C * (ell : ℝ) ^ (2 * K + 1)) *
          Real.exp ((R : ℝ) * T) ≤ Real.exp (2 * V) := by
    calc
      (4 * C * (ell : ℝ) ^ (2 * K + 1)) *
          Real.exp ((R : ℝ) * T) ≤ Real.exp V * Real.exp V :=
        mul_le_mul hpolyV hRexp (by positivity) (by positivity)
      _ = Real.exp (2 * V) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hVabsorb : 2 * V ≤ U / 4 := by
    have h8 : (8 : ℝ) ≤ (ell : ℝ) ^ (48 * K) := by
      have hpowNat : ell ≤ ell ^ (48 * K) :=
        le_self_pow₀ (by omega : 1 ≤ ell) (by omega : 48 * K ≠ 0)
      have h8ell : (8 : ℝ) ≤ ell := by exact_mod_cast (show 8 ≤ ell by omega)
      have hellPow : (ell : ℝ) ≤ (ell : ℝ) ^ (48 * K) := by
        exact_mod_cast hpowNat
      exact h8ell.trans hellPow
    have hmul := mul_le_mul_of_nonneg_right h8 hVpos.le
    dsimp only [V, U]
    rw [show 50 * K = 48 * K + 2 * K by omega, pow_add]
    nlinarith
  have hDabsorb : 2 * D * T ≤ U / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hDpowEll hTpos.le
    dsimp only [T, U]
    rw [show 50 * K = 49 * K + K by omega, pow_add]
    nlinarith
  refine hcoarse.trans ?_
  calc
    (4 * C * (ell : ℝ) ^ (2 * K + 1)) *
          Real.exp ((R : ℝ) * T) * Real.exp (-3 * U / 4) ≤
        Real.exp (2 * V) * Real.exp (-3 * U / 4) :=
      mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = Real.exp (2 * V - 3 * U / 4) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    _ ≤ Real.exp (-(2 * (2 * m + 2 : ℕ) : ℝ) * (ell : ℝ) ^ K) := by
      apply Real.exp_le_exp.mpr
      have hDabsorb' := hDabsorb
      dsimp only [D, T] at hDabsorb'
      norm_cast at hDabsorb'
      nlinarith

/-- The all-scale extension of the selected `L12` first moment is
nonnegative. -/
theorem selectedAlignedHarperSafeL12Moment_nonneg
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m ell i : ℕ) :
    0 ≤ selectedAlignedHarperSafeL12Moment hK hHarper q m ell i := by
  classical
  unfold selectedAlignedHarperSafeL12Moment
  split_ifs with hi
  · let := Classical.decPred
      (selectedAlignedHarperNear hK hHarper m ell i)
    unfold selectedAlignedHarperL12FirstMoment
    apply caichScheduledL12FirstMoment_nonneg
    · exact (caichWSmoothingParameterNatCast_pos q
        (alignedRootExpTestPoint m i)).le
    · exact Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi)
  · norm_num

/-- The exact selected aligned `L12` finite-union moment budget is
unconditionally summable. -/
theorem selectedAlignedHarperL12ScalarSummability_unconditional
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    SelectedAlignedHarperL12ScalarSummability hK hHarper q m := by
  classical
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  let tests : ℕ → Finset ℕ := alignedRootExpTests K m
  let moment : ℕ → ℕ → ℝ :=
    selectedAlignedHarperSafeL12Moment hK hHarper q m
  have hpoint := eventually_selectedAlignedHarperSafeL12Moment_term_le_exp
    hC.le hP hN hK hHarper q m
  have hmajor : ∀ᶠ ell : ℕ in atTop,
      ‖caichAuxiliaryFiniteUnionMomentBudget tests moment
          (selectedAlignedLargeSafeThreshold K) 1 ell‖ ≤
        Real.exp (-(ell : ℝ)) := by
    filter_upwards [hpoint, eventually_ge_atTop (1 : ℕ)] with
        ell hpointEll hell
    have htermNonneg : ∀ i ∈ tests ell,
        0 ≤ moment ell i / selectedAlignedLargeSafeThreshold K ell ^ 1 := by
      intro i hi
      dsimp only [moment]
      exact div_nonneg
        (selectedAlignedHarperSafeL12Moment_nonneg
          hK hHarper q m ell i)
        (pow_nonneg (selectedAlignedLargeSafeThreshold_pos K ell).le 1)
    have hcostNonneg : 0 ≤ caichAuxiliaryFiniteUnionMomentBudget
        tests moment (selectedAlignedLargeSafeThreshold K) 1 ell := by
      unfold caichAuxiliaryFiniteUnionMomentBudget
      exact Finset.sum_nonneg htermNonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hcostNonneg]
    let D : ℝ := (2 * m + 2 : ℕ)
    let T : ℝ := (ell : ℝ) ^ K
    have hcard := card_alignedRootExpTests_le_exp_entropy K m ell
    have hDT : ((tests ell).card : ℝ) ≤ Real.exp (D * T) := by
      simpa only [tests, D, T, Real.rpow_natCast] using! hcard
    have hlinear : (ell : ℝ) ≤ D * T := by
      have hellPow : (ell : ℝ) ≤ (ell : ℝ) ^ K := by
        have hnat : ell ≤ ell ^ K :=
          le_self_pow₀ hell (show K ≠ 0 by omega)
        exact_mod_cast hnat
      have hD : (1 : ℝ) ≤ D := by
        dsimp [D]
        exact_mod_cast (show 1 ≤ 2 * m + 2 by omega)
      have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
      have hTmul : T ≤ D * T := by
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right hD hTnonneg
      exact hellPow.trans (by simpa only [T] using! hTmul)
    unfold caichAuxiliaryFiniteUnionMomentBudget
    calc
      (∑ i ∈ tests ell,
          moment ell i / selectedAlignedLargeSafeThreshold K ell ^ 1) ≤
          ∑ _i ∈ tests ell, Real.exp (-2 * D * T) := by
        gcongr with i hi
        dsimp only [moment]
        simpa only [pow_one, D, T, neg_mul] using!
          hpointEll i (by simpa only [tests] using! hi)
      _ = ((tests ell).card : ℝ) * Real.exp (-2 * D * T) := by simp
      _ ≤ Real.exp (D * T) * Real.exp (-2 * D * T) :=
        mul_le_mul_of_nonneg_right hDT (Real.exp_pos _).le
      _ = Real.exp (-D * T) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(ell : ℝ)) := by
        exact Real.exp_le_exp.mpr (by linarith)
  simpa only [SelectedAlignedHarperL12ScalarSummability, tests, moment] using!
    Real.summable_exp_neg_nat.of_norm_bounded_eventually_nat hmajor

/-- Markov, the exact finite test union, and the finite initial-scale bridge
from the safe threshold back to Caich's published `L12` threshold. -/
theorem summable_measureReal_selectedAlignedHarperL12_failure
    {K : ℕ} (hK : 9 ≤ K)
    (hHarper : HarperRademacherInitialMomentStatement)
    (q m : ℕ) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure (alignedRootExpTests K m)
        (selectedAlignedHarperL12 hK hHarper q m)
        (caichLargeAuxThreshold K) ell) := by
  classical
  let tests := alignedRootExpTests K m
  let value := selectedAlignedHarperL12 hK hHarper q m
  let safeValue : ℕ → ℕ → Omega → ℝ := fun ell i omega ↦
    if i ∈ tests ell then value ell i omega else 0
  let safeMoment : ℕ → ℕ → ℝ := fun ell i ↦
    if i ∈ tests ell then
      selectedAlignedHarperL12FirstMoment hK hHarper q m ell i else 0
  have hscalar := selectedAlignedHarperL12ScalarSummability_unconditional
    hK hHarper q m
  have hsafe := summable_measureReal_caichAuxiliaryComponentFailure_of_natMoment
    tests safeValue safeMoment (selectedAlignedLargeSafeThreshold K) 1
    (by omega)
    (fun ell i omega ↦ by
      unfold safeValue
      by_cases hi : i ∈ tests ell
      · rw [if_pos hi]
        dsimp only [value]
        let := Classical.decPred
          (selectedAlignedHarperNear hK hHarper m ell i)
        unfold selectedAlignedHarperL12
        exact caichScheduledL12_nonneg
          (caichWSmoothingParameterNatCast_pos q
            (alignedRootExpTestPoint m i)).le omega
          (Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi))
          _ _ _ _
      · rw [if_neg hi])
    (selectedAlignedLargeSafeThreshold_pos K)
    (fun ell i ↦ by
      unfold safeValue
      by_cases hi : i ∈ tests ell
      · simp only [if_pos hi, pow_one]
        exact integrable_selectedAlignedHarperL12 (q := q) hK hHarper hi
      · simp [hi])
    (fun ell i ↦ by
      unfold safeValue safeMoment
      by_cases hi : i ∈ tests ell
      · simp only [if_pos hi, pow_one]
        exact integral_selectedAlignedHarperL12_le_firstMoment
          (q := q) hK hHarper hi
      · simp [hi])
    (by simpa only [tests, safeMoment,
      selectedAlignedHarperSafeL12Moment] using! hscalar)
  apply hsafe.congr
  intro ell
  by_cases hell : ell < 5
  · have hempty : tests ell = ∅ := by
      simp [tests, alignedRootExpTests, hell]
    simp [tests, safeValue, value, hempty, caichAuxiliaryComponentFailure,
      caichAuxiliaryComponentGoodAtScale]
  · congr 1
    ext omega
    simp only [safeValue, value,
      selectedAlignedLargeSafeThreshold, if_neg hell,
      caichAuxiliaryComponentFailure, caichAuxiliaryComponentGoodAtScale,
      Set.mem_setOf_eq, not_forall, not_le]
    constructor
    · rintro ⟨i, hi, hbad⟩
      exact ⟨i, by simpa only [tests] using! hi,
        by simpa only [if_pos hi] using! hbad⟩
    · rintro ⟨i, hi, hbad⟩
      have hi' : i ∈ tests ell := by simpa only [tests] using! hi
      exact ⟨i, hi', by simpa only [if_pos hi'] using! hbad⟩

end Problem520
end Erdos
