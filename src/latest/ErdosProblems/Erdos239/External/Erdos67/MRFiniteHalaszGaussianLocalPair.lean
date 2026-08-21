import ErdosProblems.Erdos239.External.Erdos67.MRFiniteHalaszGaussianMean
import ErdosProblems.Erdos239.External.Erdos67.MRIntervalBetaSieve

/-!
# Local-pair Gaussian bounds for finite Halasz factors

This module replaces the global `cardinality × square-mass` estimate in
the first Gaussian implementation by a row-wise close-pair estimate.  The
key point is that a Gaussian row only sees an interval of length `O(U/T)`
inside `(0,U]`; the arbitrary-interval beta sieve therefore cancels the
outer Gaussian factor `T`.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67
open Erdos67.MRIntervalBetaSieve

/-- On positive integers bounded by `U`, additive separation divided by
`U` is a lower bound for logarithmic separation. -/
theorem natDist_div_le_abs_log_sub_log
    {m n U : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hmU : m ≤ U) (hnU : n ≤ U) :
    ((Nat.dist m n : ℕ) : ℝ) / U ≤
      |Real.log m - Real.log n| := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hUR : (0 : ℝ) < U := by exact_mod_cast hm.trans_le hmU
  rcases le_total m n with hmn | hnm
  · rw [Nat.dist_eq_sub_of_le hmn, Nat.cast_sub hmn]
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hnR hmR)
    rw [inv_div] at hlog
    have hmono : Real.log m ≤ Real.log n :=
      Real.log_le_log hmR (by exact_mod_cast hmn)
    rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
    have hnUR : (n : ℝ) ≤ U := by exact_mod_cast hnU
    calc
      ((n : ℝ) - m) / U ≤ ((n : ℝ) - m) / n := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr (by exact_mod_cast hmn))
          hnR hnUR
      _ = 1 - (m : ℝ) / n := by field_simp
      _ ≤ Real.log ((n : ℝ) / m) := hlog
      _ = Real.log n - Real.log m := Real.log_div hnR.ne' hmR.ne'
      _ = -(Real.log m - Real.log n) := by ring
  · rw [Nat.dist_eq_sub_of_le_right hnm, Nat.cast_sub hnm]
    have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hmR hnR)
    rw [inv_div] at hlog
    have hmono : Real.log n ≤ Real.log m :=
      Real.log_le_log hnR (by exact_mod_cast hnm)
    rw [abs_of_nonneg (sub_nonneg.mpr hmono)]
    have hmUR : (m : ℝ) ≤ U := by exact_mod_cast hmU
    calc
      ((m : ℝ) - n) / U ≤ ((m : ℝ) - n) / m := by
        exact div_le_div_of_nonneg_left (sub_nonneg.mpr (by exact_mod_cast hnm))
          hmR hmUR
      _ = 1 - (n : ℝ) / m := by field_simp
      _ ≤ Real.log ((m : ℝ) / n) := hlog
      _ = Real.log m - Real.log n := Real.log_div hmR.ne' hnR.ne'

/-- The Gaussian kernel is geometrically small once its scaled argument
crosses the `4k` threshold. -/
theorem finiteHalaszGaussianPairKernel_inv_sq_le_pow_half
    {T x : ℝ} (hT : 0 < T) {k : ℕ}
    (hgap : 4 * (k : ℝ) ≤ T * |x|) :
    finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) x ≤
      (1 / 2 : ℝ) ^ k := by
  have hscaled : (k : ℝ) ≤ (T * |x|) ^ 2 / 4 := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hs0 : 0 ≤ T * |x| := mul_nonneg hT.le (abs_nonneg x)
    have hsq : (4 * (k : ℝ)) ^ 2 ≤ (T * |x|) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (by norm_num) hk0) hgap 2
    by_cases hk : k = 0
    · subst k
      norm_num only [Nat.cast_zero]
      show (0 : ℝ) ≤ (T * |x|) ^ 2 / 4
      exact div_nonneg (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    · have hk1 : (1 : ℝ) ≤ k := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk1)]
  have hkernel :
      finiteHalaszGaussianPairKernel (T⁻¹ ^ 2) x =
        Real.exp (-((T * |x|) ^ 2 / 4)) := by
    unfold finiteHalaszGaussianPairKernel
    have hTne : T ≠ 0 := ne_of_gt hT
    rw [← sq_abs x]
    congr 1
    field_simp [hTne]
  rw [hkernel]
  calc
    Real.exp (-((T * |x|) ^ 2 / 4)) ≤ Real.exp (-(k : ℝ)) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hscaled)
    _ = Real.exp (-1) ^ k := by
      rw [show -(k : ℝ) = (k : ℝ) * (-1) by ring,
        Real.exp_nat_mul]
    _ ≤ (1 / 2 : ℝ) ^ k :=
      pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_neg_one_lt_half.le k

/-- First two moments of the half-geometric weights. -/
theorem sum_range_succ_mul_pow_half_eq (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) =
      4 - 2 * (K + 2 : ℕ) * (1 / 2 : ℝ) ^ K := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      push_cast
      ring

theorem sum_range_succ_mul_pow_half_le_four (K : ℕ) :
    (∑ k ∈ Finset.range K, ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) ≤ 4 := by
  rw [sum_range_succ_mul_pow_half_eq]
  have hnonneg : 0 ≤ 2 * (K + 2 : ℕ) * (1 / 2 : ℝ) ^ K := by positivity
  linarith

/-- Additive-distance bucket used to localize one Gaussian row. -/
def finiteHalaszGaussianDistanceBucket
    (T : ℝ) (U n m : ℕ) : ℕ :=
  ⌊T * (Nat.dist n m : ℝ) / (4 * U)⌋₊

/-- Natural radius containing the `k`-th distance bucket. -/
def finiteHalaszGaussianDistanceRadius
    (T : ℝ) (U : ℕ) (k : ℕ) : ℕ :=
  ⌈4 * (U : ℝ) * (k + 1 : ℕ) / T⌉₊

theorem finiteHalaszGaussianDistanceBucket_lt
    {T : ℝ} (hT : 0 < T) {U n m : ℕ} (hU : 0 < U)
    (hnU : n ≤ U) (hmU : m ≤ U) :
    finiteHalaszGaussianDistanceBucket T U n m < ⌊T / 4⌋₊ + 1 := by
  have hdist : Nat.dist n m ≤ U := by
    rcases le_total n m with hnm | hmn
    · rw [Nat.dist_eq_sub_of_le hnm]
      omega
    · rw [Nat.dist_eq_sub_of_le_right hmn]
      omega
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  have harg0 : 0 ≤ T * (Nat.dist n m : ℝ) / (4 * U) := by positivity
  have harg : T * (Nat.dist n m : ℝ) / (4 * U) ≤ T / 4 := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * U)
      (by norm_num : (0 : ℝ) < 4)).2
    have hdistR : ((Nat.dist n m : ℕ) : ℝ) ≤ U := by exact_mod_cast hdist
    nlinarith
  unfold finiteHalaszGaussianDistanceBucket
  exact (Nat.floor_le_floor harg).trans_lt (Nat.lt_succ_self _)

theorem finiteHalaszGaussianDistanceBucket_scaledGap
    {T : ℝ} (hT : 0 < T) {U n m : ℕ} (hU : 0 < U)
    (hm : 0 < m) (hn : 0 < n) (hmU : m ≤ U) (hnU : n ≤ U) :
    4 * (finiteHalaszGaussianDistanceBucket T U n m : ℝ) ≤
      T * |Real.log m - Real.log n| := by
  have harg0 : 0 ≤ T * (Nat.dist n m : ℝ) / (4 * U) := by positivity
  have hfloor := Nat.floor_le harg0
  have hlog := natDist_div_le_abs_log_sub_log hm hn hmU hnU
  rw [Nat.dist_comm] at hlog
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  unfold finiteHalaszGaussianDistanceBucket
  calc
    4 * (⌊T * (Nat.dist n m : ℝ) / (4 * U)⌋₊ : ℝ) ≤
        4 * (T * (Nat.dist n m : ℝ) / (4 * U)) := by gcongr
    _ = T * (((Nat.dist n m : ℕ) : ℝ) / U) := by field_simp
    _ ≤ T * |Real.log m - Real.log n| :=
      mul_le_mul_of_nonneg_left hlog hT.le

/-- The points in one additive-distance bucket of the missing-block set. -/
def finiteHalaszGaussianDistanceFiber
    (I : ℕ × ℕ) (L U : ℕ) (T : ℝ) (n k : ℕ) : Finset ℕ :=
  (intervalMissingPrimeBlockSet I L U).filter fun m ↦
    finiteHalaszGaussianDistanceBucket T U n m = k

@[simp] theorem mem_finiteHalaszGaussianDistanceFiber
    {I : ℕ × ℕ} {L U n m k : ℕ} {T : ℝ} :
    m ∈ finiteHalaszGaussianDistanceFiber I L U T n k ↔
      m ∈ intervalMissingPrimeBlockSet I L U ∧
        finiteHalaszGaussianDistanceBucket T U n m = k := by
  simp [finiteHalaszGaussianDistanceFiber]

/-- Membership in bucket `k` forces additive distance at most the natural
radius attached to that bucket. -/
theorem natDist_le_finiteHalaszGaussianDistanceRadius
    {T : ℝ} (hT : 0 < T) {U n m k : ℕ} (hU : 0 < U)
    (hk : finiteHalaszGaussianDistanceBucket T U n m = k) :
    Nat.dist n m ≤ finiteHalaszGaussianDistanceRadius T U k := by
  have hUR : (0 : ℝ) < U := by exact_mod_cast hU
  have harg0 : 0 ≤ T * (Nat.dist n m : ℝ) / (4 * U) := by positivity
  have hfloorlt := Nat.lt_floor_add_one
    (T * (Nat.dist n m : ℝ) / (4 * U))
  unfold finiteHalaszGaussianDistanceBucket at hk
  rw [hk] at hfloorlt
  have hdistlt : ((Nat.dist n m : ℕ) : ℝ) <
      4 * (U : ℝ) * (k + 1 : ℕ) / T := by
    have hden : (0 : ℝ) < 4 * U := by positivity
    apply (lt_div_iff₀ hT).2
    apply (div_lt_iff₀ hden).1 at hfloorlt
    calc
      ((Nat.dist n m : ℕ) : ℝ) * T =
          T * (Nat.dist n m : ℝ) := by ring
      _ < ((k : ℝ) + 1) * (4 * (U : ℝ)) := hfloorlt
      _ = 4 * (U : ℝ) * (k + 1 : ℕ) := by
        push_cast
        ring
  have hrceil := Nat.le_ceil
    (4 * (U : ℝ) * (k + 1 : ℕ) / T)
  unfold finiteHalaszGaussianDistanceRadius
  have hcast : ((Nat.dist n m : ℕ) : ℝ) <
      (⌈4 * (U : ℝ) * (k + 1 : ℕ) / T⌉₊ : ℝ) :=
    hdistlt.trans_le hrceil
  exact_mod_cast hcast.le

/-- A natural distance ball is contained in one ordinary integer
interval.  The extra unit on the lower endpoint makes the containment
valid even when truncated subtraction hits zero. -/
theorem mem_Ioc_sub_sub_one_add_of_natDist_le
    {n m H : ℕ} (hm : 0 < m) (hdist : Nat.dist n m ≤ H) :
    m ∈ Finset.Ioc (n - H - 1) (n + H) := by
  rw [Finset.mem_Ioc]
  rcases le_total n m with hnm | hmn
  · rw [Nat.dist_eq_sub_of_le hnm] at hdist
    omega
  · rw [Nat.dist_eq_sub_of_le_right hmn] at hdist
    omega

/-- A Gaussian distance fiber is contained in a short missing-block
interval centered at its base point. -/
theorem finiteHalaszGaussianDistanceFiber_subset_interval
    {I : ℕ × ℕ} {L U n k : ℕ} {T : ℝ}
    (hT : 0 < T) (hU : 0 < U) :
    finiteHalaszGaussianDistanceFiber I L U T n k ⊆
      intervalMissingPrimeBlockSet I
        (n - finiteHalaszGaussianDistanceRadius T U k - 1)
        (n + finiteHalaszGaussianDistanceRadius T U k) := by
  intro m hm
  rw [mem_finiteHalaszGaussianDistanceFiber] at hm
  rw [mem_intervalMissingPrimeBlockSet]
  have hdist := natDist_le_finiteHalaszGaussianDistanceRadius
    hT hU hm.2
  have hmpos : 0 < m :=
    (Nat.zero_le L).trans_lt (mem_intervalMissingPrimeBlockSet.mp hm.1).1
  have hspatial := Finset.mem_Ioc.mp
    (mem_Ioc_sub_sub_one_add_of_natDist_le hmpos hdist)
  exact ⟨hspatial.1, hspatial.2,
    (mem_intervalMissingPrimeBlockSet.mp hm.1).2.2⟩

/-- The containing interval has the expected `O(U(k+1)/T)` length. -/
theorem cast_centeredGaussianRadiusIntervalLength_le
    {T : ℝ} (hT : 0 < T) {U n k : ℕ} (hU : 0 < U) :
    (((n + finiteHalaszGaussianDistanceRadius T U k) -
        (n - finiteHalaszGaussianDistanceRadius T U k - 1) : ℕ) : ℝ) ≤
      8 * (U : ℝ) * (k + 1 : ℕ) / T + 3 := by
  let H := finiteHalaszGaussianDistanceRadius T U k
  let r : ℝ := 4 * (U : ℝ) * (k + 1 : ℕ) / T
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hH : (H : ℝ) < r + 1 := by
    dsimp only [H, finiteHalaszGaussianDistanceRadius, r]
    exact Nat.ceil_lt_add_one hr0
  have hlenNat :
      (n + H) - (n - H - 1) ≤ 2 * H + 1 := by omega
  have hlenReal :
      (((n + H) - (n - H - 1) : ℕ) : ℝ) ≤ 2 * (H : ℝ) + 1 := by
    exact_mod_cast hlenNat
  have hlast : 2 * (H : ℝ) + 1 ≤ 2 * r + 3 := by linarith
  calc
    (((n + finiteHalaszGaussianDistanceRadius T U k) -
        (n - finiteHalaszGaussianDistanceRadius T U k - 1) : ℕ) : ℝ) ≤
        2 * (finiteHalaszGaussianDistanceRadius T U k : ℝ) + 1 := hlenReal
    _ ≤ 2 * r + 3 := hlast
    _ = 8 * (U : ℝ) * (k + 1 : ℕ) / T + 3 := by
      dsimp only [r]
      ring

/-- A local beta-sieve estimate on arbitrary intervals bounds each
Gaussian distance fiber. -/
theorem card_finiteHalaszGaussianDistanceFiber_le_of_intervalBeta
    {I : ℕ × ℕ} {L U n k : ℕ} {T density remainder : ℝ}
    (hT : 0 < T) (hU : 0 < U) (hdensity : 0 ≤ density)
    (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    ((finiteHalaszGaussianDistanceFiber I L U T n k).card : ℝ) ≤
      (8 * (U : ℝ) * (k + 1 : ℕ) / T + 3) * density + remainder := by
  let H := finiteHalaszGaussianDistanceRadius T U k
  let A := n - H - 1
  let B := n + H
  have hsub := finiteHalaszGaussianDistanceFiber_subset_interval
    (I := I) (L := L) (U := U) (n := n) (k := k) hT hU
  have hcard :
      ((finiteHalaszGaussianDistanceFiber I L U T n k).card : ℝ) ≤
        ((intervalMissingPrimeBlockSet I A B).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hAB : A ≤ B := by dsimp [A, B, H]; omega
  have hlength := cast_centeredGaussianRadiusIntervalLength_le
    (n := n) (k := k) hT hU
  have hlength' : (((B - A : ℕ) : ℝ)) ≤
      8 * (U : ℝ) * (k + 1 : ℕ) / T + 3 := by
    simpa only [A, B, H] using hlength
  calc
    ((finiteHalaszGaussianDistanceFiber I L U T n k).card : ℝ) ≤
        ((intervalMissingPrimeBlockSet I A B).card : ℝ) := hcard
    _ ≤ (((B - A : ℕ) : ℝ) * density + remainder) := hbeta A B hAB
    _ ≤ (8 * (U : ℝ) * (k + 1 : ℕ) / T + 3) * density + remainder := by
      exact add_le_add (mul_le_mul_of_nonneg_right hlength' hdensity) le_rfl

/-- One Gaussian row over a missing-block set.  The `U/T` term is the
source-sharp close-pair contribution; the only term growing with the
number of buckets is the finite beta-sieve level remainder, which is kept
explicit. -/
theorem sum_missingBlock_gaussianRow_le_of_intervalBeta
    {I : ℕ × ℕ} {L U n : ℕ} {T density remainder : ℝ}
    (hT : 0 < T) (hU : 0 < U)
    (hn : n ∈ intervalMissingPrimeBlockSet I L U)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∑ m ∈ intervalMissingPrimeBlockSet I L U,
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n)) ≤
      32 * (U : ℝ) / T * density + 6 * density + 2 * remainder := by
  let D := intervalMissingPrimeBlockSet I L U
  let K := ⌊T / 4⌋₊ + 1
  let bucket : ℕ → ℕ := fun m ↦
    finiteHalaszGaussianDistanceBucket T U n m
  have hnmem := mem_intervalMissingPrimeBlockSet.mp hn
  have hnpos : 0 < n := (Nat.zero_le L).trans_lt hnmem.1
  have hnU : n ≤ U := hnmem.2.1
  have hmaps : ∀ m ∈ D, bucket m ∈ Finset.range K := by
    intro m hm
    have hmmem := mem_intervalMissingPrimeBlockSet.mp hm
    exact Finset.mem_range.mpr
      (finiteHalaszGaussianDistanceBucket_lt hT hU hnU hmmem.2.1)
  have hfiber (k : ℕ) (hk : k ∈ Finset.range K) :
      (∑ m ∈ D with bucket m = k,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
        (8 * (U : ℝ) * (k + 1 : ℕ) / T + 3) * density *
              (1 / 2 : ℝ) ^ k +
            remainder * (1 / 2 : ℝ) ^ k := by
    let F := D.filter fun m ↦ bucket m = k
    have hpoint : ∀ m ∈ F,
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) ≤ (1 / 2 : ℝ) ^ k := by
      intro m hm
      have hmD : m ∈ D := (Finset.mem_filter.mp hm).1
      have hmbucket : bucket m = k := (Finset.mem_filter.mp hm).2
      have hmmem := mem_intervalMissingPrimeBlockSet.mp hmD
      have hmpos : 0 < m := (Nat.zero_le L).trans_lt hmmem.1
      have hgap := finiteHalaszGaussianDistanceBucket_scaledGap
        hT hU hmpos hnpos hmmem.2.1 hnU
      dsimp only [bucket] at hmbucket
      rw [hmbucket] at hgap
      exact finiteHalaszGaussianPairKernel_inv_sq_le_pow_half hT hgap
    have hsum :
        (∑ m ∈ F,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
          (F.card : ℝ) * (1 / 2 : ℝ) ^ k := by
      calc
        _ ≤ ∑ _m ∈ F, (1 / 2 : ℝ) ^ k :=
          Finset.sum_le_sum hpoint
        _ = (F.card : ℝ) * (1 / 2 : ℝ) ^ k := by simp
    have hcard := card_finiteHalaszGaussianDistanceFiber_le_of_intervalBeta
      (I := I) (L := L) (U := U) (n := n) (k := k)
      hT hU hdensity hrem hbeta
    have hhalf : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    calc
      (∑ m ∈ D with bucket m = k,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
          ((finiteHalaszGaussianDistanceFiber I L U T n k).card : ℝ) *
            (1 / 2 : ℝ) ^ k := by
              simpa only [F, D, bucket,
                finiteHalaszGaussianDistanceFiber] using hsum
      _ ≤ ((8 * (U : ℝ) * (k + 1 : ℕ) / T + 3) * density + remainder) *
            (1 / 2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hcard hhalf
      _ = (8 * (U : ℝ) * (k + 1 : ℕ) / T + 3) * density *
              (1 / 2 : ℝ) ^ k +
            remainder * (1 / 2 : ℝ) ^ k := by ring
  have hgroup :
      (∑ m ∈ D,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) =
        ∑ k ∈ Finset.range K, ∑ m ∈ D with bucket m = k,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  rw [hgroup]
  calc
    (∑ k ∈ Finset.range K, ∑ m ∈ D with bucket m = k,
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n)) ≤
      ∑ k ∈ Finset.range K,
        ((8 * (U : ℝ) * (k + 1 : ℕ) / T + 3) * density *
              (1 / 2 : ℝ) ^ k +
            remainder * (1 / 2 : ℝ) ^ k) := by
      exact Finset.sum_le_sum hfiber
    _ = (8 * (U : ℝ) / T * density) *
          (∑ k ∈ Finset.range K,
            ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) +
        (3 * density + remainder) *
          (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) := by
      calc
        _ = ∑ k ∈ Finset.range K,
              ((8 * (U : ℝ) / T * density) *
                  ((k + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k +
                (3 * density + remainder) * (1 / 2 : ℝ) ^ k) := by
            apply Finset.sum_congr rfl
            intro k hk
            push_cast
            ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ ≤ (8 * (U : ℝ) / T * density) * 4 +
        (3 * density + remainder) * 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (sum_range_succ_mul_pow_half_le_four K) (by positivity)
      · exact mul_le_mul_of_nonneg_left (sum_geometric_two_le K)
          (add_nonneg (mul_nonneg (by norm_num) hdensity) hrem)
    _ = 32 * (U : ℝ) / T * density + 6 * density + 2 * remainder := by
      ring

/-- Summing the local Gaussian row estimate over its base point costs
only the length of the ambient interval. -/
theorem sum_missingBlock_gaussianPairs_le_of_intervalBeta
    {I : ℕ × ℕ} {L U : ℕ} {T density remainder : ℝ}
    (hT : 0 < T) (hU : 0 < U) (hLU : L ≤ U)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∑ n ∈ intervalMissingPrimeBlockSet I L U,
        ∑ m ∈ intervalMissingPrimeBlockSet I L U,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      ((((U - L : ℕ) : ℝ) * density + remainder)) *
        (32 * (U : ℝ) / T * density + 6 * density + 2 * remainder) := by
  let D := intervalMissingPrimeBlockSet I L U
  let R := 32 * (U : ℝ) / T * density + 6 * density + 2 * remainder
  have hrow : ∀ n ∈ D,
      (∑ m ∈ D, finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n)) ≤ R := by
    intro n hn
    exact sum_missingBlock_gaussianRow_le_of_intervalBeta
      hT hU hn hdensity hrem hbeta
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hcard : (D.card : ℝ) ≤
      (((U - L : ℕ) : ℝ) * density + remainder) := hbeta L U hLU
  calc
    (∑ n ∈ D, ∑ m ∈ D,
        finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
          (Real.log m - Real.log n)) ≤
        ∑ _n ∈ D, R := Finset.sum_le_sum hrow
    _ = (D.card : ℝ) * R := by simp
    _ ≤ ((((U - L : ℕ) : ℝ) * density + remainder)) * R :=
      mul_le_mul_of_nonneg_right hcard hR

/-- A coefficient supported on one missing-prime-block interval inherits
the source-sharp row estimate.  The coefficient norm bound is deliberately
kept abstract so that this lemma can be reused after frequency twists. -/
theorem finiteHalaszLogGaussianPairMajorant_le_of_intervalBeta
    {I : ℕ × ℕ} {L U : ℕ} {a : ℕ → ℂ}
    {T density remainder W : ℝ}
    (hT : 0 < T) (hU : 0 < U) (hLU : L ≤ U)
    (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder) (hW : 0 ≤ W)
    (hsupport : ∀ n ∈ Finset.Ioc L U, a n ≠ 0 →
      n ∈ intervalMissingPrimeBlockSet I L U)
    (hcoeff : ∀ n ∈ Finset.Ioc L U, ‖a n‖ ≤ W)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    finiteHalaszLogGaussianPairMajorant (Finset.Ioc L U) a (T⁻¹ ^ 2) ≤
      Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
        (W ^ 2 * ((((U - L : ℕ) : ℝ) * density + remainder)) *
          (32 * (U : ℝ) / T * density + 6 * density + 2 * remainder)) := by
  let D := Finset.Ioc L U
  let E := intervalMissingPrimeBlockSet I L U
  have hED : E ⊆ D := by
    intro n hn
    exact Finset.mem_Ioc.mpr
      ⟨(mem_intervalMissingPrimeBlockSet.mp hn).1,
        (mem_intervalMissingPrimeBlockSet.mp hn).2.1⟩
  have hzero : ∀ n ∈ D, n ∉ E → a n = 0 := by
    intro n hnD hnE
    by_contra hne
    exact hnE (hsupport n hnD hne)
  have hinner : ∀ n,
      (∑ m ∈ D, ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) =
        ∑ m ∈ E, ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
    intro n
    symm
    apply Finset.sum_subset hED
    intro m hmD hmE
    rw [hzero m hmD hmE, norm_zero, mul_zero, zero_mul]
  have hdouble :
      (∑ n ∈ D, ∑ m ∈ D, ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) =
        ∑ n ∈ E, ∑ m ∈ E, ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
    calc
      _ = ∑ n ∈ D, ∑ m ∈ E, ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hinner n
      _ = _ := by
        symm
        apply Finset.sum_subset hED
        intro n hnD hnE
        simp [hzero n hnD hnE]
  have hweighted :
      (∑ n ∈ E, ∑ m ∈ E, ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
        W ^ 2 *
          (∑ n ∈ E, ∑ m ∈ E,
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    have hnD := hED hn
    have hmD := hED hm
    have hk0 := finiteHalaszGaussianPairKernel_nonneg (T⁻¹ ^ 2)
      (Real.log m - Real.log n)
    calc
      ‖a n‖ * ‖a m‖ *
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) ≤
          (W * W) * finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by
        gcongr
        · exact hcoeff n hnD
        · exact hcoeff m hmD
      _ = W ^ 2 * finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n) := by ring
  have hpairs := sum_missingBlock_gaussianPairs_le_of_intervalBeta
    (I := I) (L := L) (U := U) hT hU hLU hdensity hrem hbeta
  unfold finiteHalaszLogGaussianPairMajorant
  rw [hdouble]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  calc
    _ ≤ W ^ 2 *
        (∑ n ∈ E, ∑ m ∈ E,
          finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
            (Real.log m - Real.log n)) := hweighted
    _ ≤ W ^ 2 * (((((U - L : ℕ) : ℝ) * density + remainder)) *
        (32 * (U : ℝ) / T * density + 6 * density + 2 * remainder)) := by
      exact mul_le_mul_of_nonneg_left hpairs (sq_nonneg W)
    _ = W ^ 2 * ((((U - L : ℕ) : ℝ) * density + remainder)) *
        (32 * (U : ℝ) / T * density + 6 * density + 2 * remainder) := by
      ring

/-- A nonzero coefficient from a prime band which avoids `I` belongs to
the corresponding missing-block interval. -/
theorem smoothedPrimeBandCoefficient_mem_intervalMissingPrimeBlockSet
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    (f : ℕ → ℂ) (sigma : ℝ) {L U n : ℕ}
    (hn : n ∈ Finset.Ioc L U)
    (hne : smoothedPrimeBandCoefficient f Q sigma n ≠ 0) :
    n ∈ intervalMissingPrimeBlockSet I L U := by
  have hnI := Finset.mem_Ioc.mp hn
  have hnpos : 0 < n := (Nat.zero_le L).trans_lt hnI.1
  have hprimeCoeff : primeBandCoefficient f Q n ≠ 0 := by
    intro hz
    apply hne
    simp [smoothedPrimeBandCoefficient, hz]
  have hsupp : PrimeSupported Q n := by
    by_contra hs
    exact hprimeCoeff (by simp [primeBandCoefficient, hs])
  rw [mem_intervalMissingPrimeBlockSet]
  refine ⟨hnI.1, hnI.2, ?_⟩
  intro p hpI hpn
  have hpprime : p.Prime := (mem_primesInBlock.mp hpI).1
  have hpFactors : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime, hpn, hnpos.ne'⟩
  exact hdisj p hpI (hsupp.2 p hpFactors)

/-- Uniform lower-endpoint bound for a smoothed prime-band coefficient
on `(L,U]`. -/
theorem norm_smoothedPrimeBandCoefficient_le_lowerEndpoint
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q]
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    {L U n : ℕ} (hL : 0 < L) (hn : n ∈ Finset.Ioc L U) :
    ‖smoothedPrimeBandCoefficient f Q sigma n‖ ≤ (L : ℝ) ^ (-sigma) := by
  have hnI := Finset.mem_Ioc.mp hn
  have hnpos : 0 < n := hL.trans hnI.1
  have hbase : (L : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnI.1.le
  have hrpow : (n : ℝ) ^ (-sigma) ≤ (L : ℝ) ^ (-sigma) := by
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hL) hbase
      (neg_nonpos.mpr hsigma)
  unfold smoothedPrimeBandCoefficient
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  calc
    ‖primeBandCoefficient f Q n‖ * (n : ℝ) ^ (-sigma) ≤
        1 * (L : ℝ) ^ (-sigma) := by
      exact mul_le_mul (norm_primeBandCoefficient_le_one hbound Q hnpos)
        hrpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) zero_le_one
    _ = (L : ℝ) ^ (-sigma) := one_mul _

/-- Local-pair majorant for one finite positive prime-band factor.  This
is the quantitative form in which the interval beta sieve cancels the
Gaussian length factor. -/
theorem finiteHalaszLogGaussianPairMajorant_smoothedPrimeBand_le_of_intervalBeta
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T density remainder : ℝ}
    (hT : 0 < T) (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    finiteHalaszLogGaussianPairMajorant (Finset.Ioc L U)
        (smoothedPrimeBandCoefficient f Q sigma) (T⁻¹ ^ 2) ≤
      Real.sqrt (Real.pi / (T⁻¹ ^ 2)) *
        (((L : ℝ) ^ (-sigma)) ^ 2 *
          ((((U - L : ℕ) : ℝ) * density + remainder)) *
          (32 * (U : ℝ) / T * density + 6 * density + 2 * remainder)) := by
  have hU : 0 < U := hL.trans_le hLU
  exact finiteHalaszLogGaussianPairMajorant_le_of_intervalBeta
    hT hU hLU hdensity hrem
      (Real.rpow_nonneg (Nat.cast_nonneg L) _)
    (fun n hn hne ↦
      smoothedPrimeBandCoefficient_mem_intervalMissingPrimeBlockSet
        I Q hdisj f sigma hn hne)
    (fun n hn ↦
      norm_smoothedPrimeBandCoefficient_le_lowerEndpoint
        hbound Q hsigma hL hn)
    hbeta

/-- Exact cancellation of the inverse-square Gaussian normalization. -/
theorem sqrt_pi_div_inv_sq_local (T : ℝ) (hT : 0 < T) :
    Real.sqrt (Real.pi / (T⁻¹ ^ 2)) = Real.sqrt Real.pi * T := by
  rw [inv_pow, div_inv_eq_mul]
  rw [Real.sqrt_mul Real.pi_nonneg]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hT]

/-- The concrete arbitrary-interval beta sieve inserted into the local
prime-band pair majorant. -/
theorem exists_finiteHalaszLogGaussianPairMajorant_smoothedPrimeBand_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (P Qb S L U : ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) {sigma T : ℝ},
        (∀ p ∈ primesInBlock (P, Qb), ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        0 < L → L ≤ U → 0 ≤ sigma → 0 < T →
        3 ≤ P → P ≤ Qb → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let density := (1 + eta) * primeBlockDensity (P, Qb)
        let remainder := (((Qb ^ S : ℕ) : ℝ) ^ 2)
        finiteHalaszLogGaussianPairMajorant (Finset.Ioc L U)
            (smoothedPrimeBandCoefficient f Q sigma) (T⁻¹ ^ 2) ≤
          Real.sqrt Real.pi * T *
            (((L : ℝ) ^ (-sigma)) ^ 2 *
              ((((U - L : ℕ) : ℝ) * density + remainder)) *
              (32 * (U : ℝ) / T * density +
                6 * density + 2 * remainder)) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    exists_card_intervalMissingPrimeBlockSet_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro P Qb S L U Q _ f sigma T hdisj hbound hL hLU hsigma hT
    hP hPQ hS hlog
  dsimp only
  let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let density := (1 + eta) * primeBlockDensity (P, Qb)
  let remainder := (((Qb ^ S : ℕ) : ℝ) ^ 2)
  have heta0 : 0 ≤ eta := by dsimp [eta]; positivity
  have hdensity : 0 ≤ density := by
    dsimp [density]
    exact mul_nonneg (by linarith) (primeBlockDensity_nonneg (P, Qb))
  have hrem : 0 ≤ remainder := by dsimp [remainder]; positivity
  have hlocal :=
    finiteHalaszLogGaussianPairMajorant_smoothedPrimeBand_le_of_intervalBeta
      (I := (P, Qb)) Q hdisj f hbound hsigma hL hLU hT
      hdensity hrem (fun A B hAB ↦ by
        have hb := hbeta A B P Qb S hAB hP hPQ hS hlog
        simpa only [eta, density, remainder] using hb)
  rw [sqrt_pi_div_inv_sq_local T hT] at hlocal
  simpa only [eta, density, remainder] using hlocal

/-- The local-pair bound in the vertical mean-square form used by the
finite Halasz core. -/
theorem intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_localPair
    (I : ℕ × ℕ) (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ primesInBlock I, ¬ Q p)
    (f : ℕ → ℂ) (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma : ℝ} (hsigma : 0 ≤ sigma)
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {T density remainder : ℝ}
    (hT : 0 < T) (hdensity : 0 ≤ density) (hrem : 0 ≤ remainder)
    (hbeta : ∀ A B : ℕ, A ≤ B →
      ((intervalMissingPrimeBlockSet I A B).card : ℝ) ≤
        (((B - A : ℕ) : ℝ) * density + remainder)) :
    (∫ t in -T..T,
        Complex.normSq (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
      Real.exp 1 * (Real.sqrt Real.pi * T *
        (((L : ℝ) ^ (-sigma)) ^ 2 *
          ((((U - L : ℕ) : ℝ) * density + remainder)) *
          (32 * (U : ℝ) / T * density + 6 * density + 2 * remainder))) := by
  have hmean :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_gaussianPairMajorant
      f Q sigma L U hT
  have hpair :=
    finiteHalaszLogGaussianPairMajorant_smoothedPrimeBand_le_of_intervalBeta
      I Q hdisj f hbound hsigma hL hLU hT hdensity hrem hbeta
  rw [sqrt_pi_div_inv_sq_local T hT] at hpair
  exact hmean.trans (mul_le_mul_of_nonneg_left hpair (Real.exp_pos 1).le)

/-- Concrete interval-beta version of the local finite positive-factor
mean square.  Its main term is quadratic in the block density and the only
remaining loss is the explicit finite sieve level. -/
theorem exists_intervalIntegral_normSq_smoothedPrimeBandPolynomial_localPair_beta_bound :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ (P Qb S L U : ℕ) (Q : ℕ → Prop) [DecidablePred Q]
        (f : ℕ → ℂ) {sigma T : ℝ},
        (∀ p ∈ primesInBlock (P, Qb), ¬ Q p) →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) →
        0 < L → L ≤ U → 0 ≤ sigma → 0 < T →
        3 ≤ P → P ≤ Qb → 101 ≤ S →
        Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99 →
        let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let density := (1 + eta) * primeBlockDensity (P, Qb)
        let remainder := (((Qb ^ S : ℕ) : ℝ) ^ 2)
        (∫ t in -T..T,
            Complex.normSq (smoothedPrimeBandPolynomial f Q sigma L U t)) ≤
          Real.exp 1 * (Real.sqrt Real.pi * T *
            (((L : ℝ) ^ (-sigma)) ^ 2 *
              ((((U - L : ℕ) : ℝ) * density + remainder)) *
              (32 * (U : ℝ) / T * density +
                6 * density + 2 * remainder))) := by
  obtain ⟨Cβ, hCβ, hbeta⟩ :=
    exists_card_intervalMissingPrimeBlockSet_beta_bound
  refine ⟨Cβ, hCβ, ?_⟩
  intro P Qb S L U Q _ f sigma T hdisj hbound hL hLU hsigma hT
    hP hPQ hS hlog
  dsimp only
  let eta := (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let density := (1 + eta) * primeBlockDensity (P, Qb)
  let remainder := (((Qb ^ S : ℕ) : ℝ) ^ 2)
  have heta0 : 0 ≤ eta := by dsimp [eta]; positivity
  have hdensity : 0 ≤ density := by
    dsimp [density]
    exact mul_nonneg (by linarith) (primeBlockDensity_nonneg (P, Qb))
  have hrem : 0 ≤ remainder := by dsimp [remainder]; positivity
  have hlocal :=
    intervalIntegral_normSq_smoothedPrimeBandPolynomial_le_localPair
      (I := (P, Qb)) Q hdisj f hbound hsigma hL hLU hT hdensity hrem
      (fun A B hAB ↦ by
        have hb := hbeta A B P Qb S hAB hP hPQ hS hlog
        simpa only [eta, density, remainder] using hb)
  simpa only [eta, density, remainder] using hlocal

end

end Erdos67.MRHalaszBands
