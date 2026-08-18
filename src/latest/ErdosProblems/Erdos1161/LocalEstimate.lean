import ErdosProblems.Erdos1161.LcmBounds
import ErdosProblems.Erdos1161.CycleIndex

/-!
# The local comparison in Erdős Problem 1161

This file isolates the elementary, but delicate, last step in the proof of
Beker's mode theorem.  If `r` is admissible and `m = n - r`, the local
cycle-index calculation has main term `1 / m` and one possible contribution
from two `m / 2`-cycles.  `halfCycleCorrection` is that contribution.

The analytic cycle-index estimate is recorded below by the predicate
`HasUniformLocalExpansion`.  The numerical lemmas in this file prove that an
`o(n⁻²)` error is enough to distinguish the largest admissible remainder
from every other admissible remainder.  The exact cycle-index argument later
in this file supplies the expansion predicate.
-/

namespace Erdos1161

open Filter

/-! ## Exact long-cycle contribution -/

/-- The order-`m` cycle types which contain an `m`-cycle. -/
def longOrderCycleTypes (n m : ℕ) : Finset (Multiset ℕ) :=
  (orderCycleTypes n m).filter fun mu ↦ m ∈ mu

@[simp] theorem mem_longOrderCycleTypes {n m : ℕ} {mu : Multiset ℕ} :
    mu ∈ longOrderCycleTypes n m ↔
      mu ∈ cycleTypes n ∧ mu.lcm = m ∧ m ∈ mu := by
  simp [longOrderCycleTypes, and_assoc]

/-- A cycle type on fewer than `m` letters cannot contain `m`. -/
theorem not_mem_cycleType_of_sum_lt {r m : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes r) (hrm : r < m) : m ∉ mu := by
  intro hm
  have hmle : m ≤ mu.sum := by
    have hsum := congrArg Multiset.sum (Multiset.cons_erase hm)
    calc
      m ≤ m + (mu.erase m).sum := Nat.le_add_right _ _
      _ = mu.sum := by simpa only [Multiset.sum_cons] using hsum
  exact (not_le_of_gt hrm) (hmle.trans (mem_cycleTypes.mp hmu).1)

/-- Inserting one `m`-cycle multiplies the cycle-index denominator by `m`,
provided the residual cycle type lives on fewer than `m` letters. -/
theorem cycleDenominator_cons_long {r m : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes r) (hrm : r < m) :
    cycleDenominator (m + r) (m ::ₘ mu) = m * cycleDenominator r mu := by
  have hmnot : m ∉ mu := not_mem_cycleType_of_sum_lt hmu hrm
  have hsum : mu.sum ≤ r := (mem_cycleTypes.mp hmu).1
  have hcountm : mu.count m = 0 := Multiset.count_eq_zero.mpr hmnot
  simp only [cycleDenominator, Multiset.sum_cons, Multiset.prod_cons,
    Multiset.toFinset_cons]
  have hfixed : m + r - (m + mu.sum) = r - mu.sum := by omega
  rw [hfixed]
  have hcounts :
      ∏ j ∈ mu.toFinset, (Multiset.count j (m ::ₘ mu)).factorial =
        ∏ j ∈ mu.toFinset, (mu.count j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    have hjne : j ≠ m := by
      intro hjm
      subst j
      exact hmnot (Multiset.mem_toFinset.mp hj)
    simp [hjne]
  rw [Finset.prod_insert (by simpa using hmnot)]
  rw [Multiset.count_cons_self, hcountm]
  norm_num only [Nat.factorial_zero, Nat.factorial_one, one_mul]
  rw [hcounts]
  ac_rfl

/-- Weight factorization for a distinguished long cycle. -/
theorem cycleWeight_cons_long {r m : ℕ} {mu : Multiset ℕ}
    (hmu : mu ∈ cycleTypes r) (hrm : r < m) :
    cycleWeight (m + r) (m ::ₘ mu) = (1 / (m : ℚ)) * cycleWeight r mu := by
  rw [cycleWeight, cycleWeight, cycleDenominator_cons_long hmu hrm,
    Nat.cast_mul]
  field_simp

/-- Adding a fixed element to a multiset, as a finite-set embedding. -/
def consMultisetEmbedding (m : ℕ) : Multiset ℕ ↪ Multiset ℕ where
  toFun mu := m ::ₘ mu
  inj' := fun _ _ h ↦ (Multiset.cons_inj_right m).mp h

/-- All occurring cycle types which contain a cycle of the specified
length, with no condition on the order of the permutation. -/
def localCycleTypesContaining (n q : ℕ) : Finset (Multiset ℕ) :=
  (cycleTypes n).filter fun mu ↦ q ∈ mu

@[simp] theorem mem_localCycleTypesContaining {n q : ℕ} {mu : Multiset ℕ} :
    mu ∈ localCycleTypesContaining n q ↔ mu ∈ cycleTypes n ∧ q ∈ mu := by
  simp [localCycleTypesContaining]

/-- If `q` exceeds the size of the residual permutation, a type containing
`q` contains it exactly once and is uniquely obtained by adjoining `q` to a
type on the residual letters. -/
theorem localCycleTypesContaining_eq_map_cons {t q : ℕ} (hq : 2 ≤ q) (htq : t < q) :
    localCycleTypesContaining (q + t) q =
      (cycleTypes t).map (consMultisetEmbedding q) := by
  classical
  ext nu
  constructor
  · intro hnu
    rw [mem_localCycleTypesContaining] at hnu
    let mu := nu.erase q
    have hcons : q ::ₘ mu = nu := Multiset.cons_erase hnu.2
    have hmu : mu ∈ cycleTypes t := by
      apply mem_cycleTypes.mpr
      constructor
      · have hsum := (mem_cycleTypes.mp hnu.1).1
        rw [← hcons, Multiset.sum_cons] at hsum
        omega
      · intro a ha
        exact (mem_cycleTypes.mp hnu.1).2 a (Multiset.mem_of_mem_erase ha)
    rw [Finset.mem_map]
    exact ⟨mu, hmu, hcons⟩
  · rw [Finset.mem_map]
    rintro ⟨mu, hmu, rfl⟩
    change q ::ₘ mu ∈ localCycleTypesContaining (q + t) q
    rw [mem_localCycleTypesContaining]
    have hmuData := mem_cycleTypes.mp hmu
    refine ⟨mem_cycleTypes.mpr ?_, Multiset.mem_cons_self q mu⟩
    constructor
    · simpa only [Multiset.sum_cons] using Nat.add_le_add_left hmuData.1 q
    · intro a ha
      rcases Multiset.mem_cons.mp ha with rfl | ha
      · exact hq
      · exact hmuData.2 a ha

/-- Exact probability of having a `q`-cycle when `q` is more than half of
the degree. -/
theorem sum_localCycleTypesContaining_cycleWeight {t q : ℕ} (hq : 2 ≤ q)
    (htq : t < q) :
    ∑ mu ∈ localCycleTypesContaining (q + t) q, cycleWeight (q + t) mu =
      1 / (q : ℚ) := by
  classical
  rw [localCycleTypesContaining_eq_map_cons hq htq, Finset.sum_map]
  change (cycleTypes t).sum
      (fun mu ↦ cycleWeight (q + t) (q ::ₘ mu)) = 1 / (q : ℚ)
  calc
    _ = ∑ mu ∈ cycleTypes t, (1 / (q : ℚ)) * cycleWeight t mu := by
      apply Finset.sum_congr rfl
      intro mu hmu
      exact cycleWeight_cons_long hmu htq
    _ = 1 / (q : ℚ) := by
      rw [← Finset.mul_sum, sum_cycleWeight]
      simp

/-- The largest power of two not exceeding `r`. -/
def binaryScale (r : ℕ) : ℕ := 2 ^ Nat.log 2 r

theorem binaryScale_le {r : ℕ} (hr : 0 < r) : binaryScale r ≤ r := by
  exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hr)

theorem lt_two_mul_binaryScale (r : ℕ) : r < 2 * binaryScale r := by
  simpa [binaryScale, pow_succ'] using Nat.lt_pow_succ_log_self (b := 2) (by omega) r

theorem two_le_binaryScale {r : ℕ} (hr : 2 ≤ r) : 2 ≤ binaryScale r := by
  have hlog : 1 ≤ Nat.log 2 r :=
    Nat.le_log_of_pow_le (by omega) (by simpa using hr)
  simpa [binaryScale] using (Nat.pow_le_pow_right (by omega : 0 < 2) hlog)

/-- Specialization of the long-cycle occurrence identity to the largest
power of two below `r`.  This is the exact residual probability used by the
two-half-cycle correction. -/
theorem sum_localCycleTypesContaining_binaryScale {r : ℕ} (hr : 2 ≤ r) :
    ∑ mu ∈ localCycleTypesContaining r (binaryScale r), cycleWeight r mu =
      1 / (binaryScale r : ℚ) := by
  have hqle : binaryScale r ≤ r := binaryScale_le (by omega)
  have htq : r - binaryScale r < binaryScale r := by
    have := lt_two_mul_binaryScale r
    omega
  have h := sum_localCycleTypesContaining_cycleWeight
    (q := binaryScale r) (t := r - binaryScale r) (two_le_binaryScale hr) htq
  rwa [Nat.add_sub_of_le hqle] at h

/-- For an admissible complement `m` with `r < m`, the order-`m` types
containing an `m`-cycle are exactly the types obtained by adjoining `m` to
an arbitrary residual type on `r` letters. -/
theorem longOrderCycleTypes_eq_map_cons {r m : ℕ} (hm : 2 ≤ m)
    (hrm : r < m) (hadm : Nat.lcmUpto r ∣ m) :
    longOrderCycleTypes (m + r) m =
      (cycleTypes r).map (consMultisetEmbedding m) := by
  classical
  ext nu
  constructor
  · intro hnu
    rw [mem_longOrderCycleTypes] at hnu
    let mu := nu.erase m
    have hcons : m ::ₘ mu = nu := Multiset.cons_erase hnu.2.2
    have hmu : mu ∈ cycleTypes r := by
      rw [mem_cycleTypes]
      constructor
      · have hsum := (mem_cycleTypes.mp hnu.1).1
        rw [← hcons, Multiset.sum_cons] at hsum
        omega
      · intro a ha
        exact (mem_cycleTypes.mp hnu.1).2 a (Multiset.mem_of_mem_erase ha)
    rw [Finset.mem_map]
    exact ⟨mu, hmu, hcons⟩
  · rw [Finset.mem_map]
    rintro ⟨mu, hmu, rfl⟩
    change m ::ₘ mu ∈ longOrderCycleTypes (m + r) m
    rw [mem_longOrderCycleTypes]
    have hmuData := mem_cycleTypes.mp hmu
    have hlcmdvd : mu.lcm ∣ m := by
      rw [Multiset.lcm_dvd]
      intro a ha
      have haleSum : a ≤ mu.sum := by
        have hsum := congrArg Multiset.sum (Multiset.cons_erase ha)
        calc
          a ≤ a + (mu.erase a).sum := Nat.le_add_right _ _
          _ = mu.sum := by simpa only [Multiset.sum_cons] using hsum
      have hale : a ≤ r := haleSum.trans hmuData.1
      exact (Nat.dvd_lcmUpto (by have := hmuData.2 a ha; omega) hale).trans hadm
    refine ⟨mem_cycleTypes.mpr ?_, ?_, Multiset.mem_cons_self m mu⟩
    · constructor
      · simpa only [Multiset.sum_cons] using Nat.add_le_add_left hmuData.1 m
      · intro a ha
        rcases Multiset.mem_cons.mp ha with rfl | ha
        · exact hm
        · exact hmuData.2 a ha
    · simpa only [Multiset.lcm_cons] using
        (lcm_eq_left_iff m mu.lcm (by simp)).2 hlcmdvd

/-- The distinguished-long-cycle part of the exact cycle-index sum is
exactly `1/m`.  This is the formal version of the first term in Beker's
Proposition 4.1. -/
theorem sum_longOrderCycleTypes_cycleWeight {r m : ℕ} (hm : 2 ≤ m)
    (hrm : r < m) (hadm : Nat.lcmUpto r ∣ m) :
    ∑ mu ∈ longOrderCycleTypes (m + r) m, cycleWeight (m + r) mu =
      1 / (m : ℚ) := by
  classical
  rw [longOrderCycleTypes_eq_map_cons hm hrm hadm, Finset.sum_map]
  change (cycleTypes r).sum
      (fun mu ↦ cycleWeight (m + r) (m ::ₘ mu)) = 1 / (m : ℚ)
  calc
    _ = ∑ mu ∈ cycleTypes r, (1 / (m : ℚ)) * cycleWeight r mu := by
      apply Finset.sum_congr rfl
      intro mu hmu
      exact cycleWeight_cons_long hmu hrm
    _ = 1 / (m : ℚ) := by
      rw [← Finset.mul_sum, sum_cycleWeight]
      simp

/-- The complementary order-`m` types, containing no `m`-cycle. -/
def nonLongOrderCycleTypes (n m : ℕ) : Finset (Multiset ℕ) :=
  (orderCycleTypes n m).filter fun mu ↦ m ∉ mu

/-- The exact rational contribution of order-`m` permutations without an
`m`-cycle.  It is a finite cycle-index sum, not an asymptotic abbreviation. -/
noncomputable def nonLongCycleContribution (n m : ℕ) : ℚ :=
  ∑ mu ∈ nonLongOrderCycleTypes n m, cycleWeight n mu

/-- Exact finite decomposition into the long-cycle main term and all other
cycle types. -/
theorem orderCountRationalProbability_eq_one_div_add_nonLong
    {r m : ℕ} (hm : 2 ≤ m) (hrm : r < m)
    (hadm : Nat.lcmUpto r ∣ m) :
    (orderCount (m + r) m : ℚ) / ((m + r).factorial : ℚ) =
      1 / (m : ℚ) + nonLongCycleContribution (m + r) m := by
  rw [orderCountRationalProbability_eq_sum_cycleWeight,
    ← sum_longOrderCycleTypes_cycleWeight hm hrm hadm]
  unfold nonLongCycleContribution longOrderCycleTypes nonLongOrderCycleTypes
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not (orderCycleTypes (m + r) m)
      (fun mu ↦ m ∈ mu) (cycleWeight (m + r))).symm

/-- Every term of the exact non-long-cycle remainder is nonnegative. -/
theorem nonLongCycleContribution_nonneg (n m : ℕ) :
    0 ≤ nonLongCycleContribution n m := by
  unfold nonLongCycleContribution
  apply Finset.sum_nonneg
  intro mu hmu
  unfold cycleWeight
  positivity

/-- Real-valued form of the exact long/non-long decomposition, matching the
`orderProbability` convention in `Basic.lean`. -/
theorem orderProbability_eq_one_div_add_nonLong
    {r m : ℕ} (hm : 2 ≤ m) (hrm : r < m)
    (hadm : Nat.lcmUpto r ∣ m) :
    orderProbability (m + r) m =
      1 / (m : ℝ) + (nonLongCycleContribution (m + r) m : ℝ) := by
  have h := orderCountRationalProbability_eq_one_div_add_nonLong hm hrm hadm
  have hreal := congrArg (fun x : ℚ ↦ (x : ℝ)) h
  simpa [orderProbability] using hreal


/-- Beker's exceptional contribution from two cycles of length `(n-r)/2`.

The alternative form `2 / (2 ^ log₂ r * (n-r)²)` avoids integer subtraction
in the exponent `1 - log₂ r`.  The two forms are equal over the reals.
-/
noncomputable def halfCycleCorrection (n r : ℕ) : ℝ :=
  if r ≤ 1 ∨ 2 ^ (Nat.log 2 r + 1) ∣ n - r then 0
  else 2 / (((2 ^ Nat.log 2 r : ℕ) : ℝ) * ((n - r : ℕ) : ℝ) ^ 2)

/-- The local main term together with the possible two-half-cycle term. -/
noncomputable def localMainTerm (n r : ℕ) : ℝ :=
  1 / ((n - r : ℕ) : ℝ) + halfCycleCorrection n r

theorem halfCycleCorrection_of_le_one {n r : ℕ} (hr : r ≤ 1) :
    halfCycleCorrection n r = 0 := by
  simp [halfCycleCorrection, hr]

theorem halfCycleCorrection_of_next_two_pow_dvd {n r : ℕ}
    (hdiv : 2 ^ (Nat.log 2 r + 1) ∣ n - r) :
    halfCycleCorrection n r = 0 := by
  simp [halfCycleCorrection, hdiv]

/-- Explicit nonzero branch of the exceptional correction, in terms of the
largest power of two below `r`. -/
theorem halfCycleCorrection_eq_two_div {n r : ℕ} (hr : 2 ≤ r)
    (hnext : ¬2 * binaryScale r ∣ n - r) :
    halfCycleCorrection n r =
      2 / ((binaryScale r : ℝ) * ((n - r : ℕ) : ℝ) ^ 2) := by
  rw [halfCycleCorrection]
  split_ifs with h
  · rcases h with hsmall | hdiv
    · omega
    · exact (hnext (by simpa [binaryScale, pow_succ', mul_comm] using hdiv)).elim
  · rfl

theorem halfCycleCorrection_nonneg (n r : ℕ) :
    0 ≤ halfCycleCorrection n r := by
  rw [halfCycleCorrection]
  split_ifs
  · exact le_rfl
  · positivity

theorem halfCycleCorrection_le_inv_sq {n r : ℕ} (hr : 2 ≤ r) :
    halfCycleCorrection n r ≤ 1 / ((n - r : ℕ) : ℝ) ^ 2 := by
  rw [halfCycleCorrection]
  split_ifs with h
  · positivity
  · have hlog : 1 ≤ Nat.log 2 r :=
      Nat.le_log_of_pow_le (by omega) (by simpa using hr)
    have hpowNat : 2 ≤ 2 ^ Nat.log 2 r := by
      simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) hlog)
    have hpow : (2 : ℝ) ≤ ((2 ^ Nat.log 2 r : ℕ) : ℝ) := by
      exact_mod_cast hpowNat
    have hden : 0 ≤ ((n - r : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have hmul : 2 * ((n - r : ℕ) : ℝ) ^ 2 ≤
        ((2 ^ Nat.log 2 r : ℕ) : ℝ) * ((n - r : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hpow hden
    by_cases hm : n - r = 0
    · simp [hm]
    · have hm' : (0 : ℝ) < ((n - r : ℕ) : ℝ) := by
        exact_mod_cast (Nat.pos_of_ne_zero hm)
      apply (div_le_iff₀ (mul_pos (by positivity)
        (sq_pos_of_pos hm'))).2
      field_simp
      nlinarith

/-- The exceptional term is at most `1/m²` for a positive complementary
length `m = n-r`. -/
theorem halfCycleCorrection_le_one_div_sq {n r : ℕ} (hr : 2 ≤ r)
    (_hrn : r < n) :
    halfCycleCorrection n r ≤ 1 / ((((n - r : ℕ) : ℝ)) ^ 2) :=
  halfCycleCorrection_le_inv_sq hr

/-- Admissibility at a larger remainder implies that the smaller
least-common multiple also divides its complementary length. -/
theorem lcmUpto_dvd_complement_of_le {n r s : ℕ} (hrs : r ≤ s)
    (hs : Nat.lcmUpto s ∣ n - s) :
    Nat.lcmUpto r ∣ n - s :=
  (Nat.lcmUpto_mono_dvd hrs).trans hs

/-- Two admissible remainders differ by a multiple of the smaller
`lcmUpto`. -/
theorem lcmUpto_dvd_remainder_sub {n r s : ℕ} (hrs : r ≤ s)
    (hsn : s ≤ n) (hr : Nat.lcmUpto r ∣ n - r)
    (hs : Nat.lcmUpto s ∣ n - s) :
    Nat.lcmUpto r ∣ s - r := by
  have hs' : Nat.lcmUpto r ∣ n - s :=
    lcmUpto_dvd_complement_of_le hrs hs
  have hadd : (n - s) + (s - r) = n - r := by omega
  apply (Nat.dvd_add_iff_right hs').mpr
  rw [hadd]
  exact hr

/-- For `r ≥ 2`, distinct admissible remainders differ by at least two.
This is the arithmetic input that beats the half-cycle correction. -/
theorem two_le_remainder_sub_of_admissible {n r s : ℕ} (hrtwo : 2 ≤ r)
    (hrs : r < s) (hsn : s < n) (hr : Nat.lcmUpto r ∣ n - r)
    (hs : Nat.lcmUpto s ∣ n - s) :
    2 ≤ s - r := by
  have hr_dvd_lcm : r ∣ Nat.lcmUpto r :=
    Nat.dvd_lcmUpto (by omega) le_rfl
  have hr_dvd : r ∣ s - r := hr_dvd_lcm.trans <|
    lcmUpto_dvd_remainder_sub hrs.le hsn.le hr hs
  exact hrtwo.trans (Nat.le_of_dvd (Nat.sub_pos_of_lt hrs) hr_dvd)

/-- Quantitative separation of two local model masses.  The lower bound
`1/(n-r)²` is uniform in the two admissible remainders and is what absorbs
the `o(n⁻²)` cycle-index error. -/
theorem one_div_sq_lt_localMainTerm_sub_of_admissible {n r s : ℕ} (hrs : r < s)
    (hsn : s < n) (hr : Nat.lcmUpto r ∣ n - r)
    (hs : Nat.lcmUpto s ∣ n - s) :
    1 / ((n - r : ℕ) : ℝ) ^ 2 < localMainTerm n s - localMainTerm n r := by
  have hmr : (0 : ℝ) < ((n - r : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (hrs.trans hsn))
  have hms : (0 : ℝ) < ((n - s : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hsn)
  have hms_lt_hmr : ((n - s : ℕ) : ℝ) < ((n - r : ℕ) : ℝ) := by
    exact_mod_cast (by omega : n - s < n - r)
  rcases lt_or_ge r 2 with hrsmall | hrlarge
  · have heta : halfCycleCorrection n r = 0 :=
      halfCycleCorrection_of_le_one (by omega)
    have hetas := halfCycleCorrection_nonneg n s
    have hdiff : 1 ≤ s - r := Nat.one_le_iff_ne_zero.mpr (by omega)
    have hdiffReal : (1 : ℝ) ≤ ((s - r : ℕ) : ℝ) := by exact_mod_cast hdiff
    have hid :
        1 / ((n - s : ℕ) : ℝ) - 1 / ((n - r : ℕ) : ℝ) =
          ((s - r : ℕ) : ℝ) /
            (((n - s : ℕ) : ℝ) * ((n - r : ℕ) : ℝ)) := by
      field_simp
      norm_num [Nat.cast_sub hrs.le, Nat.cast_sub hsn.le,
        Nat.cast_sub (hrs.trans hsn).le]
    have hmain :
        1 / (((n - s : ℕ) : ℝ) * ((n - r : ℕ) : ℝ)) ≤
          1 / ((n - s : ℕ) : ℝ) - 1 / ((n - r : ℕ) : ℝ) := by
      rw [hid]
      exact div_le_div_of_nonneg_right hdiffReal (mul_nonneg hms.le hmr.le)
    have hbeat :
        1 / ((n - r : ℕ) : ℝ) ^ 2 <
          1 / (((n - s : ℕ) : ℝ) * ((n - r : ℕ) : ℝ)) := by
      apply (div_lt_div_iff₀ (sq_pos_of_pos hmr) (mul_pos hms hmr)).2
      nlinarith
    rw [localMainTerm, localMainTerm, heta]
    linarith
  · have hdiff : 2 ≤ s - r :=
      two_le_remainder_sub_of_admissible hrlarge hrs hsn hr hs
    have heta_r := halfCycleCorrection_le_inv_sq (n := n) hrlarge
    have heta_s := halfCycleCorrection_nonneg n s
    have hmain :
        2 / (((n - s : ℕ) : ℝ) * ((n - r : ℕ) : ℝ)) ≤
          1 / ((n - s : ℕ) : ℝ) - 1 / ((n - r : ℕ) : ℝ) := by
      have hdiffReal : (2 : ℝ) ≤ ((s - r : ℕ) : ℝ) := by exact_mod_cast hdiff
      have hid :
          1 / ((n - s : ℕ) : ℝ) - 1 / ((n - r : ℕ) : ℝ) =
            ((s - r : ℕ) : ℝ) /
              (((n - s : ℕ) : ℝ) * ((n - r : ℕ) : ℝ)) := by
        field_simp
        norm_num [Nat.cast_sub hrs.le, Nat.cast_sub hsn.le,
          Nat.cast_sub (hrs.trans hsn).le]
      rw [hid]
      exact div_le_div_of_nonneg_right hdiffReal (mul_nonneg hms.le hmr.le)
    have hbeat :
        2 / ((n - r : ℕ) : ℝ) ^ 2 <
          2 / (((n - s : ℕ) : ℝ) * ((n - r : ℕ) : ℝ)) := by
      apply (div_lt_div_iff₀ (sq_pos_of_pos hmr) (mul_pos hms hmr)).2
      nlinarith
    have hmain2 :
        2 / ((n - r : ℕ) : ℝ) ^ 2 <
          1 / ((n - s : ℕ) : ℝ) - 1 / ((n - r : ℕ) : ℝ) :=
      hbeat.trans_le hmain
    have htwo :
        2 / ((n - r : ℕ) : ℝ) ^ 2 =
          2 * (1 / ((n - r : ℕ) : ℝ) ^ 2) := by ring
    rw [htwo] at hmain2
    rw [localMainTerm, localMainTerm]
    calc
      1 / ((n - r : ℕ) : ℝ) ^ 2 <
          (1 / ((n - s : ℕ) : ℝ) - 1 / ((n - r : ℕ) : ℝ)) -
            halfCycleCorrection n r := by linarith
      _ ≤ 1 / ((n - s : ℕ) : ℝ) + halfCycleCorrection n s -
          (1 / ((n - r : ℕ) : ℝ) + halfCycleCorrection n r) := by linarith

/-- The model local mass is strictly largest at the largest admissible
remainder.  This is the qualitative corollary of the quantitative gap. -/
theorem localMainTerm_lt_of_admissible {n r s : ℕ} (hrs : r < s)
    (hsn : s < n) (hr : Nat.lcmUpto r ∣ n - r)
    (hs : Nat.lcmUpto s ∣ n - s) :
    localMainTerm n r < localMainTerm n s := by
  have hgap := one_div_sq_lt_localMainTerm_sub_of_admissible hrs hsn hr hs
  have hrempos : (0 : ℝ) < ((n - r : ℕ) : ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (hrs.trans hsn))
  have hpos : 0 < 1 / ((n - r : ℕ) : ℝ) ^ 2 := by
    positivity
  linarith

/-- A quantified, Lean-friendly formulation of the uniform local expansion.
The cutoff `N` and error numerator `e n` are integers-free; an eventual bound
`n² e n → 0` is precisely what the final comparison needs. -/
def HasUniformLocalExpansion (p : ℕ → ℕ → ℝ) : Prop :=
  ∃ e : ℕ → ℝ,
    (∀ n, 0 ≤ e n) ∧
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ 2 * e n) atTop (nhds 0) ∧
      ∀ᶠ n in atTop, ∀ r, r < n → Nat.lcmUpto r ∣ n - r →
        |p n (n - r) - localMainTerm n r| ≤ e n

/-- Any family with Beker's uniform local expansion is eventually strictly
increasing along the admissible remainders.  This theorem is entirely
quantitative: it is the bridge from the cycle-index error estimate to the
unique-mode comparison. -/
theorem eventually_strictOn_admissible_of_hasUniformLocalExpansion
    {p : ℕ → ℕ → ℝ} (hp : HasUniformLocalExpansion p) :
    ∀ᶠ n : ℕ in atTop, ∀ r s : ℕ,
      r < s → s < n →
      Nat.lcmUpto r ∣ n - r → Nat.lcmUpto s ∣ n - s →
      p n (n - r) < p n (n - s) := by
  rcases hp with ⟨e, he_nonneg, he_zero, he_bound⟩
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp he_zero) (1 / 4) (by norm_num)
  filter_upwards [he_bound, Filter.eventually_ge_atTop N,
    Filter.eventually_gt_atTop 0] with n hn hNn hnpos
  intro r s hrs hsn hr hs
  have herror_r := hn r (hrs.trans hsn) hr
  have herror_s := hn s hsn hs
  have hscaled : (n : ℝ) ^ 2 * e n < 1 / 4 := by
    have hd := hN n hNn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (he_nonneg n))] at hd
    exact hd
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have htwice : 2 * e n < 1 / (n : ℝ) ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hnreal)).2
    nlinarith
  have hrempos : (0 : ℝ) < (n - r : ℕ) := by
    exact_mod_cast (Nat.sub_pos_of_lt (hrs.trans hsn))
  have hremle : ((n - r : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n r
  have hinvle : 1 / (n : ℝ) ^ 2 ≤ 1 / ((n - r : ℕ) : ℝ) ^ 2 := by
    have hsq : ((n - r : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      gcongr
    exact one_div_le_one_div_of_le (sq_pos_of_pos hrempos)
      hsq
  have hgap := one_div_sq_lt_localMainTerm_sub_of_admissible hrs hsn hr hs
  have hrside := (abs_le.mp herror_r).2
  have hsside := (abs_le.mp herror_s).1
  linarith

/-- The largest admissible remainder is consequently the unique local
maximizer.  This is the form consumed by the resolution glue after the
global structural theorem has excluded nonadmissible orders. -/
theorem eventually_largestAdmissibleRemainder_strictMax
    {p : ℕ → ℕ → ℝ} (hp : HasUniformLocalExpansion p) :
    ∀ᶠ n : ℕ in atTop, ∀ r ∈ admissibleRemainders n,
      r ≠ largestAdmissibleRemainder n →
      p n (n - r) <
        p n (n - largestAdmissibleRemainder n) := by
  filter_upwards [eventually_strictOn_admissible_of_hasUniformLocalExpansion hp,
    Filter.eventually_gt_atTop 0] with n hstrict hn
  intro r hr hrne
  have hsMem := largestAdmissibleRemainder_mem hn
  have hrData := mem_admissibleRemainders_iff.mp hr
  have hsData := mem_admissibleRemainders_iff.mp hsMem
  have hrs : r < largestAdmissibleRemainder n :=
    lt_of_le_of_ne (admissibleRemainder_le_largest hr) hrne
  exact hstrict r (largestAdmissibleRemainder n) hrs hsData.1 hrData.2 hsData.2

end Erdos1161
