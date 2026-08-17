/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos807.Parameters
import ErdosProblems.Erdos807.HostMoments
import ErdosProblems.Erdos807.FamilyCount

/-!
# Moderate-overlap estimates for the stable-slot witnesses

This file contains the analytic summation used for pairs of witnesses which
agree in between two and nine tenths of their slots.  The graph-specific
pair estimate is then derived from the stable edge-block API.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos807
namespace ModerateMoments

/-- The integral version of the usual moderate-overlap base.  The leading
factor `2` absorbs both the parity loss in replacing `(i-1)/2` by natural
division and the loss from the bucket size `n / k`. -/
noncomputable def moderateBase (n i : ℕ) : ℝ :=
  ((2 * structuredSize n ^ 2 * 2 ^ ((i - 1) / 2) : ℕ) : ℝ) / (n : ℝ)

/-- The normalized upper bound for the intersection-`i` stratum. -/
noncomputable def moderateTerm (n i : ℕ) : ℝ :=
  moderateBase n i ^ i

/-- Sum of all normalized moderate-overlap upper bounds. -/
noncomputable def moderateRelativeError (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 2 (9 * structuredSize n / 10), moderateTerm n i

theorem moderateBase_nonneg (n i : ℕ) : 0 ≤ moderateBase n i := by
  unfold moderateBase
  positivity

theorem moderateTerm_nonneg (n i : ℕ) : 0 ≤ moderateTerm n i := by
  exact pow_nonneg (moderateBase_nonneg n i) _

theorem moderateRelativeError_nonneg (n : ℕ) :
    0 ≤ moderateRelativeError n := by
  unfold moderateRelativeError
  exact Finset.sum_nonneg fun i _ ↦ moderateTerm_nonneg n i

/-- The power-only estimate from `Parameters` gives a uniform bound for each
moderate-overlap term. -/
theorem moderateTerm_le_rpow_of
    {n i : ℕ} (hn : 0 < n) (hi : 2 ≤ i)
    (hpow :
      (2 * structuredSize n ^ 2 * 2 ^ ((i - 1) / 2)) ^ 25 ≤ n ^ 24) :
    moderateTerm n i ≤ (n : ℝ) ^ (-(2 / 25 : ℝ)) := by
  exact div_pow_le_rpow_neg_two_div_twentyfive_of_pow_le hn hi hpow

/-- Every term in the moderate range obeys the same decaying bound,
eventually and uniformly in the intersection size. -/
theorem eventually_moderateTerm_le_rpow :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.Icc 2 (9 * structuredSize n / 10),
      moderateTerm n i ≤ (n : ℝ) ^ (-(2 / 25 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1,
    eventually_moderate_overlap_power_bound_with_two] with n hn hpow
  intro i hi
  have hi2 : 2 ≤ i := (Finset.mem_Icc.mp hi).1
  have hirange : 10 * i ≤ 9 * structuredSize n := by
    have hiupper := (Finset.mem_Icc.mp hi).2
    have hdiv := Nat.div_mul_le_self (9 * structuredSize n) 10
    omega
  exact moderateTerm_le_rpow_of (by omega) hi2 (hpow i hirange)

/-- The number of moderate intersection sizes is at most the structured
order. -/
theorem card_moderateRange_le (n : ℕ) :
    (Finset.Icc 2 (9 * structuredSize n / 10)).card ≤ structuredSize n := by
  simp only [Nat.card_Icc]
  omega

/-- Uniform termwise decay gives a clean bound for the whole moderate sum. -/
theorem eventually_moderateRelativeError_le :
    ∀ᶠ n : ℕ in atTop,
      moderateRelativeError n ≤
        (structuredSize n : ℝ) * (n : ℝ) ^ (-(2 / 25 : ℝ)) := by
  filter_upwards [eventually_moderateTerm_le_rpow] with n hn
  unfold moderateRelativeError
  calc
    (∑ i ∈ Finset.Icc 2 (9 * structuredSize n / 10), moderateTerm n i) ≤
        ∑ _i ∈ Finset.Icc 2 (9 * structuredSize n / 10),
          (n : ℝ) ^ (-(2 / 25 : ℝ)) := by
            exact Finset.sum_le_sum fun i hi ↦ hn i hi
    _ = ((Finset.Icc 2 (9 * structuredSize n / 10)).card : ℝ) *
          (n : ℝ) ^ (-(2 / 25 : ℝ)) := by simp
    _ ≤ (structuredSize n : ℝ) * (n : ℝ) ^ (-(2 / 25 : ℝ)) := by
      gcongr
      exact_mod_cast card_moderateRange_le n

/-- The complete normalized contribution of all moderate overlaps tends to
zero. -/
theorem tendsto_moderateRelativeError_zero :
    Tendsto moderateRelativeError atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall moderateRelativeError_nonneg
  · exact eventually_moderateRelativeError_le
  · exact tendsto_structuredSize_mul_rpow_neg_two_div_twentyfive

/-! ## Arithmetic normalization of a slot-overlap stratum -/

/-- Once every bucket has at least three points, the loss caused by flooring
the bucket size is smaller than a factor `sqrt 2`.  We record the squared
integer inequality, which avoids introducing square roots. -/
theorem bucket_square_bound {n k : ℕ} (hk : 0 < k) (hq : 3 ≤ n / k) :
    n ^ 2 ≤ 2 * (k * (n / k)) ^ 2 := by
  have hnlt : n < k * (n / k + 1) := by
    have h := Nat.lt_div_mul_add (a := n) (b := k) hk
    calc
      n < n / k * k + k := h
      _ = k * (n / k + 1) := by ring
  have hqsq : (n / k + 1) ^ 2 ≤ 2 * (n / k) ^ 2 := by
    nlinarith
  calc
    n ^ 2 ≤ (k * (n / k + 1)) ^ 2 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hnlt) 2
    _ = k ^ 2 * (n / k + 1) ^ 2 := by ring
    _ ≤ k ^ 2 * (2 * (n / k) ^ 2) := Nat.mul_le_mul_left _ hqsq
    _ = 2 * (k * (n / k)) ^ 2 := by ring

/-- Natural division loses at most one half in the exponent
`i(i-1)/2`.  Doubling the exponent makes the parity allowance integral. -/
theorem double_choose_two_le (i : ℕ) :
    2 * i.choose 2 ≤ i * (2 * ((i - 1) / 2) + 1) := by
  rw [Nat.choose_two_right]
  have hhalf := Nat.div_mul_le_self (i * (i - 1)) 2
  have hfloor := Nat.lt_div_mul_add (a := i - 1) (b := 2) (by norm_num)
  nlinarith

/-- The bucket-floor loss and the parity loss in `choose i 2` fit together
inside the single leading factor `2` in `moderateBase`.  This is the
division-free integer form of that fact. -/
theorem moderate_cleared_denominator_bound {n k i : ℕ}
    (hk : 0 < k) (hq : 3 ≤ n / k) :
    k ^ i * 2 ^ i.choose 2 * n ^ i ≤
      (2 * k ^ 2 * 2 ^ ((i - 1) / 2)) ^ i * (n / k) ^ i := by
  let q := n / k
  let a := (i - 1) / 2
  have hn2 : n ^ 2 ≤ 2 * (k * q) ^ 2 := by
    simpa only [q] using bucket_square_bound hk hq
  have hn2i : (n ^ i) ^ 2 ≤ (2 * (k * q) ^ 2) ^ i := by
    calc
      (n ^ i) ^ 2 = n ^ (i * 2) := (pow_mul n i 2).symm
      _ = n ^ (2 * i) := by congr 1 <;> omega
      _ = (n ^ 2) ^ i := pow_mul n 2 i
      _ ≤ (2 * (k * q) ^ 2) ^ i := Nat.pow_le_pow_left hn2 i
  have he : 2 * i.choose 2 ≤ i * (2 * a + 1) := by
    simpa only [a] using double_choose_two_le i
  have he2 : (2 ^ i.choose 2) ^ 2 ≤ (2 ^ (2 * a + 1)) ^ i := by
    calc
      (2 ^ i.choose 2) ^ 2 = 2 ^ (i.choose 2 * 2) := (pow_mul 2 _ 2).symm
      _ = 2 ^ (2 * i.choose 2) := by congr 1 <;> omega
      _ ≤ 2 ^ (i * (2 * a + 1)) := Nat.pow_le_pow_right (by norm_num) he
      _ = 2 ^ ((2 * a + 1) * i) := by rw [Nat.mul_comm i]
      _ = (2 ^ (2 * a + 1)) ^ i := pow_mul 2 _ i
  have hsquare :
      (k ^ i * 2 ^ i.choose 2 * n ^ i) ^ 2 ≤
        ((2 * k ^ 2 * 2 ^ a) ^ i * q ^ i) ^ 2 := by
    calc
      (k ^ i * 2 ^ i.choose 2 * n ^ i) ^ 2 =
          (k ^ i) ^ 2 * (2 ^ i.choose 2) ^ 2 * (n ^ i) ^ 2 := by ring
      _ ≤ (k ^ i) ^ 2 * (2 ^ (2 * a + 1)) ^ i *
          (2 * (k * q) ^ 2) ^ i := by gcongr
      _ = ((2 * k ^ 2 * 2 ^ a) ^ i * q ^ i) ^ 2 := by
        simp only [mul_pow, pow_succ]
        ring
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsquare

/-- Extract the shared-edge factor from the two-copy probability. -/
theorem half_pow_union_identity {k i : ℕ} (hi : i ≤ k) :
    (1 / 2 : ℝ) ^ (2 * k.choose 2 - i.choose 2) =
      ((1 / 2 : ℝ) ^ k.choose 2) ^ 2 * (2 : ℝ) ^ i.choose 2 := by
  have hchoose : i.choose 2 ≤ k.choose 2 := Nat.choose_le_choose 2 hi
  have hsub : 2 * k.choose 2 - i.choose 2 + i.choose 2 = 2 * k.choose 2 :=
    Nat.sub_add_cancel (hchoose.trans (Nat.le_mul_of_pos_left _ (by norm_num)))
  have hpow : (2 : ℝ) ^ (2 * k.choose 2) =
      (2 : ℝ) ^ (2 * k.choose 2 - i.choose 2) * (2 : ℝ) ^ i.choose 2 := by
    rw [← pow_add, hsub]
  have hsq : ((2 : ℝ) ^ k.choose 2) ^ 2 = (2 : ℝ) ^ (2 * k.choose 2) := by
    calc
      ((2 : ℝ) ^ k.choose 2) ^ 2 = (2 : ℝ) ^ (k.choose 2 * 2) :=
        (pow_mul 2 _ 2).symm
      _ = (2 : ℝ) ^ (2 * k.choose 2) := by rw [Nat.mul_comm]
  simp only [one_div, inv_pow]
  rw [hsq, hpow]
  field_simp

/-- The complete combinatorial part of the normalized stratum estimate,
with the ambient denominator cleared. -/
theorem slot_combinatorial_cleared_bound {n k i : ℕ}
    (hk : 0 < k) (hq : 3 ≤ n / k) (hi : i ≤ k) :
    ((n / k) ^ k *
        (k.choose i * ((n / k) - 1) ^ (k - i)) * 2 ^ i.choose 2) * n ^ i ≤
      (n / k) ^ (2 * k) *
        (2 * k ^ 2 * 2 ^ ((i - 1) / 2)) ^ i := by
  let q := n / k
  let A := 2 * k ^ 2 * 2 ^ ((i - 1) / 2)
  have hchoose : k.choose i ≤ k ^ i := Nat.choose_le_pow k i
  have hqpow : (q - 1) ^ (k - i) ≤ q ^ (k - i) :=
    Nat.pow_le_pow_left (Nat.sub_le q 1) _
  have hcore : k ^ i * 2 ^ i.choose 2 * n ^ i ≤ A ^ i * q ^ i := by
    simpa only [q, A] using moderate_cleared_denominator_bound hk hq
  calc
    (q ^ k * (k.choose i * (q - 1) ^ (k - i)) * 2 ^ i.choose 2) * n ^ i ≤
        (q ^ k * (k ^ i * q ^ (k - i)) * 2 ^ i.choose 2) * n ^ i := by
      gcongr
    _ = q ^ k * q ^ (k - i) * (k ^ i * 2 ^ i.choose 2 * n ^ i) := by ring
    _ ≤ q ^ k * q ^ (k - i) * (A ^ i * q ^ i) := by gcongr
    _ = A ^ i * (q ^ k * q ^ (k - i) * q ^ i) := by ring
    _ = A ^ i * q ^ (k + (k - i) + i) := by rw [pow_add, pow_add]
    _ = q ^ (2 * k) * A ^ i := by
      have hexp : k + (k - i) + i = 2 * k := by omega
      rw [hexp]
      ring

/-- Real normalized form of `slot_combinatorial_cleared_bound`. -/
theorem slot_combinatorial_normalized_bound {n k i : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hq : 3 ≤ n / k) (hi : i ≤ k) :
    (((n / k) ^ k *
        (k.choose i * ((n / k) - 1) ^ (k - i)) * 2 ^ i.choose 2 : ℕ) : ℝ) ≤
      (((n / k) ^ (2 * k) : ℕ) : ℝ) *
        (((2 * k ^ 2 * 2 ^ ((i - 1) / 2) : ℕ) : ℝ) / (n : ℝ)) ^ i := by
  rw [div_pow]
  rw [← mul_div_assoc,
    le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ i)]
  push_cast
  exact_mod_cast slot_combinatorial_cleared_bound hk hq hi

/-! ## Graph-specific normalized contribution -/

/-- A moderate base with an arbitrary template order. -/
noncomputable def slotModerateBase (n k i : ℕ) : ℝ :=
  ((2 * k ^ 2 * 2 ^ ((i - 1) / 2) : ℕ) : ℝ) / (n : ℝ)

/-- The exact crude pair estimate from `HostMoments`, normalized by the
square of the exact first moment. -/
theorem hostIntersectionContribution_le_mean_sq_mul
    {n r i : ℕ} (hn : 0 < n) (hr : 0 < r)
    (hq : 3 ≤ HostFamily.bucketSize n r)
    (hi : i ≤ HostFamily.templateOrder r) :
    HostMoments.hostIntersectionContribution n r i ≤
      (FiniteUniform.natExpectation (HostFamily.witnessCount n r)) ^ 2 *
        slotModerateBase n (HostFamily.templateOrder r) i ^ i := by
  let k := HostFamily.templateOrder r
  let q := HostFamily.bucketSize n r
  let F : ℝ := (2 ^ (90 * r * r) : ℕ)
  let t : ℝ := (1 / 2 : ℝ) ^ k.choose 2
  let A : ℝ := ((2 * k ^ 2 * 2 ^ ((i - 1) / 2) : ℕ) : ℝ) / (n : ℝ)
  have hk : 0 < k := by simp [k, HostFamily.templateOrder, hr]
  have hcomb :
      ((q ^ k * (k.choose i * (q - 1) ^ (k - i)) * 2 ^ i.choose 2 : ℕ) : ℝ) ≤
        ((q ^ (2 * k) : ℕ) : ℝ) * A ^ i := by
    simpa only [q, k, HostFamily.bucketSize, A] using
      slot_combinatorial_normalized_bound hn hk hq hi
  have hhalf := half_pow_union_identity hi
  calc
    HostMoments.hostIntersectionContribution n r i ≤
        (q ^ k * (k.choose i * (q - 1) ^ (k - i)) : ℕ) *
          ((2 ^ (90 * r * r) : ℕ) ^ 2 *
            (1 / 2 : ℝ) ^ (2 * k.choose 2 - i.choose 2)) := by
      simpa only [q, k] using HostMoments.hostIntersectionContribution_le_crude n r i
    _ = F ^ 2 * t ^ 2 *
          ((q ^ k * (k.choose i * (q - 1) ^ (k - i)) *
            2 ^ i.choose 2 : ℕ) : ℝ) := by
      rw [hhalf]
      push_cast
      simp only [F, t, k, HostFamily.templateOrder, Nat.cast_pow]
      ring_nf
    _ ≤ F ^ 2 * t ^ 2 * (((q ^ (2 * k) : ℕ) : ℝ) * A ^ i) := by
      gcongr
    _ = (FiniteUniform.natExpectation (HostFamily.witnessCount n r)) ^ 2 *
          slotModerateBase n k i ^ i := by
      rw [HostMoments.natExpectation_host_witnessCount]
      simp only [q, k, F, t, A, slotModerateBase]
      push_cast
      rw [show (q : ℝ) ^ (2 * k) = ((q : ℝ) ^ k) ^ 2 by
        calc
          (q : ℝ) ^ (2 * k) = (q : ℝ) ^ (k * 2) := by rw [Nat.mul_comm]
          _ = ((q : ℝ) ^ k) ^ 2 := pow_mul _ k 2]
      ring

/-- Specialization to the rounded ABH parameters. -/
theorem hostIntersectionContribution_le_mean_sq_mul_moderateTerm
    {n i : ℕ} (hn : 0 < n) (hr : 0 < blockCount n)
    (hq : 3 ≤ HostFamily.bucketSize n (blockCount n))
    (hi : i ≤ structuredSize n) :
    HostMoments.hostIntersectionContribution n (blockCount n) i ≤
      (FiniteUniform.natExpectation
          (HostFamily.witnessCount n (blockCount n))) ^ 2 *
        moderateTerm n i := by
  have hi' : i ≤ HostFamily.templateOrder (blockCount n) := by
    simpa [HostFamily.templateOrder, structuredSize_eq_mul_blockCount] using hi
  simpa [moderateTerm, moderateBase, slotModerateBase,
    HostFamily.templateOrder, structuredSize_eq_mul_blockCount] using
    hostIntersectionContribution_le_mean_sq_mul hn hr hq hi'


end ModerateMoments
end Erdos807
