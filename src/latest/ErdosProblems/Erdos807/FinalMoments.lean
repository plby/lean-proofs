/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos807.HostMoments
import ErdosProblems.Erdos807.ModerateMoments
import ErdosProblems.Erdos807.MomentRanges
import ErdosProblems.Erdos807.FamilyCount
import ErdosProblems.Erdos807.ABHSchema

/-!
# Completion of the stable-slot second-moment argument

This file normalizes the large-overlap contribution, combines all overlap
strata, and applies the finite Paley--Zygmund inequality to the canonical
host witness count.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos807
namespace FinalMoments

open Finset
open HostMoments

/-- The deliberately enlarged base used for the large-overlap stratum.
The exponent `2r + 9k/100 = 11r` dominates the exact `10r` extension code. -/
noncomputable def largeBase (n j : ℕ) : ℝ :=
  (((structuredSize n * n *
      2 ^ (2 * blockCount n + 9 * structuredSize n / 100) : ℕ) : ℝ) /
    ((2 ^ (structuredSize n - j) : ℕ) : ℝ))

/-- Normalized contribution assigned to choices differing in `j` slots. -/
noncomputable def largeTerm (n j : ℕ) : ℝ := largeBase n j ^ j

/-- Sum of the normalized large-overlap bounds. -/
noncomputable def largeRelativeError (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (structuredSize n / 10), largeTerm n j

theorem largeBase_nonneg (n j : ℕ) : 0 ≤ largeBase n j := by
  unfold largeBase
  positivity

theorem largeTerm_nonneg (n j : ℕ) : 0 ≤ largeTerm n j :=
  pow_nonneg (largeBase_nonneg n j) _

theorem largeRelativeError_nonneg (n : ℕ) : 0 ≤ largeRelativeError n := by
  unfold largeRelativeError
  exact Finset.sum_nonneg fun j _ ↦ largeTerm_nonneg n j

theorem eventually_largeTerm_le_rpow :
    ∀ᶠ n : ℕ in atTop, ∀ j ∈ Finset.Icc 1 (structuredSize n / 10),
      largeTerm n j ≤ (n : ℝ) ^ (-(2 / 5 : ℝ)) := by
  filter_upwards [eventually_large_overlap_ratio_bound] with n hn
  intro j hj
  have hjpos : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjrange : 10 * j ≤ structuredSize n := by
    have hu := (Finset.mem_Icc.mp hj).2
    have hd := Nat.div_mul_le_self (structuredSize n) 10
    omega
  exact hn j hjpos hjrange

theorem card_largeRange_le (n : ℕ) :
    (Finset.Icc 1 (structuredSize n / 10)).card ≤ structuredSize n := by
  simp only [Nat.card_Icc]
  omega

theorem eventually_largeRelativeError_le :
    ∀ᶠ n : ℕ in atTop,
      largeRelativeError n ≤
        (structuredSize n : ℝ) * (n : ℝ) ^ (-(2 / 5 : ℝ)) := by
  filter_upwards [eventually_largeTerm_le_rpow] with n hn
  unfold largeRelativeError
  calc
    (∑ j ∈ Finset.Icc 1 (structuredSize n / 10), largeTerm n j) ≤
        ∑ _j ∈ Finset.Icc 1 (structuredSize n / 10),
          (n : ℝ) ^ (-(2 / 5 : ℝ)) :=
      Finset.sum_le_sum fun j hj ↦ hn j hj
    _ = ((Finset.Icc 1 (structuredSize n / 10)).card : ℝ) *
          (n : ℝ) ^ (-(2 / 5 : ℝ)) := by simp
    _ ≤ (structuredSize n : ℝ) * (n : ℝ) ^ (-(2 / 5 : ℝ)) := by
      gcongr
      exact_mod_cast card_largeRange_le n

theorem tendsto_largeRelativeError_zero :
    Tendsto largeRelativeError atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall largeRelativeError_nonneg
  · exact eventually_largeRelativeError_le
  · exact tendsto_structuredSize_mul_rpow_neg_two_div_five

/-! ## First-moment identifications -/

/-- The probability-space expectation computed in `HostMoments` is the
closed slot first moment used by the parameter estimates. -/
theorem hostMean_eq_slotFirstMoment (n r : ℕ) :
    FiniteUniform.natExpectation (HostFamily.witnessCount n r) =
      FamilyCount.slotFirstMoment n r := by
  rw [HostMoments.natExpectation_host_witnessCount]
  unfold FamilyCount.slotFirstMoment HostFamily.bucketSize
  simp only [HostFamily.templateOrder, FamilyCount.structuredOrder,
    FamilyCount.bitCount, Nat.cast_pow]
  rw [one_div, inv_pow]
  ring_nf

/-- The `ABHSchema` and `FiniteUniform` presentations of the mean agree. -/
theorem uniformMean_eq_hostMean (n r : ℕ) :
    ABHSchema.uniformMean (HostFamily.witnessCount n r) =
      FiniteUniform.natExpectation (HostFamily.witnessCount n r) := rfl

/-- The `ABHSchema` and `FiniteUniform` presentations of the second moment
agree. -/
theorem uniformSecondMoment_eq_hostSecondMoment (n r : ℕ) :
    ABHSchema.uniformSecondMoment (HostFamily.witnessCount n r) =
      FiniteUniform.natSecondMoment (HostFamily.witnessCount n r) := rfl

/-! ## Arithmetic for a large-overlap stratum -/

theorem choose_two_sub_choose_two_ge_mul {k j : ℕ} (hj : j ≤ k) :
    (k - j) * j ≤ k.choose 2 - (k - j).choose 2 := by
  by_cases hjzero : j = 0
  · simp [hjzero]
  have hmono : (k - j).choose 2 ≤ k.choose 2 :=
    Nat.choose_le_choose 2 (Nat.sub_le k j)
  have hreal : (((k - j) * j : ℕ) : ℝ) ≤
      ((k.choose 2 - (k - j).choose 2 : ℕ) : ℝ) := by
    have hjreal : (j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hj
    have hjnonneg : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hjone : (1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hjzero)
    rw [Nat.cast_mul, Nat.cast_sub hmono, Nat.cast_choose_two,
      Nat.cast_choose_two, Nat.cast_sub hj]
    nlinarith
  exact_mod_cast hreal

theorem large_code_exponent_le_enlarged (n j : ℕ) :
    10 * blockCount n * j ≤
      (2 * blockCount n + 9 * structuredSize n / 100) * j := by
  apply Nat.mul_le_mul_right j
  rw [structuredSize_eq_mul_blockCount]
  have hdiv : 9 * (100 * blockCount n) / 100 = 9 * blockCount n := by
    rw [show 9 * (100 * blockCount n) = 100 * (9 * blockCount n) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
  rw [hdiv]
  omega

theorem choose_complement_mul_bucket_le (n j : ℕ)
    (hj : j ≤ structuredSize n) :
    (structuredSize n).choose (structuredSize n - j) *
        (n / structuredSize n - 1) ^ j ≤
      (structuredSize n * n) ^ j := by
  calc
    (structuredSize n).choose (structuredSize n - j) *
        (n / structuredSize n - 1) ^ j =
        (structuredSize n).choose j *
          (n / structuredSize n - 1) ^ j := by rw [Nat.choose_symm hj]
    _ ≤ structuredSize n ^ j * n ^ j := by
      gcongr
      · exact Nat.choose_le_pow _ _
      · have hdiv := Nat.div_le_self n (structuredSize n)
        omega
    _ = (structuredSize n * n) ^ j := by rw [mul_pow]

/-- The exact matrix-code factor and the saved overlap edges are bounded by
the enlarged large-overlap dyadic factor. -/
theorem large_dyadic_factor_le (n j : ℕ)
    (hj : j ≤ structuredSize n) :
    ((2 : ℝ) ^ (10 * blockCount n * j)) *
        (1 / 2 : ℝ) ^
          ((structuredSize n).choose 2 -
            (structuredSize n - j).choose 2) ≤
      (((2 : ℝ) ^
          (2 * blockCount n + 9 * structuredSize n / 100)) /
        (2 : ℝ) ^ (structuredSize n - j)) ^ j := by
  have hnum : (2 : ℝ) ^ (10 * blockCount n * j) ≤
      ((2 : ℝ) ^
        (2 * blockCount n + 9 * structuredSize n / 100)) ^ j := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (large_code_exponent_le_enlarged n j)
  have hdenNat := choose_two_sub_choose_two_ge_mul hj
  have hden : ((2 : ℝ) ^ (structuredSize n - j)) ^ j ≤
      (2 : ℝ) ^ ((structuredSize n).choose 2 -
        (structuredSize n - j).choose 2) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) hdenNat
  rw [one_div, inv_pow]
  rw [div_pow]
  exact mul_le_mul hnum
    ((inv_le_inv₀ (by positivity) (by positivity)).2 hden)
    (by positivity) (by positivity)

/-- Before dividing by the square of the mean, the exact large-overlap
stratum is at most one mean times `largeTerm`. -/
theorem large_stratum_le_mean_mul_largeTerm (n j : ℕ)
    (hj : j ≤ structuredSize n) :
    HostMoments.hostIntersectionContribution n (blockCount n)
        (structuredSize n - j) ≤
      FiniteUniform.natExpectation
          (HostFamily.witnessCount n (blockCount n)) * largeTerm n j := by
  let k := structuredSize n
  let r := blockCount n
  let q := n / k
  let C := k.choose 2
  let C' := (k - j).choose 2
  let S := C - C'
  have htemplate : HostFamily.templateOrder r = k := by
    simp [r, k, HostFamily.templateOrder, structuredSize_eq_mul_blockCount]
  have hbucket : HostFamily.bucketSize n r = q := by
    unfold HostFamily.bucketSize
    rw [htemplate]
  have hjtemplate : j ≤ HostFamily.templateOrder r := by
    rw [htemplate]
    exact hj
  have hraw := HostMoments.hostIntersectionContribution_le_large n r j hjtemplate
  have hC' : C' ≤ C := by
    exact Nat.choose_le_choose 2 (Nat.sub_le k j)
  have hE : 2 * C - C' = C + S := by simp only [S]; omega
  have hcomb : k.choose (k - j) * (q - 1) ^ j ≤ (k * n) ^ j := by
    have h := choose_complement_mul_bucket_le n j hj
    change k.choose (k - j) * (q - 1) ^ j ≤ (k * n) ^ j at h
    exact h
  have hdyadic :
      ((2 : ℝ) ^ (10 * r * j)) * (1 / 2 : ℝ) ^ S ≤
        (((2 : ℝ) ^ (2 * r + 9 * k / 100)) /
          (2 : ℝ) ^ (k - j)) ^ j := by
    have h := large_dyadic_factor_le n j hj
    change ((2 : ℝ) ^ (10 * r * j)) * (1 / 2 : ℝ) ^ S ≤
      (((2 : ℝ) ^ (2 * r + 9 * k / 100)) /
        (2 : ℝ) ^ (k - j)) ^ j at h
    exact h
  calc
    HostMoments.hostIntersectionContribution n (blockCount n) (structuredSize n - j) ≤
        (q ^ k * (k.choose (k - j) * (q - 1) ^ j) : ℕ) *
          ((2 ^ (90 * r * r) : ℕ) * 2 ^ (10 * r * j) *
            (1 / 2 : ℝ) ^ (2 * C - C')) := by
      simpa [r, k, q, C, C', htemplate] using hraw
    _ = FiniteUniform.natExpectation (HostFamily.witnessCount n r) *
        (((k.choose (k - j) * (q - 1) ^ j : ℕ) : ℝ) *
          ((2 : ℝ) ^ (10 * r * j) * (1 / 2 : ℝ) ^ S)) := by
      rw [HostMoments.natExpectation_host_witnessCount, htemplate, hbucket,
        hE, pow_add]
      simp only [C, Nat.cast_mul, Nat.cast_pow]
      ring
    _ ≤ FiniteUniform.natExpectation (HostFamily.witnessCount n r) *
        ((((k * n : ℕ) : ℝ) ^ j) *
          ((((2 : ℝ) ^ (2 * r + 9 * k / 100)) /
            (2 : ℝ) ^ (k - j)) ^ j)) := by
      gcongr
      · rw [HostMoments.natExpectation_host_witnessCount]
        positivity
      · exact_mod_cast hcomb
    _ = FiniteUniform.natExpectation
          (HostFamily.witnessCount n (blockCount n)) * largeTerm n j := by
      simp only [r, k]
      unfold largeTerm largeBase
      simp only [Nat.cast_mul, Nat.cast_pow]
      rw [mul_pow, div_pow]
      ring

/-- If the first moment is at least one, the normalized large-overlap
stratum is bounded by `largeTerm`. -/
theorem normalized_large_stratum_le (n j : ℕ)
    (hj : j ≤ structuredSize n)
    (hmean : 1 ≤ FiniteUniform.natExpectation
      (HostFamily.witnessCount n (blockCount n))) :
    HostMoments.hostIntersectionContribution n (blockCount n)
        (structuredSize n - j) /
        FiniteUniform.natExpectation
          (HostFamily.witnessCount n (blockCount n)) ^ 2 ≤
      largeTerm n j := by
  let μ := FiniteUniform.natExpectation
    (HostFamily.witnessCount n (blockCount n))
  have hμ : 0 < μ := lt_of_lt_of_le (by norm_num) hmean
  have hraw := large_stratum_le_mean_mul_largeTerm n j hj
  calc
    HostMoments.hostIntersectionContribution n (blockCount n)
          (structuredSize n - j) / μ ^ 2 ≤
        (μ * largeTerm n j) / μ ^ 2 := by
      exact div_le_div_of_nonneg_right hraw (sq_nonneg μ)
    _ = largeTerm n j / μ := by field_simp
    _ ≤ largeTerm n j := by
      rw [div_le_iff₀ hμ]
      nlinarith [largeTerm_nonneg n j]

/-! ## The one-overlap and diagonal errors -/

/-- The overlap-one term is kept separate from the uniformly summed range
`2 ≤ i ≤ 0.9k`. -/
noncomputable def oneOverlapError (n : ℕ) : ℝ :=
  ModerateMoments.moderateTerm n 1

theorem oneOverlapError_nonneg (n : ℕ) : 0 ≤ oneOverlapError n :=
  ModerateMoments.moderateTerm_nonneg n 1

theorem eventually_oneOverlapError_le_rpow :
    ∀ᶠ n : ℕ in atTop,
      oneOverlapError n ≤ (n : ℝ) ^ (-(1 / 25 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 1,
    tendsto_structuredSize_atTop.eventually_ge_atTop 2,
    eventually_moderate_overlap_power_bound_with_two] with n hn hk hpower
  have hrange : 10 * 1 ≤ 9 * structuredSize n := by omega
  have hbase := div_le_rpow_neg_one_div_twentyfive_of_pow_le
    (by omega : 0 < n) (hpower 1 hrange)
  simpa [oneOverlapError, ModerateMoments.moderateTerm,
    ModerateMoments.moderateBase] using hbase

theorem tendsto_oneOverlapError_zero :
    Tendsto oneOverlapError atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall oneOverlapError_nonneg
  · exact eventually_oneOverlapError_le_rpow
  · exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 25)).comp
      tendsto_natCast_atTop_atTop

/-- The diagonal contributes one first moment, hence its normalized cost is
at most the reciprocal of the first-moment lower bound `2^k`. -/
noncomputable def diagonalError (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ structuredSize n)⁻¹

theorem diagonalError_nonneg (n : ℕ) : 0 ≤ diagonalError n := by
  unfold diagonalError
  positivity

theorem tendsto_diagonalError_zero :
    Tendsto diagonalError atTop (nhds 0) := by
  unfold diagonalError
  exact tendsto_inv_atTop_zero.comp
    ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      tendsto_structuredSize_atTop)

/-- Eventually all stable-slot parameters needed by the normalized moderate
bound are positive, and every bucket contains at least three vertices. -/
theorem eventually_host_parameter_conditions :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < blockCount n ∧
        3 ≤ HostFamily.bucketSize n (blockCount n) := by
  filter_upwards [eventually_ge_atTop 1,
    tendsto_logParameter_atTop.eventually_ge_atTop 8000,
    eventually_one_le_blockCount] with n hn hlog hr
  have hk : 0 < FamilyCount.structuredOrder (blockCount n) := by
    unfold FamilyCount.structuredOrder
    exact Nat.mul_pos (by norm_num) (by omega)
  have hroom := FamilyCount.slot_room_of_logParameter_ge hlog
  have hexp : 2 ≤ FamilyCount.chooseExponentPerVertex (blockCount n) := by
    simp [FamilyCount.chooseExponentPerVertex]
    omega
  have hthree : 3 ≤ 2 ^ FamilyCount.chooseExponentPerVertex (blockCount n) := by
    calc
      3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ FamilyCount.chooseExponentPerVertex (blockCount n) :=
        Nat.pow_le_pow_right (by norm_num) hexp
  have hmul : 3 * FamilyCount.structuredOrder (blockCount n) ≤ n := by
    calc
      3 * FamilyCount.structuredOrder (blockCount n) ≤
          2 ^ FamilyCount.chooseExponentPerVertex (blockCount n) *
            FamilyCount.structuredOrder (blockCount n) := by gcongr
      _ ≤ n := hroom
  refine ⟨by omega, by omega, ?_⟩
  unfold HostFamily.bucketSize
  exact (Nat.le_div_iff_mul_le hk).2 hmul

/-- The exact diagonal stratum, divided by the squared mean, is controlled
by `diagonalError`. -/
theorem normalized_diagonal_stratum_le (n : ℕ)
    (hmean : (2 : ℝ) ^ structuredSize n ≤
      FiniteUniform.natExpectation
        (HostFamily.witnessCount n (blockCount n))) :
    HostMoments.hostIntersectionContribution n (blockCount n)
        (structuredSize n) /
        FiniteUniform.natExpectation
          (HostFamily.witnessCount n (blockCount n)) ^ 2 ≤
      diagonalError n := by
  let μ := FiniteUniform.natExpectation
    (HostFamily.witnessCount n (blockCount n))
  have htwo : 0 < (2 : ℝ) ^ structuredSize n := by positivity
  have hμ : 0 < μ := htwo.trans_le hmean
  have hraw := large_stratum_le_mean_mul_largeTerm n 0 (Nat.zero_le _)
  change HostMoments.hostIntersectionContribution n (blockCount n)
      (structuredSize n - 0) ≤ μ * largeTerm n 0 at hraw
  have hdiag : HostMoments.hostIntersectionContribution n (blockCount n)
      (structuredSize n) ≤ μ := by
    simpa [largeTerm] using hraw
  calc
    HostMoments.hostIntersectionContribution n (blockCount n)
          (structuredSize n) / μ ^ 2 ≤ μ / μ ^ 2 := by
      exact div_le_div_of_nonneg_right hdiag (sq_nonneg μ)
    _ = μ⁻¹ := by field_simp
    _ ≤ ((2 : ℝ) ^ structuredSize n)⁻¹ := by
      exact (inv_le_inv₀ hμ htwo).2 hmean
    _ = diagonalError n := rfl

/-- Total relative error after extracting the disjoint baseline. -/
noncomputable def relativeError (n : ℕ) : ℝ :=
  oneOverlapError n + ModerateMoments.moderateRelativeError n +
    largeRelativeError n + diagonalError n

theorem relativeError_nonneg (n : ℕ) : 0 ≤ relativeError n := by
  unfold relativeError
  exact add_nonneg
    (add_nonneg
      (add_nonneg (oneOverlapError_nonneg n)
        (ModerateMoments.moderateRelativeError_nonneg n))
      (largeRelativeError_nonneg n))
    (diagonalError_nonneg n)

theorem tendsto_relativeError_zero : Tendsto relativeError atTop (nhds 0) := by
  unfold relativeError
  simpa using (((tendsto_oneOverlapError_zero.add
    ModerateMoments.tendsto_moderateRelativeError_zero).add
      tendsto_largeRelativeError_zero).add tendsto_diagonalError_zero)

/-! ## Paley--Zygmund endpoint -/

theorem uniformProbability_eq_randomGraph_probability
    (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    ABHSchema.uniformProbability P = RandomGraph.probability n P := by
  rw [← HostMoments.finiteUniform_probability_eq_randomGraph_probability]
  classical
  rw [FiniteUniform.probability_eq_card_div]
  rfl

/-- Once the eventual relative second-moment estimate has been supplied,
the concrete host count is positive with high probability. -/
theorem almostSurely_positive_of_eventually_secondMoment
    (hsecond : ∀ᶠ n : ℕ in atTop,
      FiniteUniform.natSecondMoment
          (HostFamily.witnessCount n (blockCount n)) ≤
        (1 + relativeError n) *
          FiniteUniform.natExpectation
            (HostFamily.witnessCount n (blockCount n)) ^ 2) :
    RandomGraph.AlmostSurely (fun n G ↦
      0 < HostFamily.witnessCount n (blockCount n) G) := by
  have hlower : Tendsto (fun n ↦ (1 + relativeError n)⁻¹)
      atTop (nhds 1) := by
    have hden : Tendsto (fun n ↦ 1 + relativeError n) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add tendsto_relativeError_zero
    simpa using hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hmeanLower : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ^ structuredSize n ≤
        FiniteUniform.natExpectation
          (HostFamily.witnessCount n (blockCount n)) := by
    filter_upwards [FamilyCount.eventually_slotFirstMoment_ge_two_pow] with n hn
    simpa [hostMean_eq_slotFirstMoment] using hn
  have hprobLower : ∀ᶠ n : ℕ in atTop,
      (1 + relativeError n)⁻¹ ≤
        RandomGraph.probability n (fun G ↦
          0 < HostFamily.witnessCount n (blockCount n) G) := by
    filter_upwards [hmeanLower, hsecond] with n hmean hsecondN
    have hmeanPos : 0 < ABHSchema.uniformMean
        (HostFamily.witnessCount n (blockCount n)) := by
      rw [uniformMean_eq_hostMean]
      exact (by positivity : (0 : ℝ) < 2 ^ structuredSize n).trans_le hmean
    have hpaley := ABHSchema.inv_one_add_le_uniformProbability_pos
      (error := relativeError n)
      (HostFamily.witnessCount n (blockCount n)) hmeanPos
      (by nlinarith [relativeError_nonneg n])
      (by simpa [uniformMean_eq_hostMean,
          uniformSecondMoment_eq_hostSecondMoment] using hsecondN)
    simpa [uniformProbability_eq_randomGraph_probability] using hpaley
  unfold RandomGraph.AlmostSurely
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds
    hprobLower (Filter.Eventually.of_forall fun n ↦
      RandomGraph.probability_le_one n _)

/-! ## The assembled second-moment estimate -/

theorem hostIntersectionContribution_nonneg (n r i : ℕ) :
    0 ≤ HostMoments.hostIntersectionContribution n r i := by
  unfold HostMoments.hostIntersectionContribution
    HostMoments.choiceIntersectionContribution
  exact Finset.sum_nonneg fun cd _ ↦ FiniteUniform.probability_nonneg _

theorem eventual_host_secondMoment_bound :
    ∀ᶠ n : ℕ in atTop,
      FiniteUniform.natSecondMoment
          (HostFamily.witnessCount n (blockCount n)) ≤
        (1 + relativeError n) *
          FiniteUniform.natExpectation
            (HostFamily.witnessCount n (blockCount n)) ^ 2 := by
  filter_upwards [eventually_host_parameter_conditions,
    FamilyCount.eventually_slotFirstMoment_ge_two_pow,
    tendsto_structuredSize_atTop.eventually_ge_atTop 10] with n hparam hfirst hk
  rcases hparam with ⟨hn, hr, hq⟩
  let k := structuredSize n
  let μ := FiniteUniform.natExpectation
    (HostFamily.witnessCount n (blockCount n))
  let f := fun i ↦ HostMoments.hostIntersectionContribution n (blockCount n) i
  have hmean : (2 : ℝ) ^ k ≤ μ := by
    change (2 : ℝ) ^ structuredSize n ≤
      FiniteUniform.natExpectation
        (HostFamily.witnessCount n (blockCount n))
    rw [hostMean_eq_slotFirstMoment]
    exact hfirst
  have hμ : 1 ≤ μ :=
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hmean
  have hμpos : 0 < μ := lt_of_lt_of_le (by norm_num) hμ
  have hμsq : 0 < μ ^ 2 := sq_pos_of_pos hμpos
  have hkdiv : 10 ∣ k := by
    rw [show k = 100 * blockCount n by
      simp [k, structuredSize_eq_mul_blockCount]]
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hsplit := MomentRanges.sum_range_le_zero_one_moderate_largeDefect_top
    f (k := k) hk hkdiv (by
      intro j hj
      exact hostIntersectionContribution_nonneg n (blockCount n) (k - j))
  have hzero : f 0 ≤ μ ^ 2 := by
    have h := ModerateMoments.hostIntersectionContribution_le_mean_sq_mul_moderateTerm
      hn hr hq (Nat.zero_le k) (i := 0)
    simpa [f, μ, ModerateMoments.moderateTerm] using h
  have hone : f 1 ≤ μ ^ 2 * oneOverlapError n := by
    have hi : 1 ≤ k := by omega
    have h := ModerateMoments.hostIntersectionContribution_le_mean_sq_mul_moderateTerm
      hn hr hq hi (i := 1)
    simpa [f, μ, oneOverlapError] using h
  have hmoderate :
      (∑ i ∈ MomentRanges.moderateRange k, f i) ≤
        μ ^ 2 * ModerateMoments.moderateRelativeError n := by
    calc
      (∑ i ∈ MomentRanges.moderateRange k, f i) ≤
          ∑ i ∈ MomentRanges.moderateRange k,
            μ ^ 2 * ModerateMoments.moderateTerm n i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (MomentRanges.mem_moderateRange.mp hi).2
        have hik : i ≤ k := by
          have hdiv := Nat.div_le_self (9 * k) 10
          omega
        simpa [f, μ] using
          (ModerateMoments.hostIntersectionContribution_le_mean_sq_mul_moderateTerm
            hn hr hq hik)
      _ = μ ^ 2 * ModerateMoments.moderateRelativeError n := by
        unfold ModerateMoments.moderateRelativeError
        simp only [MomentRanges.moderateRange, k]
        rw [Finset.mul_sum]
  have hlarge :
      (∑ j ∈ MomentRanges.largeDefectRange k, f (k - j)) ≤
        μ ^ 2 * largeRelativeError n := by
    calc
      (∑ j ∈ MomentRanges.largeDefectRange k, f (k - j)) ≤
          ∑ j ∈ MomentRanges.largeDefectRange k,
            μ ^ 2 * largeTerm n j := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := by
          have hu := (MomentRanges.mem_largeDefectRange.mp hj).2
          have hdiv := Nat.div_le_self k 10
          omega
        have hnorm := normalized_large_stratum_le n j hjk hμ
        change f (k - j) / μ ^ 2 ≤ largeTerm n j at hnorm
        rw [div_le_iff₀ hμsq] at hnorm
        simpa [f, μ, mul_comm] using hnorm
      _ = μ ^ 2 * largeRelativeError n := by
        unfold largeRelativeError
        simp only [MomentRanges.largeDefectRange, k]
        rw [Finset.mul_sum]
  have hdiag : f k ≤ μ ^ 2 * diagonalError n := by
    have hnorm := normalized_diagonal_stratum_le n hmean
    change f k / μ ^ 2 ≤ diagonalError n at hnorm
    rw [div_le_iff₀ hμsq] at hnorm
    simpa [f, μ, mul_comm] using hnorm
  calc
    FiniteUniform.natSecondMoment
          (HostFamily.witnessCount n (blockCount n)) =
        ∑ i ∈ range (k + 1), f i := by
      simpa [f, k, HostFamily.templateOrder, structuredSize_eq_mul_blockCount]
        using HostMoments.natSecondMoment_host_witnessCount n (blockCount n)
    _ ≤
        f 0 + f 1 +
          (∑ i ∈ MomentRanges.moderateRange k, f i) +
          (∑ j ∈ MomentRanges.largeDefectRange k, f (k - j)) + f k := hsplit
    _ ≤ μ ^ 2 + μ ^ 2 * oneOverlapError n +
          μ ^ 2 * ModerateMoments.moderateRelativeError n +
          μ ^ 2 * largeRelativeError n + μ ^ 2 * diagonalError n := by
      gcongr
    _ = (1 + relativeError n) * μ ^ 2 := by
      unfold relativeError
      ring

/-- The canonical stable-slot host appears with high probability. -/
theorem almostSurely_positive_host_witnessCount :
    RandomGraph.AlmostSurely (fun n G ↦
      0 < HostFamily.witnessCount n (blockCount n) G) :=
  almostSurely_positive_of_eventually_secondMoment eventual_host_secondMoment_bound

end FinalMoments
end Erdos807
