import ErdosProblems.Erdos248.Scales
import BoundedGaps.Maynard.MaynardS1CrossCorrection

/-!
# Erdős Problem 248: the finite product Selberg weight

This file defines the actual nonnegative weight on the dyadic interval and
records its exact CRT/Y-transform decomposition.  No asymptotic estimate is
used here.  The cutoff is the bounded quadratic function
`min 1 (max (1-t) 0)^2`; on nonnegative inputs this is the usual compactly
supported quadratic Selberg cutoff.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

/-- A bounded, nonnegative, compactly supported quadratic cutoff. -/
def selbergCutoff (t : ℝ) : ℝ :=
  min 1 ((max (1 - t) 0) ^ 2)

theorem selbergCutoff_nonneg (t : ℝ) : 0 ≤ selbergCutoff t := by
  unfold selbergCutoff
  exact le_min (show (0 : ℝ) ≤ 1 by norm_num) (sq_nonneg _)

theorem selbergCutoff_le_one (t : ℝ) : selbergCutoff t ≤ 1 := by
  exact min_le_left (1 : ℝ) _

theorem abs_selbergCutoff_le_one (t : ℝ) : |selbergCutoff t| ≤ 1 := by
  rw [abs_of_nonneg (selbergCutoff_nonneg t)]
  exact selbergCutoff_le_one t

@[simp] theorem selbergCutoff_zero : selbergCutoff 0 = 1 := by
  norm_num [selbergCutoff]

theorem selbergCutoff_eq_zero {t : ℝ} (ht : 1 ≤ t) :
    selbergCutoff t = 0 := by
  unfold selbergCutoff
  rw [max_eq_right (by linarith)]
  norm_num

/-- The cutoff is uniformly bounded below on the inner half of its support. -/
theorem quarter_le_selbergCutoff {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤ selbergCutoff t := by
  have hnonneg : 0 ≤ 1 - t := by linarith
  have hsq : (1 - t) ^ 2 ≤ (1 : ℝ) := by nlinarith
  unfold selbergCutoff
  rw [max_eq_left hnonneg, min_eq_right hsq]
  nlinarith [sq_nonneg (t - 1 / 2)]

/-- The coordinate product cutoff.  Multiplication by `100^k` converts
the common normalized logarithm into the coordinate scale
`log r / log R_k`. -/
def tupleCutoff (K : ℕ) (x : nearShifts K → ℝ) : ℝ :=
  ∏ h : nearShifts K,
    selbergCutoff (((100 ^ (h : ℕ) : ℕ) : ℝ) * x h)

theorem tupleCutoff_nonneg (K : ℕ) (x : nearShifts K → ℝ) :
    0 ≤ tupleCutoff K x := by
  unfold tupleCutoff
  exact Finset.prod_nonneg fun h _ ↦ selbergCutoff_nonneg _

theorem abs_tupleCutoff_le_one (K : ℕ) (x : nearShifts K → ℝ) :
    |tupleCutoff K x| ≤ 1 := by
  rw [abs_of_nonneg (tupleCutoff_nonneg K x)]
  unfold tupleCutoff
  simpa only [Finset.prod_const_one] using
    Finset.prod_le_prod (fun h _ ↦ selbergCutoff_nonneg _)
      (fun h _ ↦ selbergCutoff_le_one _)

/-- Primorial modulus fixing all tiny-prime residues. -/
def preSieveModulus (K : ℕ) : ℕ :=
  primorial (tinyCutoff K)

/-- Supported Y-variable associated to the product cutoff. -/
def sieveY (K : ℕ) : (nearShifts K → ℕ) → ℝ :=
  maynardYValue (nearShifts K) (globalRadius K) (preSieveModulus K)
    (tupleCutoff K)

/-- The finite tuple coefficient obtained by inverse Y-transform. -/
def sieveCoefficient (K : ℕ) : (nearShifts K → ℕ) → ℝ :=
  maynardCoefficient (nearShifts K) (globalRadius K)
    (preSieveModulus K) (tupleCutoff K)

/-- Finite tuple support used in every expanded divisor sum. -/
def sieveDivisorSupport (K : ℕ) : Finset (nearShifts K → ℕ) :=
  maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
    (preSieveModulus K)

/-- The nonnegative product Selberg weight on a natural number. -/
def sieveWeight (K n : ℕ) : ℝ :=
  preSievedSquareDivisorWeight (nearShifts K) (sieveDivisorSupport K)
    (sieveCoefficient K) 0 (preSieveModulus K) n

/-- Total unnormalized mass on the dyadic interval `[x,2x)`. -/
def sieveMass (K : ℕ) : ℝ :=
  sieveWeightSum (intervalStart K) (sieveWeight K)

theorem sieveY_supported (K : ℕ) :
    IsSupportedMaynardY (nearShifts K) (globalRadius K)
      (preSieveModulus K) (sieveY K) := by
  exact isSupportedMaynardY_maynardYValue _ _ _ _

theorem abs_sieveY_le_one (K : ℕ) (r : nearShifts K → ℕ) :
    |sieveY K r| ≤ 1 := by
  unfold sieveY maynardYValue
  split_ifs
  · exact abs_tupleCutoff_le_one K _
  · norm_num

/-- Nonzero Y-mass in coordinate `h` is confined to the intended varying
radius `R_h`, not merely to the much looser common Y-transform radius. -/
theorem sieveY_ne_zero_coordinate_lt {K : ℕ}
    {r : nearShifts K → ℕ} (hr : sieveY K r ≠ 0)
    (h : nearShifts K) :
    r h < shiftRadius K h := by
  have hbase :
      divisorTupleProduct (nearShifts K) r < globalRadius K ∧
        Nat.Coprime (divisorTupleProduct (nearShifts K) r)
          (preSieveModulus K) ∧
        Squarefree (divisorTupleProduct (nearShifts K) r) := by
    by_contra hnot
    exact hr (by simp [sieveY, maynardYValue, hnot])
  have htuple :
      tupleCutoff K
          (fun i => Real.log (r i) / Real.log (globalRadius K)) ≠ 0 := by
    unfold sieveY maynardYValue at hr
    rw [if_pos hbase] at hr
    exact hr
  have hcut :
      selbergCutoff
          (((100 ^ (h : ℕ) : ℕ) : ℝ) *
            (Real.log (r h) / Real.log (globalRadius K))) ≠ 0 := by
    intro hz
    apply htuple
    unfold tupleCutoff
    exact Finset.prod_eq_zero (Finset.mem_univ h) hz
  have harg :
      ((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (Real.log (r h) / Real.log (globalRadius K)) < 1 := by
    by_contra hnot
    have hone : (1 : ℝ) ≤
        ((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (Real.log (r h) / Real.log (globalRadius K)) := le_of_not_gt hnot
    exact hcut (selbergCutoff_eq_zero hone)
  by_contra hnot
  have hradiusLe : shiftRadius K h ≤ r h := Nat.le_of_not_gt hnot
  have hglobalLog : 0 < Real.log (globalRadius K) :=
    Real.log_pos (by exact_mod_cast one_lt_globalRadius K)
  have hradiusReal : (0 : ℝ) < shiftRadius K h := by
    exact_mod_cast shiftRadius_pos K h
  have hrReal : (0 : ℝ) < r h := by
    exact_mod_cast lt_of_lt_of_le (shiftRadius_pos K h) hradiusLe
  have hlogLe : Real.log (shiftRadius K h) ≤ Real.log (r h) :=
    Real.strictMonoOn_log.monotoneOn hradiusReal hrReal (by exact_mod_cast hradiusLe)
  have hnormLe :
      Real.log (shiftRadius K h) / Real.log (globalRadius K) ≤
        Real.log (r h) / Real.log (globalRadius K) :=
    (div_le_div_iff_of_pos_right hglobalLog).2 hlogLe
  rw [log_shiftRadius_div_log_globalRadius
    (K := K) (k := (h : ℕ)) (mem_nearShifts.mp h.property).2] at hnormLe
  have hfactor : (0 : ℝ) < ((100 ^ (h : ℕ) : ℕ) : ℝ) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hnormLe hfactor.le
  have hcancel :
      ((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (1 / ((100 ^ (h : ℕ) : ℕ) : ℝ)) = 1 := by
    field_simp
  rw [hcancel] at hmul
  linarith

/-- A coefficient vanishes as soon as one divisor coordinate reaches its
assigned radius.  This sharpens the generic common-radius support to the
geometric varying-radius box needed in every CRT error estimate. -/
theorem sieveCoefficient_eq_zero_of_shiftRadius_le {K : ℕ}
    (d : nearShifts K → ℕ) (h : nearShifts K)
    (hd : shiftRadius K h ≤ d h) :
    sieveCoefficient K d = 0 := by
  rw [sieveCoefficient,
    maynardCoefficient_eq_fromYValue]
  unfold maynardCoefficientFromY
  by_cases hcop :
      Nat.Coprime (divisorTupleProduct (nearShifts K) d)
        (preSieveModulus K)
  · rw [if_pos hcop]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro r hrbox
    by_cases hcond :
        divisorTupleProduct (nearShifts K) r < globalRadius K ∧
          ∀ i : nearShifts K, d i ∣ r i
    · rw [if_pos hcond]
      have hrpos : 0 < r h :=
        (mem_maynardDivisorTupleBox_iff.mp hrbox h).1
      have hdle : d h ≤ r h := Nat.le_of_dvd hrpos (hcond.2 h)
      have hyzero : sieveY K r = 0 := by
        by_contra hyne
        have hrlt := sieveY_ne_zero_coordinate_lt hyne h
        omega
      change sieveY K r / _ = 0
      rw [hyzero, zero_div]
    · rw [if_neg hcond]
  · rw [if_neg hcop]

theorem sieveCoefficient_ne_zero_coordinate_lt {K : ℕ}
    {d : nearShifts K → ℕ} (hd : sieveCoefficient K d ≠ 0)
    (h : nearShifts K) :
    d h < shiftRadius K h := by
  by_contra hnot
  exact hd (sieveCoefficient_eq_zero_of_shiftRadius_le d h
    (Nat.le_of_not_gt hnot))

theorem divisorTupleProduct_le_radiusProduct_of_sieveCoefficient_ne_zero
    {K : ℕ} {d : nearShifts K → ℕ}
    (hd : sieveCoefficient K d ≠ 0) :
    divisorTupleProduct (nearShifts K) d ≤ radiusProduct K := by
  classical
  unfold divisorTupleProduct radiusProduct
  rw [Finset.prod_subtype (nearShifts K) (fun _ => Iff.rfl)]
  apply Finset.prod_le_prod
  · intro k hk
    exact Nat.zero_le _
  · intro k hk
    exact (sieveCoefficient_ne_zero_coordinate_lt hd k).le

/-- The genuinely active part of the generic Maynard divisor support. -/
def activeDivisorSupport (K : ℕ) : Finset (nearShifts K → ℕ) :=
  (sieveDivisorSupport K).filter fun d => sieveCoefficient K d ≠ 0

theorem activeDivisorSupport_subset_coordinateBox (K : ℕ) :
    activeDivisorSupport K ⊆
      Fintype.piFinset (fun h : nearShifts K =>
        Finset.range (shiftRadius K h)) := by
  classical
  intro d hd
  rw [activeDivisorSupport, Finset.mem_filter] at hd
  rw [Fintype.mem_piFinset]
  intro h
  exact Finset.mem_range.mpr
    (sieveCoefficient_ne_zero_coordinate_lt hd.2 h)

theorem activeDivisorSupport_card_le_radiusProduct (K : ℕ) :
    (activeDivisorSupport K).card ≤ radiusProduct K := by
  classical
  calc
    (activeDivisorSupport K).card ≤
        (Fintype.piFinset (fun h : nearShifts K =>
          Finset.range (shiftRadius K h))).card :=
      Finset.card_le_card (activeDivisorSupport_subset_coordinateBox K)
    _ = ∏ h : nearShifts K, shiftRadius K h := by
      simp only [Fintype.card_piFinset, Finset.card_range]
    _ = radiusProduct K := by
      unfold radiusProduct
      rw [Finset.prod_subtype (nearShifts K) (fun _ => Iff.rfl)]

/-- Uniform polylogarithmic bound for every coefficient on the generic
support.  The exponent is explicit because the dimension is exactly `K`. -/
theorem abs_sieveCoefficient_le_log {K : ℕ} (hK : 0 < K)
    (d : nearShifts K → ℕ) (hd : d ∈ sieveDivisorSupport K) :
    |sieveCoefficient K d| ≤
      (1 + Real.log (globalRadius K)) ^ (2 * K ^ 2) := by
  have hd' : d ∈ maynardDivisorTupleSupport (nearShifts K)
      (globalRadius K) (preSieveModulus K) := by
    simpa [sieveDivisorSupport] using hd
  unfold sieveCoefficient
  simpa using
    (abs_maynardCoefficient_le_sharp_log
      (nearShifts K) (globalRadius K) (preSieveModulus K)
      (tupleCutoff K) d 1 (by norm_num)
      (abs_tupleCutoff_le_one K) (nearShifts_nonempty hK) hd')

/-- Terms with a zero coefficient may be removed from both variables in the
absolute CRT error mass. -/
theorem compatibleDivisorPairCoefficientMass_eq_filter_ne_zero
    {H : Finset ℕ} (D : Finset (H → ℕ))
    (lambda : (H → ℕ) → ℝ) :
    compatibleDivisorPairCoefficientMass H D lambda =
      compatibleDivisorPairCoefficientMass H
        (D.filter fun d => lambda d ≠ 0) lambda := by
  classical
  unfold compatibleDivisorPairCoefficientMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hld : lambda d = 0
  · simp [hld]
  · rw [if_pos hld]
    rw [Finset.filter_filter]
    rw [Finset.sum_filter]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hle : lambda e = 0
    · simp [hle]
    · simp [hle]

/-- Explicit envelope for the complete interval-counting error mass, using
the sharp coordinate support rather than the loose generic radius box. -/
theorem sieveCoefficientMass_le_radiusProduct {K : ℕ} (hK : 0 < K) :
    compatibleDivisorPairCoefficientMass (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K) ≤
      (radiusProduct K : ℝ) ^ 2 *
        ((1 + Real.log (globalRadius K)) ^ (2 * K ^ 2)) ^ 2 := by
  rw [compatibleDivisorPairCoefficientMass_eq_filter_ne_zero]
  change compatibleDivisorPairCoefficientMass (nearShifts K)
      (activeDivisorSupport K) (sieveCoefficient K) ≤ _
  calc
    compatibleDivisorPairCoefficientMass (nearShifts K)
        (activeDivisorSupport K) (sieveCoefficient K) ≤
        (((activeDivisorSupport K).card : ℝ) ^ 2) *
          ((1 + Real.log (globalRadius K)) ^ (2 * K ^ 2)) ^ 2 := by
      apply compatibleDivisorPairCoefficientMass_le_card_sq_mul
      · positivity
      · intro d hd
        exact abs_sieveCoefficient_le_log hK d
          (Finset.mem_filter.mp hd).1
    _ ≤ (radiusProduct K : ℝ) ^ 2 *
        ((1 + Real.log (globalRadius K)) ^ (2 * K ^ 2)) ^ 2 := by
      gcongr
      exact_mod_cast activeDivisorSupport_card_le_radiusProduct K

theorem sieveWeight_nonneg (K n : ℕ) : 0 ≤ sieveWeight K n := by
  exact preSievedSquareDivisorWeight_nonneg _ _ _ _ _ _

theorem sieveDivisorSupport_isMaynard (K : ℕ)
    (d : nearShifts K → ℕ) (hd : d ∈ sieveDivisorSupport K) :
    IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) d := by
  exact isMaynardDivisorTuple_of_mem_support hd

theorem preSieveModulus_pos (K : ℕ) : 0 < preSieveModulus K := by
  exact primorial_pos _

/-- Exact interval-counting decomposition of the total mass. -/
theorem sieveMass_eq_main_add_error (K : ℕ) :
    sieveMass K =
      compatibleDivisorPairMainSum (nearShifts K) (sieveDivisorSupport K)
          (preSieveModulus K) (intervalStart K) (sieveCoefficient K) +
        compatibleDivisorPairErrorSum (nearShifts K) (sieveDivisorSupport K)
          0 (preSieveModulus K) (intervalStart K) (sieveCoefficient K) := by
  unfold sieveMass sieveWeight
  exact sieveWeightSum_preSieved_eq_compatibleDivisorPairMainSum_add_error
    (sieveDivisorSupport_isMaynard K) (nearShifts_cover K)

/-- The exact main term is the Y-diagonal minus the cross-coordinate
correction, multiplied by the interval length divided by the primorial. -/
theorem sieveMain_eq_diagonal_sub_cross (K : ℕ) :
    compatibleDivisorPairMainSum (nearShifts K) (sieveDivisorSupport K)
        (preSieveModulus K) (intervalStart K) (sieveCoefficient K) =
      (intervalStart K : ℝ) / preSieveModulus K *
        (maynardYDiagonalSum (nearShifts K) (globalRadius K)
            (preSieveModulus K) (sieveY K) -
          incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
            (sieveDivisorSupport K) (sieveCoefficient K)) := by
  unfold sieveDivisorSupport sieveCoefficient sieveY
  exact compatibleDivisorPairMainSum_eq_yValueDiagonal_sub_incompatible
    (nearShifts K) (globalRadius K) (preSieveModulus K)
      (intervalStart K) (tupleCutoff K)

end Erdos248
