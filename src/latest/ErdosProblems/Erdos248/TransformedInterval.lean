import ErdosProblems.Erdos248.TransformedEnergy

/-!
# Erdős Problem 248: interval errors for transformed coefficients

The prime-event transforms keep `Y` in the sharp coordinate box.  A crude
but fully explicit coefficient estimate is therefore enough: the enormous
gap between `radiusProduct` and `intervalStart` absorbs a fixed power of the
former without any delicate divisor-sum asymptotic.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance transformedIntervalDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def activeTransformedYSupport (K R W : ℕ)
    (y : (nearShifts K → ℕ) → ℝ) : Finset (nearShifts K → ℕ) :=
  (maynardDivisorTupleSupport (nearShifts K) R W).filter fun r => y r ≠ 0

theorem activeTransformedYSupport_subset_varying
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hySharp : IsVaryingSupported K y) :
    activeTransformedYSupport K R W y ⊆ varyingTupleBox K := by
  intro r hr
  have hrData := Finset.mem_filter.mp hr
  have hrMaynard := isMaynardDivisorTuple_of_mem_support hrData.1
  rw [varyingTupleBox, Fintype.mem_piFinset]
  intro h
  rw [varyingCoordinateSupport, preSievedCommonCoordinateSupport,
    Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr (hySharp hrData.2 h),
    Nat.pos_of_ne_zero (hrMaynard.coordinate_squarefree h).ne_zero,
    hrMaynard.coordinate_squarefree h,
    (hrMaynard.coordinate_coprime_W h).coprime_dvd_right hmod⟩

theorem activeTransformedYSupport_card_le
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hySharp : IsVaryingSupported K y) :
    (activeTransformedYSupport K R W y).card ≤ radiusProduct K := by
  calc
    (activeTransformedYSupport K R W y).card ≤
        (varyingTupleBox K).card :=
      Finset.card_le_card
        (activeTransformedYSupport_subset_varying hmod hySharp)
    _ = ∏ h : nearShifts K, (varyingCoordinateSupport K h).card := by
      simp [varyingTupleBox, Fintype.card_piFinset]
    _ ≤ ∏ h : nearShifts K, shiftRadius K h := by
      apply Finset.prod_le_prod
      · intro h hh
        exact Nat.zero_le _
      · intro h hh
        calc
          (varyingCoordinateSupport K h).card ≤
              (Finset.range (shiftRadius K h)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = shiftRadius K h := Finset.card_range _
    _ = radiusProduct K := by
      unfold radiusProduct
      rw [Finset.prod_subtype (nearShifts K) (fun _ => Iff.rfl)]

theorem maynardCoefficientFromY_eq_zero_of_radius_le
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (d : nearShifts K → ℕ) (h : nearShifts K)
    (hd : shiftRadius K h ≤ d h) :
    maynardCoefficientFromY (nearShifts K) R W y d = 0 := by
  rw [maynardCoefficientFromY_eq_coreSum hy d]
  split_ifs
  · apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro r hr
    unfold inverseYTerm
    by_cases hdr : tupleDvd d r
    · rw [if_pos hdr]
      have hyr : y r = 0 := by
        by_contra hyr
        have hrPos : 0 < r h :=
          Nat.pos_of_ne_zero ((hy r hyr).coordinate_squarefree h).ne_zero
        have hdrLe : d h ≤ r h := Nat.le_of_dvd hrPos (hdr h)
        exact (not_le_of_gt (hySharp hyr h)) (hd.trans hdrLe)
      simp [hyr]
    · rw [if_neg hdr]
  · rfl

def activeTransformedCoefficientSupport (K R W : ℕ)
    (y : (nearShifts K → ℕ) → ℝ) : Finset (nearShifts K → ℕ) :=
  (maynardDivisorTupleSupport (nearShifts K) R W).filter fun d =>
    maynardCoefficientFromY (nearShifts K) R W y d ≠ 0

theorem activeTransformedCoefficientSupport_subset_box
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y) :
    activeTransformedCoefficientSupport K R W y ⊆
      Fintype.piFinset fun h : nearShifts K => Finset.range (shiftRadius K h) := by
  intro d hd
  have hdData := Finset.mem_filter.mp hd
  rw [Fintype.mem_piFinset]
  intro h
  apply Finset.mem_range.mpr
  by_contra hnot
  exact hdData.2 (maynardCoefficientFromY_eq_zero_of_radius_le
    hy hySharp d h (Nat.le_of_not_gt hnot))

theorem activeTransformedCoefficientSupport_card_le
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y) :
    (activeTransformedCoefficientSupport K R W y).card ≤ radiusProduct K := by
  calc
    (activeTransformedCoefficientSupport K R W y).card ≤
        (Fintype.piFinset fun h : nearShifts K =>
          Finset.range (shiftRadius K h)).card :=
      Finset.card_le_card
        (activeTransformedCoefficientSupport_subset_box hy hySharp)
    _ = ∏ h : nearShifts K, shiftRadius K h := by
      simp only [Fintype.card_piFinset, Finset.card_range]
    _ = radiusProduct K := by
      unfold radiusProduct
      rw [Finset.prod_subtype (nearShifts K) (fun _ => Iff.rfl)]

theorem abs_moebiusTupleFactor_le_product
    {H : Finset ℕ} (d : H → ℕ) :
    |∏ h : H, (ArithmeticFunction.moebius (d h) : ℝ) * d h| ≤
      (divisorTupleProduct H d : ℝ) := by
  rw [Finset.abs_prod]
  calc
    (∏ h : H, |(ArithmeticFunction.moebius (d h) : ℝ) * d h|) ≤
        ∏ h : H, (d h : ℝ) := by
      apply Finset.prod_le_prod
      · intro h hh
        exact abs_nonneg _
      · intro h hh
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d h)]
        have hmu : |(ArithmeticFunction.moebius (d h) : ℝ)| ≤ 1 := by
          rcases ArithmeticFunction.moebius_eq_or (d h) with hmu | hmu | hmu <;>
            simp [hmu]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hmu (by positivity : (0 : ℝ) ≤ d h)
    _ = (divisorTupleProduct H d : ℝ) := by
      simp [divisorTupleProduct]

theorem abs_inverseYTerm_le
    {H : Finset ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {d r : H → ℕ} (hr : ∀ h : H, 0 < r h) :
    |inverseYTerm d y r| ≤ B := by
  unfold inverseYTerm
  by_cases hdr : tupleDvd d r
  · rw [if_pos hdr, abs_div]
    have hden : (1 : ℝ) ≤
        ∏ h : H, (Nat.totient (r h) : ℝ) := by
      apply Finset.one_le_prod
      intro h hh
      exact_mod_cast Nat.totient_pos.mpr (hr h)
    rw [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ ∏ h : H, (Nat.totient (r h) : ℝ))]
    exact (div_le_div_of_nonneg_right (hyBound r) (by positivity)).trans
      (div_le_self hB hden)
  · rw [if_neg hdr, abs_zero]
    exact hB

theorem abs_transformedCoefficient_le
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    (d : nearShifts K → ℕ)
    (hd : d ∈ maynardDivisorTupleSupport (nearShifts K) R W) :
    |maynardCoefficientFromY (nearShifts K) R W y d| ≤
      (radiusProduct K : ℝ) ^ 2 * B := by
  by_cases hcoeff :
      maynardCoefficientFromY (nearShifts K) R W y d = 0
  · rw [hcoeff, abs_zero]
    positivity
  let A := activeTransformedYSupport K R W y
  have hcard : (A.card : ℝ) ≤ radiusProduct K := by
    exact_mod_cast activeTransformedYSupport_card_le hmod hySharp
  have hdprod : (divisorTupleProduct (nearShifts K) d : ℝ) ≤
      radiusProduct K := by
    have hcoord : ∀ h : nearShifts K, d h < shiftRadius K h := by
      intro h
      by_contra hnot
      have hzero := maynardCoefficientFromY_eq_zero_of_radius_le
        hy hySharp d h (Nat.le_of_not_gt hnot)
      exact hcoeff hzero
    exact_mod_cast (by
      unfold divisorTupleProduct radiusProduct
      rw [Finset.prod_subtype (nearShifts K) (fun _ => Iff.rfl)]
      apply Finset.prod_le_prod
      · intro h hh
        exact Nat.zero_le _
      · intro h hh
        exact (hcoord h).le)
  rw [maynardCoefficientFromY_eq_coreSum hy d]
  have hdCop := (isMaynardDivisorTuple_of_mem_support hd).2.1
  rw [if_pos hdCop, abs_mul]
  calc
    |∏ h : nearShifts K,
        (ArithmeticFunction.moebius (d h) : ℝ) * d h| *
        |∑ r ∈ maynardDivisorTupleSupport (nearShifts K) R W,
          inverseYTerm d y r| ≤
        (divisorTupleProduct (nearShifts K) d : ℝ) *
          |∑ r ∈ maynardDivisorTupleSupport (nearShifts K) R W,
            inverseYTerm d y r| := by
      gcongr
      exact abs_moebiusTupleFactor_le_product d
    _ = (divisorTupleProduct (nearShifts K) d : ℝ) *
          |∑ r ∈ A, inverseYTerm d y r| := by
      congr 1
      apply congrArg abs
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro r hrD hrNot
      have hyr : y r = 0 := by
        by_contra hyr
        exact hrNot (Finset.mem_filter.mpr ⟨hrD, hyr⟩)
      simp [inverseYTerm, hyr]
    _ ≤ (divisorTupleProduct (nearShifts K) d : ℝ) *
          ∑ r ∈ A, |inverseYTerm d y r| := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (divisorTupleProduct (nearShifts K) d : ℝ) *
          ∑ _r ∈ A, B := by
      gcongr with r hr
      have hrMaynard := isMaynardDivisorTuple_of_mem_support
        (Finset.mem_filter.mp hr).1
      exact abs_inverseYTerm_le hB hyBound fun h =>
        Nat.pos_of_ne_zero (hrMaynard.coordinate_squarefree h).ne_zero
    _ = (divisorTupleProduct (nearShifts K) d : ℝ) * (A.card * B) := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
    _ ≤ (radiusProduct K : ℝ) * ((radiusProduct K : ℝ) * B) := by
      gcongr
    _ = (radiusProduct K : ℝ) ^ 2 * B := by ring

theorem transformedCoefficientMass_le
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    compatibleDivisorPairCoefficientMass (nearShifts K)
        (maynardDivisorTupleSupport (nearShifts K) R W)
        (maynardCoefficientFromY (nearShifts K) R W y) ≤
      (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
  rw [compatibleDivisorPairCoefficientMass_eq_filter_ne_zero]
  change compatibleDivisorPairCoefficientMass (nearShifts K)
      (activeTransformedCoefficientSupport K R W y)
      (maynardCoefficientFromY (nearShifts K) R W y) ≤ _
  calc
    compatibleDivisorPairCoefficientMass (nearShifts K)
        (activeTransformedCoefficientSupport K R W y)
        (maynardCoefficientFromY (nearShifts K) R W y) ≤
        (((activeTransformedCoefficientSupport K R W y).card : ℝ) ^ 2) *
          (((radiusProduct K : ℝ) ^ 2 * B) ^ 2) := by
      apply compatibleDivisorPairCoefficientMass_le_card_sq_mul
      · positivity
      · intro d hd
        exact abs_transformedCoefficient_le hmod hy hySharp hB hyBound d
          (Finset.mem_filter.mp hd).1
    _ ≤ ((radiusProduct K : ℝ) ^ 2) *
          (((radiusProduct K : ℝ) ^ 2 * B) ^ 2) := by
      gcongr
      exact_mod_cast activeTransformedCoefficientSupport_card_le hy hySharp
    _ = (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by ring

theorem abs_transformedIntervalError_le
    {K R W N v : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hmod : preSieveModulus K ∣ W) (hW : 0 < W)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    |compatibleDivisorPairErrorSum (nearShifts K)
        (maynardDivisorTupleSupport (nearShifts K) R W) v W N
        (maynardCoefficientFromY (nearShifts K) R W y)| ≤
      (radiusProduct K : ℝ) ^ 6 * B ^ 2 := by
  exact (abs_compatibleDivisorPairErrorSum_le_coefficientMass
    (R := R) hW (fun d hd => isMaynardDivisorTuple_of_mem_support hd)).trans
      (transformedCoefficientMass_le hmod hy hySharp hB hyBound)

end Erdos248
