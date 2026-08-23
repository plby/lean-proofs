import ErdosProblems.Erdos248.MediumEventMass

/-!
# Erdős Problem 248: sharp medium-prime energies

The coarse medium-prime estimates bound every coordinate by its unweighted
reciprocal-totient majorant.  That loses a factor `96 ^ K`, including on the
principal finite difference.  Here we keep the cutoff squares in all
unchanged coordinates and use the majorant comparison only in the one
distinguished coordinate.  Thus the principal term costs only one absolute
factor `96`; the exponentially weighted loss is confined to the genuine
cross-coordinate remainders.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance mediumSharpEnergyDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The scalar reciprocal-totient mass of one varying coordinate. -/
def varyingCoordinateReciprocalMass (K : ℕ) (h : nearShifts K) : ℝ :=
  ∑ n ∈ varyingCoordinateSupport K h, (1 : ℝ) / Nat.totient n

theorem varyingCoordinateReciprocalMass_nonneg (K : ℕ)
    (h : nearShifts K) :
    0 ≤ varyingCoordinateReciprocalMass K h := by
  unfold varyingCoordinateReciprocalMass
  positivity

/-- The open varying support has no more mass than the corresponding closed
Wirsing mean. -/
theorem varyingCoordinateReciprocalMass_le_majorant (K : ℕ)
    (h : nearShifts K) :
    varyingCoordinateReciprocalMass K h ≤ varyingCoordinateMajorant K h := by
  unfold varyingCoordinateReciprocalMass varyingCoordinateMajorant
    varyingCoordinateSupport preSievedCommonCoordinateSupport
    squarefreeCoprimeInvTotientMean
  calc
    (∑ n ∈ (Finset.range (shiftRadius K h)).filter fun n =>
        1 ≤ n ∧ Squarefree n ∧ Nat.Coprime n (preSieveModulus K),
        (1 : ℝ) / Nat.totient n) =
        ∑ n ∈ (Finset.range (shiftRadius K h)).filter fun n =>
          1 ≤ n ∧ Squarefree n ∧ Nat.Coprime n (preSieveModulus K),
          if Squarefree n ∧ Nat.Coprime n (preSieveModulus K) then
            (1 : ℝ) / Nat.totient n else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [if_pos ⟨(Finset.mem_filter.mp hn).2.2.1,
        (Finset.mem_filter.mp hn).2.2.2⟩]
    _ ≤ ∑ n ∈ Finset.Icc 1 (shiftRadius K h),
        if Squarefree n ∧ Nat.Coprime n (preSieveModulus K) then
          (1 : ℝ) / Nat.totient n else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnData := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨hnData.2.1,
          (Finset.mem_range.mp hnData.1).le⟩
      · intro n hn hnot
        split_ifs <;> positivity
    _ = _ := rfl

/-- Exact box factorization for the cutoff product with one coordinate
deleted. -/
theorem coordinateProductExcept_energy_eq (K : ℕ)
    (m : nearShifts K) :
    (∑ r ∈ varyingTupleBox K,
        coordinateProductExcept K m r ^ 2 *
          reciprocalTotientTupleWeight (nearShifts K) r) =
      varyingCoordinateReciprocalMass K m *
        ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          coordinateEnergy K h := by
  let f : (h : nearShifts K) → ℕ → ℝ := fun h n =>
    if h = m then (1 : ℝ) / Nat.totient n
    else coordinateCutoff K h n ^ 2 / Nat.totient n
  have hintegrand : ∀ r : nearShifts K → ℕ,
      coordinateProductExcept K m r ^ 2 *
          reciprocalTotientTupleWeight (nearShifts K) r =
        ∏ h : nearShifts K, f h (r h) := by
    intro r
    unfold coordinateProductExcept reciprocalTotientTupleWeight
    rw [← Finset.prod_pow]
    rw [show (∏ h : nearShifts K, (1 : ℝ) / Nat.totient (r h)) =
        ((1 : ℝ) / Nat.totient (r m)) *
          ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            (1 : ℝ) / Nat.totient (r h) by
      exact (Finset.mul_prod_erase Finset.univ
        (fun h : nearShifts K => (1 : ℝ) / Nat.totient (r h))
        (Finset.mem_univ m)).symm]
    rw [show (∏ h : nearShifts K, f h (r h)) =
        f m (r m) *
          ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            f h (r h) by
      exact (Finset.mul_prod_erase Finset.univ
        (fun h : nearShifts K => f h (r h)) (Finset.mem_univ m)).symm]
    simp only [f, if_pos]
    rw [show
      (∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          coordinateCutoff K h (r h) ^ 2) *
          ((1 : ℝ) / Nat.totient (r m) *
            ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
              (1 : ℝ) / Nat.totient (r h)) =
        ((1 : ℝ) / Nat.totient (r m)) *
          ((∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
              coordinateCutoff K h (r h) ^ 2) *
            ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
              (1 : ℝ) / Nat.totient (r h)) by ring]
    apply congrArg (((1 : ℝ) / Nat.totient (r m)) * ·)
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h hh
    have hne : h ≠ m := (Finset.mem_erase.mp hh).1
    rw [if_neg hne]
    ring
  unfold varyingTupleBox
  calc
    (∑ r ∈ Fintype.piFinset (varyingCoordinateSupport K),
        coordinateProductExcept K m r ^ 2 *
          reciprocalTotientTupleWeight (nearShifts K) r) =
        ∑ r ∈ Fintype.piFinset (varyingCoordinateSupport K),
          ∏ h : nearShifts K, f h (r h) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact hintegrand r
    _ = ∏ h : nearShifts K,
        ∑ n ∈ varyingCoordinateSupport K h, f h n := by
      exact (Finset.prod_univ_sum (varyingCoordinateSupport K) f).symm
    _ = (∑ n ∈ varyingCoordinateSupport K m,
          (1 : ℝ) / Nat.totient n) *
        ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          coordinateEnergy K h := by
      rw [show (∏ h : nearShifts K,
          ∑ n ∈ varyingCoordinateSupport K h, f h n) =
          (∑ n ∈ varyingCoordinateSupport K m, f m n) *
            ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
              ∑ n ∈ varyingCoordinateSupport K h, f h n by
        exact (Finset.mul_prod_erase Finset.univ
          (fun h : nearShifts K =>
            ∑ n ∈ varyingCoordinateSupport K h, f h n)
          (Finset.mem_univ m)).symm]
      congr 1
      · apply Finset.sum_congr rfl
        intro n hn
        simp [f]
      · apply Finset.prod_congr rfl
        intro h hh
        have hne : h ≠ m := (Finset.mem_erase.mp hh).1
        unfold coordinateEnergy
        apply Finset.sum_congr rfl
        intro n hn
        simp [f, hne]
    _ = _ := rfl

/-- Deleting one cutoff coordinate costs only one local majorant comparison,
not one comparison in every dimension. -/
theorem coordinateProductExcept_energy_le_productEnergy
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) (m : nearShifts K) :
    (∑ r ∈ varyingTupleBox K,
        coordinateProductExcept K m r ^ 2 *
          reciprocalTotientTupleWeight (nearShifts K) r) ≤
      96 * productCoordinateEnergy K := by
  rw [coordinateProductExcept_energy_eq]
  have hmass := varyingCoordinateReciprocalMass_le_majorant K m
  have hlocal := varyingMajorant_le_ninetySix_energy hA hreg m
  have hrest : 0 ≤
      ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
        coordinateEnergy K h :=
    Finset.prod_nonneg fun h hh => coordinateEnergy_nonneg K h
  calc
    varyingCoordinateReciprocalMass K m *
        ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          coordinateEnergy K h ≤
      (96 * coordinateEnergy K m) *
        ∏ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          coordinateEnergy K h := by
      exact mul_le_mul_of_nonneg_right (hmass.trans hlocal) hrest
    _ = 96 * productCoordinateEnergy K := by
      unfold productCoordinateEnergy
      have hsplit := Finset.mul_prod_erase Finset.univ
        (fun h : nearShifts K => coordinateEnergy K h) (Finset.mem_univ m)
      rw [← hsplit]
      ring

/-- Every coordinate energy is bounded below by `1/16`. -/
theorem one_sixteenth_le_coordinateEnergy {K : ℕ}
    (hK : 0 < K) (h : nearShifts K) :
    (1 / 16 : ℝ) ≤ coordinateEnergy K h := by
  have hinner := one_le_innerCoordinateMajorant K h
  have henergy := sixteenth_innerMajorant_le_coordinateEnergy hK h
  nlinarith

/-- Pointwise one-prime estimate retaining the cutoff product in all
unchanged coordinates. -/
theorem sq_mediumSingleTransformY_le_sharp
    {K p : ℕ} (hK : 0 < K) (hp : p.Prime)
    (hpCut : tinyCutoff K < p) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) {r : nearShifts K → ℕ}
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K * p) r)
    (hrBox : r ∈ varyingTupleBox K) :
    mediumSingleTransformY K m p r ^ 2 ≤
      8 * primeLogDisplacement K m p ^ 2 *
          coordinateProductExcept K m r ^ 2 +
        2 * ((K : ℝ) / (p - 1 : ℕ)) ^ 2 := by
  let X := sieveY K r - sieveY K (insertTuplePrime p m r)
  let Y := ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
    sieveY K (insertTuplePrime p h r) / (Nat.totient p : ℝ)
  let δ := primeLogDisplacement K m p
  have hrBase : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) r :=
    isMaynard_base_of_enlarged (dvd_mul_right (preSieveModulus K) p) hr
  have hrp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (preSieveModulus K) (insertTuplePrime p m r) :=
    insertPrime_isMaynard_base hK hp hpCut (dvd_refl _) hr hrBox m hpRadius
  have hXsq : X ^ 2 ≤ 4 * δ ^ 2 * coordinateProductExcept K m r ^ 2 := by
    dsimp [X, δ]
    rw [maynardYValue_sieve_eq_coordinateProduct hrBase,
      maynardYValue_sieve_eq_coordinateProduct hrp]
    exact sq_coordinateProduct_firstDifference_le hp.one_le m
      (varyingTupleBox_coordinate hrBox m).2.1
  have hYabs : |Y| ≤ (K : ℝ) / (p - 1 : ℕ) := by
    dsimp [Y]
    rw [Nat.totient_prime hp]
    calc
      |∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          sieveY K (insertTuplePrime p h r) / ((p - 1 : ℕ) : ℝ)| ≤
          ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            |sieveY K (insertTuplePrime p h r) /
              ((p - 1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          (1 : ℝ) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro h hh
        rw [abs_div, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right (abs_sieveY_le_one K _) (by positivity)
      _ ≤ ∑ _h : nearShifts K, (1 : ℝ) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro h hh hnot
        positivity
      _ = (K : ℝ) / (p - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  have hYsq : Y ^ 2 ≤ ((K : ℝ) / (p - 1 : ℕ)) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hYabs
  have htotal : mediumSingleTransformY K m p r = X + Y := by
    simpa [mediumSingleTransformY, X, Y] using
      differencePrimeY_eq_firstDifference_add_cross hp m (sieveY K) hr
  rw [htotal]
  nlinarith [sq_nonneg (X - Y)]

/-- Sharp one-prime energy: the logarithmic finite difference has only an
absolute loss.  The factor `96 ^ K` occurs solely on the cross-coordinate
remainder, which contains the reciprocal prime factor. -/
theorem varyingYEnergy_mediumSingleTransformY_le_sharp
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p : ℕ} (hreg : NormalizationRegular A K) (hp : p.Prime)
    (hpCut : tinyCutoff K < p) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) :
    varyingYEnergy K (mediumSingleTransformY K m p) ≤
      768 * primeLogDisplacement K m p ^ 2 * productCoordinateEnergy K +
        2 * ((K : ℝ) / (p - 1 : ℕ)) ^ 2 *
          (96 ^ K * productCoordinateEnergy K) := by
  let C : ℝ := 8 * primeLogDisplacement K m p ^ 2
  let D : ℝ := 2 * ((K : ℝ) / (p - 1 : ℕ)) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hprincipal := coordinateProductExcept_energy_le_productEnergy hA hreg m
  have hweight := varyingTupleReciprocalWeightSum_le K
  have hmajorant := varyingMajorantProduct_le_energy hA hreg
  calc
    varyingYEnergy K (mediumSingleTransformY K m p) ≤
        ∑ r ∈ varyingTupleBox K,
          (C * coordinateProductExcept K m r ^ 2 + D) *
            reciprocalTotientTupleWeight (nearShifts K) r := by
      unfold varyingYEnergy
      apply Finset.sum_le_sum
      intro r hrBox
      apply mul_le_mul_of_nonneg_right _ (by
        unfold reciprocalTotientTupleWeight
        positivity)
      by_cases hz : mediumSingleTransformY K m p r = 0
      · rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
        exact add_nonneg (mul_nonneg hC (sq_nonneg _)) hD
      · have hr := mediumSingleTransformY_supported K m p r hz
        simpa [C, D, mul_assoc] using
          sq_mediumSingleTransformY_le_sharp hreg.1 hp hpCut m hpRadius hr hrBox
    _ = C * (∑ r ∈ varyingTupleBox K,
          coordinateProductExcept K m r ^ 2 *
            reciprocalTotientTupleWeight (nearShifts K) r) +
        D * (∑ r ∈ varyingTupleBox K,
          reciprocalTotientTupleWeight (nearShifts K) r) := by
      rw [show (∑ r ∈ varyingTupleBox K,
          (C * coordinateProductExcept K m r ^ 2 + D) *
            reciprocalTotientTupleWeight (nearShifts K) r) =
          (∑ r ∈ varyingTupleBox K,
            C * (coordinateProductExcept K m r ^ 2 *
              reciprocalTotientTupleWeight (nearShifts K) r)) +
          ∑ r ∈ varyingTupleBox K,
            D * reciprocalTotientTupleWeight (nearShifts K) r by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        ring]
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ C * (96 * productCoordinateEnergy K) +
        D * (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hprincipal hC)
        (mul_le_mul_of_nonneg_left hweight hD)
    _ ≤ C * (96 * productCoordinateEnergy K) +
        D * (96 ^ K * productCoordinateEnergy K) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hmajorant hD)
    _ = 768 * primeLogDisplacement K m p ^ 2 * productCoordinateEnergy K +
        2 * ((K : ℝ) / (p - 1 : ℕ)) ^ 2 *
          (96 ^ K * productCoordinateEnergy K) := by
      dsimp [C, D]
      ring

/-- Pointwise two-prime estimate retaining the cutoff product on the
principal mixed finite difference.  Only the two genuine cross-coordinate
remainders are bounded uniformly. -/
theorem sq_mediumPairTransformY_le_sharp
    {K p q : ℕ} (hK : 0 < K) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hpCut : tinyCutoff K < p)
    (hqCut : tinyCutoff K < q) (m : nearShifts K)
    (hpRadius : p < shiftRadius K m) (hqRadius : q < shiftRadius K m)
    {r : nearShifts K → ℕ}
    (hr : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      ((preSieveModulus K * p) * q) r)
    (hrBox : r ∈ varyingTupleBox K) :
    mediumPairTransformY K m p q r ^ 2 ≤
      64 * primeLogDisplacement K m p * primeLogDisplacement K m q *
          coordinateProductExcept K m r ^ 2 +
        4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
          (p - 1 : ℕ)) ^ 2 +
        2 * ((K : ℝ) *
          (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
          (q - 1 : ℕ)) ^ 2 := by
  let W := preSieveModulus K
  let y := sieveY K
  let zp := differencePrimeY (globalRadius K) W p m y
  let δp := primeLogDisplacement K m p
  let δq := primeLogDisplacement K m q
  let X := y r - y (insertTuplePrime p m r) -
    y (insertTuplePrime q m r) +
      y (insertTuplePrime q m (insertTuplePrime p m r))
  let Y := ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
    (y (insertTuplePrime p h r) -
      y (insertTuplePrime q m (insertTuplePrime p h r))) /
        (Nat.totient p : ℝ)
  let Z := ∑ h ∈ (Finset.univ : Finset (nearShifts K)).erase m,
    zp (insertTuplePrime q h r) / (Nat.totient q : ℝ)
  let B := 2 * δp + (K : ℝ) / (p - 1 : ℕ)
  have hpR : p ≤ radiusProduct K :=
    hpRadius.le.trans (shiftRadius_le_radiusProduct m)
  have hqR : q ≤ radiusProduct K :=
    hqRadius.le.trans (shiftRadius_le_radiusProduct m)
  have hrW : IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W r :=
    isMaynard_base_of_enlarged
      ((dvd_mul_right W p).trans (dvd_mul_right (W * p) q)) hr
  have hrWp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (W * p) r :=
    ⟨hr.1, hr.2.1.coprime_dvd_right (dvd_mul_right (W * p) q), hr.2.2⟩
  have hpIns : ∀ i : nearShifts K,
      IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W
        (insertTuplePrime p i r) := fun i =>
    insertPrime_isMaynard_base_of_le_radiusProduct hK hp hpCut
      (dvd_mul_right (W * p) q) hr hrBox i hpR
  have hqDiv : W * q ∣ (W * p) * q := by
    refine ⟨p, ?_⟩
    ring
  have hqIns : ∀ i : nearShifts K,
      IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W
        (insertTuplePrime q i r) := fun i =>
    insertPrime_isMaynard_base_of_le_radiusProduct hK hq hqCut
      hqDiv hr hrBox i hqR
  have hpqIns : ∀ i j : nearShifts K,
      IsMaynardDivisorTuple (nearShifts K) (globalRadius K) W
        (insertTuplePrime q j (insertTuplePrime p i r)) := fun i j =>
    insertTwoPrimes_isMaynard_base hK hp hq hpq hpCut hqCut
      (dvd_refl _) hr hrBox i j hpR hqR
  have hcommSame : insertTuplePrime p m (insertTuplePrime q m r) =
      insertTuplePrime q m (insertTuplePrime p m r) := by
    funext i
    by_cases hi : i = m
    · subst i
      simp only [insertTuplePrime_apply_same]
      ring
    · simp [insertTuplePrime, hi]
  have hcommCross : ∀ i : nearShifts K, i ≠ m →
      insertTuplePrime p i (insertTuplePrime q m r) =
        insertTuplePrime q m (insertTuplePrime p i r) := by
    intro i him
    funext j
    by_cases hji : j = i
    · subst j
      simp [insertTuplePrime, him]
    · by_cases hjm : j = m
      · subst j
        simp [insertTuplePrime, him, Ne.symm him]
      · simp [insertTuplePrime, hji, hjm]
  have hqrWp : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
      (W * p) (insertTuplePrime q m r) := by
    have hqd : Nat.Coprime q (divisorTupleProduct (nearShifts K) r) := by
      have hc := hr.2.1.coprime_dvd_right
        ((dvd_mul_left q (W * p)).trans (dvd_refl ((W * p) * q)))
      exact hc.symm
    have hqWp : Nat.Coprime q (W * p) := by
      rw [Nat.coprime_mul_iff_right]
      exact ⟨prime_coprime_preSieveModulus hq hqCut,
        (Nat.coprime_primes hq hp).2 (Ne.symm hpq)⟩
    have hrWpCop : Nat.Coprime (divisorTupleProduct (nearShifts K) r)
        (W * p) := hrWp.2.1
    refine ⟨?_, ?_, ?_⟩
    · rw [divisorTupleProduct_insertTuplePrime]
      calc
        q * divisorTupleProduct (nearShifts K) r ≤
            radiusProduct K * radiusProduct K :=
          Nat.mul_le_mul hqR (varyingTupleBox_product_le_radiusProduct hrBox)
        _ = radiusProduct K ^ 2 := by ring
        _ < globalRadius K := radiusProduct_pow_lt_globalRadius hK (by norm_num)
    · rw [divisorTupleProduct_insertTuplePrime,
        Nat.coprime_mul_iff_left]
      exact ⟨hqWp, hrWpCop⟩
    · rw [divisorTupleProduct_insertTuplePrime]
      exact (Nat.squarefree_mul hqd).2 ⟨hq.squarefree, hr.2.2⟩
  have hXeq : X =
      (coordinateCutoff K m (r m) -
          coordinateCutoff K m (p * r m) -
          coordinateCutoff K m (q * r m) +
          coordinateCutoff K m (q * (p * r m))) *
        coordinateProductExcept K m r := by
    dsimp [X, y]
    exact sieveY_secondDifference_eq m r hrW (hpIns m) (hqIns m) (hpqIns m m)
  have hXsq : X ^ 2 ≤
      16 * δp * δq * coordinateProductExcept K m r ^ 2 := by
    rw [hXeq, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (sq_coordinateCutoff_secondDifference_le hp.one_le hq.one_le
        (varyingTupleBox_coordinate hrBox m).2.1 m)
      (sq_nonneg _)
  have hcrossEach : ∀ i : nearShifts K, i ≠ m →
      |y (insertTuplePrime p i r) -
        y (insertTuplePrime q m (insertTuplePrime p i r))| ≤ 2 * δq := by
    intro i him
    rw [sieveY_firstDifference_eq m (insertTuplePrime p i r)
      (hpIns i) (hpqIns i m), abs_mul,
      abs_of_nonneg (coordinateProductExcept_nonneg K m
        (insertTuplePrime p i r))]
    have hcoord : insertTuplePrime p i r m = r m :=
      insertTuplePrime_apply_ne p (Ne.symm him) r
    rw [hcoord]
    exact (mul_le_mul
      (coordinateCutoff_mul_sub_le hq.one_le
        (varyingTupleBox_coordinate hrBox m).2.1 m)
      (coordinateProductExcept_le_one K m (insertTuplePrime p i r))
      (coordinateProductExcept_nonneg K m (insertTuplePrime p i r))
      (mul_nonneg (by norm_num)
        (primeLogDisplacement_nonneg hq.one_le m))).trans_eq (by ring)
  have hYabs : |Y| ≤
      2 * (K : ℝ) * δq / (p - 1 : ℕ) := by
    dsimp [Y]
    rw [Nat.totient_prime hp]
    calc
      |∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          (y (insertTuplePrime p i r) -
            y (insertTuplePrime q m (insertTuplePrime p i r))) /
              ((p - 1 : ℕ) : ℝ)| ≤
          ∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            |(y (insertTuplePrime p i r) -
              y (insertTuplePrime q m (insertTuplePrime p i r))) /
                ((p - 1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          (2 * δq) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_div, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right
          (hcrossEach i (Finset.mem_erase.mp hi).1) (by positivity)
      _ ≤ ∑ _i : nearShifts K, (2 * δq) / (p - 1 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro i hi hnot
        exact div_nonneg
          (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hq.one_le m))
          (by positivity)
      _ = 2 * (K : ℝ) * δq / (p - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  have hzpCross : ∀ i : nearShifts K, i ≠ m →
      |zp (insertTuplePrime q i r)| ≤ B := by
    intro i him
    by_cases hz : zp (insertTuplePrime q i r) = 0
    · simp [hz, B]
      exact add_nonneg
        (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp.one_le m))
        (div_nonneg (by positivity) (by positivity))
    · have hsup : IsMaynardDivisorTuple (nearShifts K) (globalRadius K)
          (W * p) (insertTuplePrime q i r) := by
        exact differencePrimeY_supported (globalRadius K) W p m y _ hz
      have hlt : ∀ j : nearShifts K,
          insertTuplePrime q i r j < shiftRadius K j :=
        differencePrimeY_varyingSupported hp.pos (sieveY_varyingSupported K) m hz
      have hbox : insertTuplePrime q i r ∈ varyingTupleBox K :=
        varyingTupleBox_of_isMaynard_of_lt (dvd_mul_right W p) hsup hlt
      simpa [zp, B, δp, W, y] using
        abs_differencePrimeY_sieveY_le hK hp hpCut m hpRadius hsup hbox
  have hZabs : |Z| ≤ (K : ℝ) * B / (q - 1 : ℕ) := by
    dsimp [Z]
    rw [Nat.totient_prime hq]
    calc
      |∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          zp (insertTuplePrime q i r) / ((q - 1 : ℕ) : ℝ)| ≤
          ∑ i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
            |zp (insertTuplePrime q i r) /
              ((q - 1 : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (nearShifts K)).erase m,
          B / (q - 1 : ℕ) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_div, abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ ((q - 1 : ℕ) : ℝ))]
        exact div_le_div_of_nonneg_right
          (hzpCross i (Finset.mem_erase.mp hi).1) (by positivity)
      _ ≤ ∑ _i : nearShifts K, B / (q - 1 : ℕ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        intro i hi hnot
        dsimp [B, δp]
        exact div_nonneg
          (add_nonneg
            (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp.one_le m))
            (div_nonneg (by positivity) (by positivity)))
          (by positivity)
      _ = (K : ℝ) * B / (q - 1 : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
          nearShifts_card]
        simp only [nsmul_eq_mul]
        ring
  have hinnerEq : zp r - zp (insertTuplePrime q m r) = X + Y := by
    have hsums :
        (∑ i ∈ (nearShifts K).attach.erase m,
            y (insertTuplePrime p i r) / (Nat.totient p : ℝ)) -
          (∑ i ∈ (nearShifts K).attach.erase m,
            y (insertTuplePrime p i (insertTuplePrime q m r)) /
              (Nat.totient p : ℝ)) =
          ∑ i ∈ (nearShifts K).attach.erase m,
            (y (insertTuplePrime p i r) -
              y (insertTuplePrime q m (insertTuplePrime p i r))) /
                (Nat.totient p : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcommCross i (Finset.mem_erase.mp hi).1]
      ring
    dsimp only [zp]
    rw [differencePrimeY_eq_firstDifference_add_cross hp m y hrWp,
      differencePrimeY_eq_firstDifference_add_cross hp m y hqrWp]
    dsimp [X, Y]
    rw [hcommSame]
    linear_combination hsums
  have htotalEq : mediumPairTransformY K m p q r = X + Y + Z := by
    have hout := iteratedDifferencePrimeY_eq_firstDifference_add_cross hq m y hr
    rw [show mediumPairTransformY K m p q r =
        zp r - zp (insertTuplePrime q m r) + Z by
      simpa [mediumPairTransformY, zp, Z, W, y] using hout]
    rw [hinnerEq]
  rw [htotalEq]
  have hXY : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (X - Y)]
  have hXYZ : (X + Y + Z) ^ 2 ≤ 2 * (X + Y) ^ 2 + 2 * Z ^ 2 := by
    nlinarith [sq_nonneg (X + Y - Z)]
  have hYsq : Y ^ 2 ≤
      (2 * (K : ℝ) * δq / (p - 1 : ℕ)) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _)
      (by dsimp [δq]
          exact div_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
              (primeLogDisplacement_nonneg hq.one_le m))
            (by positivity) :
        0 ≤ 2 * (K : ℝ) * δq / (p - 1 : ℕ))).mpr hYabs
  have hZsq : Z ^ 2 ≤ ((K : ℝ) * B / (q - 1 : ℕ)) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _)
      (by dsimp [B, δp]
          exact div_nonneg
            (mul_nonneg (by positivity)
              (add_nonneg
                (mul_nonneg (by norm_num)
                  (primeLogDisplacement_nonneg hp.one_le m))
                (div_nonneg (by positivity) (by positivity))))
            (by positivity) :
        0 ≤ (K : ℝ) * B / (q - 1 : ℕ))).mpr hZabs
  dsimp [δp, δq, B] at hXsq hYsq hZsq ⊢
  nlinarith

/-- Sharp two-prime energy.  The principal mixed finite difference costs
only the single absolute factor from the distinguished coordinate; all
`96 ^ K` loss is attached to cross terms carrying a reciprocal prime
denominator. -/
theorem varyingYEnergy_mediumPairTransformY_le_sharp
    {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K p q : ℕ} (hreg : NormalizationRegular A K)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpCut : tinyCutoff K < p) (hqCut : tinyCutoff K < q)
    (m : nearShifts K) (hpRadius : p < shiftRadius K m)
    (hqRadius : q < shiftRadius K m) :
    varyingYEnergy K (mediumPairTransformY K m p q) ≤
      6144 * primeLogDisplacement K m p * primeLogDisplacement K m q *
          productCoordinateEnergy K +
        (4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
            (p - 1 : ℕ)) ^ 2 +
          2 * ((K : ℝ) *
            (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
            (q - 1 : ℕ)) ^ 2) *
          (96 ^ K * productCoordinateEnergy K) := by
  let C : ℝ :=
    64 * primeLogDisplacement K m p * primeLogDisplacement K m q
  let D : ℝ :=
    4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
        (p - 1 : ℕ)) ^ 2 +
      2 * ((K : ℝ) *
        (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
        (q - 1 : ℕ)) ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (primeLogDisplacement_nonneg hp.one_le m))
      (primeLogDisplacement_nonneg hq.one_le m)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hprincipal := coordinateProductExcept_energy_le_productEnergy hA hreg m
  have hweight := varyingTupleReciprocalWeightSum_le K
  have hmajorant := varyingMajorantProduct_le_energy hA hreg
  calc
    varyingYEnergy K (mediumPairTransformY K m p q) ≤
        ∑ r ∈ varyingTupleBox K,
          (C * coordinateProductExcept K m r ^ 2 + D) *
            reciprocalTotientTupleWeight (nearShifts K) r := by
      unfold varyingYEnergy
      apply Finset.sum_le_sum
      intro r hrBox
      apply mul_le_mul_of_nonneg_right _ (by
        unfold reciprocalTotientTupleWeight
        positivity)
      by_cases hz : mediumPairTransformY K m p q r = 0
      · rw [hz, zero_pow (by norm_num : 2 ≠ 0)]
        exact add_nonneg (mul_nonneg hC (sq_nonneg _)) hD
      · have hr := mediumPairTransformY_supported K m p q r hz
        simpa [C, D, mul_assoc, add_assoc] using
          sq_mediumPairTransformY_le_sharp hreg.1 hp hq hpq hpCut hqCut m
            hpRadius hqRadius hr hrBox
    _ = C * (∑ r ∈ varyingTupleBox K,
          coordinateProductExcept K m r ^ 2 *
            reciprocalTotientTupleWeight (nearShifts K) r) +
        D * (∑ r ∈ varyingTupleBox K,
          reciprocalTotientTupleWeight (nearShifts K) r) := by
      rw [show (∑ r ∈ varyingTupleBox K,
          (C * coordinateProductExcept K m r ^ 2 + D) *
            reciprocalTotientTupleWeight (nearShifts K) r) =
          (∑ r ∈ varyingTupleBox K,
            C * (coordinateProductExcept K m r ^ 2 *
              reciprocalTotientTupleWeight (nearShifts K) r)) +
          ∑ r ∈ varyingTupleBox K,
            D * reciprocalTotientTupleWeight (nearShifts K) r by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        ring]
      rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ C * (96 * productCoordinateEnergy K) +
        D * (∏ h : nearShifts K, varyingCoordinateMajorant K h) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hprincipal hC)
        (mul_le_mul_of_nonneg_left hweight hD)
    _ ≤ C * (96 * productCoordinateEnergy K) +
        D * (96 ^ K * productCoordinateEnergy K) := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hmajorant hD)
    _ = 6144 * primeLogDisplacement K m p * primeLogDisplacement K m q *
          productCoordinateEnergy K +
        (4 * (2 * (K : ℝ) * primeLogDisplacement K m q /
            (p - 1 : ℕ)) ^ 2 +
          2 * ((K : ℝ) *
            (2 * primeLogDisplacement K m p + (K : ℝ) / (p - 1 : ℕ)) /
            (q - 1 : ℕ)) ^ 2) *
          (96 ^ K * productCoordinateEnergy K) := by
      dsimp [C, D]
      ring

end Erdos248
