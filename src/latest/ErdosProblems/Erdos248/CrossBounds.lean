import ErdosProblems.Erdos248.CorrelationBounds

/-!
# Erdős Problem 248: cross bounds for enlarged event moduli
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance crossBoundsDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Cross corrections after adjoining event primes

The library's sharp rough-tail identity is stated when the modulus is
literally a primorial.  Event correlations replace that modulus by the
primorial times at most four primes.  The following lemmas record the same
argument under the only property that is actually used: the primorial
divides the current modulus. -/

theorem roughCrossCoordinate_of_leftYFactor_ne_zero_of_dvd
    {H : Finset ℕ} {R W D : ℕ} {y : (H → ℕ) → ℝ}
    (hDW : primorial D ∣ W) (hy : IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hl : leftCrossYFactor H y u s ≠ 0)
    (ab : H × H) (hab : ab ∈ offDiagonalPairs H) :
    s ab hab ∈ squarefreeRoughUnitSupport D R := by
  have hlSupport := hy _ (leftCrossYFactor_ne_zero_y_ne_zero hl)
  have hsMem := (Finset.mem_pi.mp hs) ab hab
  have hsBounds := Finset.mem_Icc.mp hsMem
  let n := s ab hab
  have hnDvd : n ∣ leftCrossLowerTuple H u s ab.1 :=
    cross_dvd_leftCrossLowerTuple u s ab hab
  have hnSquarefree : Squarefree n :=
    (hlSupport.coordinate_squarefree ab.1).squarefree_of_dvd hnDvd
  have hnCoprimeW : Nat.Coprime n W :=
    Nat.Coprime.of_dvd_left hnDvd
      (hlSupport.coordinate_coprime_W ab.1)
  have hnCoprime : Nat.Coprime n (primorial D) :=
    hnCoprimeW.coprime_dvd_right hDW
  rw [squarefreeRoughUnitSupport, Finset.mem_insert]
  by_cases hnOne : n = 1
  · exact Or.inl hnOne
  · apply Or.inr
    rw [squarefreeRoughSupport, Finset.mem_filter]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, hsBounds.2⟩,
      hnSquarefree, ?_⟩
    · have hnPos : 0 < n := hsBounds.1
      omega
    · intro p hpMem
      have hpPrime := Nat.prime_of_mem_primeFactors hpMem
      have hpDvd := Nat.dvd_of_mem_primeFactors hpMem
      have hpGt : D < p :=
        prime_gt_of_dvd_coprime_primorial hpPrime hpDvd hnCoprime
      have hpLeN : p ≤ n := Nat.le_of_dvd hsBounds.1 hpDvd
      rw [roughPrimeSupport, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpLeN.trans hsBounds.2⟩,
        hpPrime⟩

theorem roughCrossTupleSupport_of_leftYFactor_ne_zero_of_dvd
    {H : Finset ℕ} {R W D : ℕ} {y : (H → ℕ) → ℝ}
    (hDW : primorial D ∣ W) (hy : IsSupportedMaynardY H R W y)
    {u : H → ℕ}
    {s : ∀ ab : H × H, ab ∈ offDiagonalPairs H → ℕ}
    (hs : s ∈ crossMoebiusTupleBox H R)
    (hl : leftCrossYFactor H y u s ≠ 0) :
    s ∈ roughCrossTupleSupport H D R := by
  rw [roughCrossTupleSupport, Finset.mem_pi]
  intro ab hab
  exact roughCrossCoordinate_of_leftYFactor_ne_zero_of_dvd
    hDW hy hs hl ab hab

theorem nontrivialStarredAuxiliaryYSum_eq_rough_of_dvd
    {H : Finset ℕ} {R W D : ℕ} {y : (H → ℕ) → ℝ}
    (hR : 0 < R) (hDW : primorial D ∣ W)
    (hy : IsSupportedMaynardY H R W y) :
    nontrivialStarredAuxiliaryYSum H R y =
      nontrivialStarredRoughAuxiliaryYSum H R D y := by
  classical
  unfold nontrivialStarredAuxiliaryYSum
    nontrivialStarredRoughAuxiliaryYSum
  apply (Finset.sum_subset
    (roughCrossTupleSupport_subset_crossMoebiusTupleBox hR) ?_).symm
  intro s hsBox hsNotRough
  by_cases hsNe : s ≠ oneCrossMoebiusTuple H
  · rw [if_pos hsNe]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hstar : IsStarredCrossTuple H u s
    · rw [if_pos hstar]
      have hl : leftCrossYFactor H y u s = 0 := by
        by_contra hl
        exact hsNotRough
          (roughCrossTupleSupport_of_leftYFactor_ne_zero_of_dvd
            hDW hy hsBox hl)
      simp [hl]
    · rw [if_neg hstar]
  · rw [if_neg hsNe]

theorem incompatibleSum_eq_neg_roughPreSieved_of_dvd
    {H : Finset ℕ} {R W D : ℕ} {y : (H → ℕ) → ℝ}
    (hR : 0 < R) (hDW : primorial D ∣ W)
    (hy : IsSupportedMaynardY H R W y) :
    incompatibleDivisorPairCommonDivisorTupleSum H
        (maynardDivisorTupleSupport H R W)
        (maynardCoefficientFromY H R W y) =
      -nontrivialStarredRoughPreSievedAuxiliaryYSum H R W D y := by
  rw [incompatibleSum_eq_neg_starredAuxiliaryYSum hy]
  rw [nontrivialStarredAuxiliaryYSum_eq_rough_of_dvd hR hDW hy]
  rw [nontrivialStarredRoughAuxiliaryYSum_eq_preSieved hy]

theorem varyingTupleBox_of_leftCrossYFactor_ne_zero_of_sharp
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    {u : nearShifts K → ℕ}
    {s : ∀ ab : nearShifts K × nearShifts K,
      ab ∈ offDiagonalPairs (nearShifts K) → ℕ}
    (hu : u ∈ preSievedCommonTupleSupport (nearShifts K) W R)
    (hl : leftCrossYFactor (nearShifts K) y u s ≠ 0) :
    u ∈ varyingTupleBox K := by
  rw [varyingTupleBox, Fintype.mem_piFinset]
  intro h
  rw [varyingCoordinateSupport, preSievedCommonCoordinateSupport,
    Finset.mem_filter]
  have huh := Fintype.mem_piFinset.mp hu h
  have huhData := Finset.mem_filter.mp huh
  have hyne : y (leftCrossLowerTuple (nearShifts K) u s) ≠ 0 :=
    leftCrossYFactor_ne_zero_y_ne_zero hl
  have hlowerLt := hySharp hyne h
  have hudvd := u_dvd_leftCrossLowerTuple (nearShifts K) u s h
  have hule : u h ≤ leftCrossLowerTuple (nearShifts K) u s h :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero ((hy _ hyne).coordinate_squarefree h).ne_zero)
      hudvd
  exact ⟨Finset.mem_range.mpr (hule.trans_lt hlowerLt),
    huhData.2.1, huhData.2.2.1,
    huhData.2.2.2.coprime_dvd_right hmod⟩

theorem abs_fixed_sharp_cross_inner_le
    {K R W D : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {s : ∀ ab : nearShifts K × nearShifts K,
      ab ∈ offDiagonalPairs (nearShifts K) → ℕ}
    (hs : s ∈ roughCrossTupleSupport (nearShifts K) D R) :
    |crossMoebiusTupleTerm (nearShifts K) s *
        ∑ u ∈ preSievedCommonTupleSupport (nearShifts K) W R,
          if IsStarredCrossTuple (nearShifts K) u s then
            (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor (nearShifts K) y u s *
              rightCrossYFactor (nearShifts K) y u s
          else 0| ≤
      B ^ 2 * crossTotientSquareWeight (nearShifts K) s *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  let P := preSievedCommonTupleSupport (nearShifts K) W R
  let A := P.filter fun u => u ∈ varyingTupleBox K
  let F : (nearShifts K → ℕ) → ℝ := fun u =>
    if IsStarredCrossTuple (nearShifts K) u s then
      (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
        leftCrossYFactor (nearShifts K) y u s *
        rightCrossYFactor (nearShifts K) y u s
    else 0
  have hsWeight : 0 ≤ crossTotientSquareWeight (nearShifts K) s := by
    unfold crossTotientSquareWeight
    exact one_div_nonneg.mpr (sq_nonneg _)
  have hfactor : 0 ≤ B ^ 2 * crossTotientSquareWeight (nearShifts K) s :=
    mul_nonneg (sq_nonneg B) hsWeight
  have hrestrict : (∑ u ∈ P, F u) = ∑ u ∈ A, F u := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro u huP huNotA
    have huNotV : u ∉ varyingTupleBox K := by
      intro huV
      exact huNotA (Finset.mem_filter.mpr ⟨huP, huV⟩)
    by_cases hstar : IsStarredCrossTuple (nearShifts K) u s
    · have hl : leftCrossYFactor (nearShifts K) y u s = 0 := by
        by_contra hlne
        exact huNotV
          (varyingTupleBox_of_leftCrossYFactor_ne_zero_of_sharp
            hmod hy hySharp huP hlne)
      simp [F, hstar, hl]
    · simp [F, hstar]
  change |crossMoebiusTupleTerm (nearShifts K) s * ∑ u ∈ P, F u| ≤ _
  rw [hrestrict, Finset.mul_sum]
  calc
    |∑ u ∈ A, crossMoebiusTupleTerm (nearShifts K) s * F u| ≤
        ∑ u ∈ A,
          |crossMoebiusTupleTerm (nearShifts K) s * F u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ A,
        B ^ 2 * crossTotientSquareWeight (nearShifts K) s *
          ((1 : ℝ) / commonTotientProduct (nearShifts K) u) := by
      apply Finset.sum_le_sum
      intro u hu
      have huP : u ∈ P := (Finset.mem_filter.mp hu).1
      by_cases hstar : IsStarredCrossTuple (nearShifts K) u s
      · rw [show F u =
            (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
              leftCrossYFactor (nearShifts K) y u s *
              rightCrossYFactor (nearShifts K) y u s by simp [F, hstar]]
        simpa [commonTotientProduct, mul_assoc] using
          (abs_starredCrossYSummand_le_separated
            (H := nearShifts K) (y := y) (B := B)
            (W := W) (R := R) (D := D) hB hyBound huP hs hstar)
      · rw [show F u = 0 by simp [F, hstar]]
        simp only [mul_zero, abs_zero]
        exact mul_nonneg hfactor (by positivity)
    _ ≤ ∑ u ∈ varyingTupleBox K,
        B ^ 2 * crossTotientSquareWeight (nearShifts K) s *
          ((1 : ℝ) / commonTotientProduct (nearShifts K) u) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        exact (Finset.mem_filter.mp hu).2
      · intro u hu hnot
        exact mul_nonneg hfactor (by positivity)
    _ = B ^ 2 * crossTotientSquareWeight (nearShifts K) s *
        (∑ u ∈ varyingTupleBox K,
          ((1 : ℝ) / commonTotientProduct (nearShifts K) u)) := by
      rw [Finset.mul_sum]
    _ ≤ B ^ 2 * crossTotientSquareWeight (nearShifts K) s *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      exact mul_le_mul_of_nonneg_left (varyingTupleInvTotientMass_le K)
        hfactor

theorem abs_incompatibleSum_le_sharp_varying
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ} {B : ℝ}
    (hR : 0 < R)
    (hmod : preSieveModulus K ∣ W)
    (hy : IsSupportedMaynardY (nearShifts K) R W y)
    (hySharp : IsVaryingSupported K y)
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B) :
    |incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
        (maynardDivisorTupleSupport (nearShifts K) R W)
        (maynardCoefficientFromY (nearShifts K) R W y)| ≤
      B ^ 2 * roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) R *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  rw [incompatibleSum_eq_neg_roughPreSieved_of_dvd
    (H := nearShifts K) (D := tinyCutoff K) hR
    (by simpa [preSieveModulus] using hmod) hy, abs_neg]
  rw [nontrivialStarredRoughPreSievedAuxiliaryYSum_eq_erase]
  calc
    |∑ s ∈ (roughCrossTupleSupport (nearShifts K) (tinyCutoff K) R).erase
          (oneCrossMoebiusTuple (nearShifts K)),
        crossMoebiusTupleTerm (nearShifts K) s *
          ∑ u ∈ preSievedCommonTupleSupport (nearShifts K) W R,
            if IsStarredCrossTuple (nearShifts K) u s then
              (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
                leftCrossYFactor (nearShifts K) y u s *
                rightCrossYFactor (nearShifts K) y u s
            else 0| ≤
        ∑ s ∈ (roughCrossTupleSupport (nearShifts K) (tinyCutoff K) R).erase
          (oneCrossMoebiusTuple (nearShifts K)),
          |crossMoebiusTupleTerm (nearShifts K) s *
            ∑ u ∈ preSievedCommonTupleSupport (nearShifts K) W R,
              if IsStarredCrossTuple (nearShifts K) u s then
                (∏ h : nearShifts K, (Nat.totient (u h) : ℝ)) *
                  leftCrossYFactor (nearShifts K) y u s *
                  rightCrossYFactor (nearShifts K) y u s
              else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ (roughCrossTupleSupport (nearShifts K) (tinyCutoff K) R).erase
          (oneCrossMoebiusTuple (nearShifts K)),
        B ^ 2 * crossTotientSquareWeight (nearShifts K) s *
          ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      apply Finset.sum_le_sum
      intro s hs
      exact abs_fixed_sharp_cross_inner_le hmod hy hySharp hB hyBound
        (Finset.mem_of_mem_erase hs)
    _ = B ^ 2 * roughCrossTupleTotientSquareTail (nearShifts K)
          (tinyCutoff K) R *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      unfold roughCrossTupleTotientSquareTail
      rw [← Finset.sum_mul, ← Finset.mul_sum]

end Erdos248
