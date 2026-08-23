import ErdosProblems.Erdos248.Correlation

/-!
# Erdős Problem 248: quantitative correlation bounds

The product cutoff makes the unrestricted `Y`-diagonal a product of
one-dimensional energies.  Keeping those energies explicit is essential:
all unchanged coordinates then cancel in correlation ratios, avoiding any
loss exponential in the dimension.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance correlationBoundsDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The one-dimensional cutoff factor in coordinate `h`. -/
def coordinateCutoff (K : ℕ) (h : nearShifts K) (n : ℕ) : ℝ :=
  selbergCutoff (((100 ^ (h : ℕ) : ℕ) : ℝ) *
    (Real.log n / Real.log (globalRadius K)))

/-- Reciprocal-totient `L²` energy of one coordinate cutoff. -/
def coordinateEnergy (K : ℕ) (h : nearShifts K) : ℝ :=
  ∑ n ∈ varyingCoordinateSupport K h,
    coordinateCutoff K h n ^ 2 / Nat.totient n

/-- Product of the coordinate energies. -/
def productCoordinateEnergy (K : ℕ) : ℝ :=
  ∏ h : nearShifts K, coordinateEnergy K h

theorem coordinateCutoff_nonneg (K : ℕ) (h : nearShifts K) (n : ℕ) :
    0 ≤ coordinateCutoff K h n :=
  selbergCutoff_nonneg _

theorem coordinateCutoff_le_one (K : ℕ) (h : nearShifts K) (n : ℕ) :
    coordinateCutoff K h n ≤ 1 :=
  selbergCutoff_le_one _

theorem coordinateEnergy_nonneg (K : ℕ) (h : nearShifts K) :
    0 ≤ coordinateEnergy K h := by
  unfold coordinateEnergy
  positivity

theorem productCoordinateEnergy_nonneg (K : ℕ) :
    0 ≤ productCoordinateEnergy K := by
  unfold productCoordinateEnergy
  exact Finset.prod_nonneg fun h _ => coordinateEnergy_nonneg K h

theorem tupleCutoff_eq_coordinateProduct (K : ℕ)
    (u : nearShifts K → ℕ) :
    tupleCutoff K
        (fun h => Real.log (u h) / Real.log (globalRadius K)) =
      ∏ h : nearShifts K, coordinateCutoff K h (u h) := by
  rfl

theorem coordinateEnergy_le_varyingMajorant (K : ℕ)
    (h : nearShifts K) :
    coordinateEnergy K h ≤ varyingCoordinateMajorant K h := by
  unfold coordinateEnergy varyingCoordinateMajorant
    squarefreeCoprimeInvTotientMean varyingCoordinateSupport
  calc
    (∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
          (shiftRadius K h),
        coordinateCutoff K h n ^ 2 / Nat.totient n) ≤
        ∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
          (shiftRadius K h),
          (1 : ℝ) / Nat.totient n := by
      apply Finset.sum_le_sum
      intro n hn
      have hcut0 := coordinateCutoff_nonneg K h n
      have hcut1 := coordinateCutoff_le_one K h n
      have hsq : coordinateCutoff K h n ^ 2 ≤ 1 := by nlinarith
      have htot : (0 : ℝ) ≤ Nat.totient n := by positivity
      exact div_le_div_of_nonneg_right hsq htot
    _ ≤ ∑ n ∈ Finset.Icc 1 (shiftRadius K h),
        if Squarefree n ∧ Nat.Coprime n (preSieveModulus K) then
          (1 : ℝ) / Nat.totient n else 0 := by
      rw [show (∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
          (shiftRadius K h), (1 : ℝ) / Nat.totient n) =
          ∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
            (shiftRadius K h),
            if Squarefree n ∧ Nat.Coprime n (preSieveModulus K) then
              (1 : ℝ) / Nat.totient n else 0 by
        apply Finset.sum_congr rfl
        intro n hn
        have hnData := Finset.mem_filter.mp hn
        rw [if_pos ⟨hnData.2.2.1, hnData.2.2.2⟩]]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnData := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨hnData.2.1,
          (Finset.mem_range.mp hnData.1).le⟩
      · intro n hn hnot
        split_ifs <;> positivity
    _ = _ := rfl

/-- Every point of the inner coordinate box belongs to the varying support. -/
theorem innerCoordinateSupport_subset_varying {K : ℕ} (hK : 0 < K)
    (h : nearShifts K) :
    innerCoordinateSupport K h ⊆ varyingCoordinateSupport K h := by
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hnIcc := Finset.mem_Icc.mp hnData.1
  have hinnerLt : innerShiftRadius K h < shiftRadius K h := by
    rw [← innerShiftRadius_sq hK (mem_nearShifts.mp h.property).2]
    nlinarith [one_lt_innerShiftRadius K h]
  rw [varyingCoordinateSupport, preSievedCommonCoordinateSupport,
    Finset.mem_filter]
  exact ⟨Finset.mem_range.mpr
      (hnIcc.2.trans_lt hinnerLt),
    hnIcc.1, hnData.2.1, hnData.2.2⟩

theorem quarter_le_coordinateCutoff_inner {K : ℕ} (hK : 0 < K)
    (h : nearShifts K) {n : ℕ} (hn : n ∈ innerCoordinateSupport K h) :
    (1 / 4 : ℝ) ≤ coordinateCutoff K h n := by
  have hnData := Finset.mem_filter.mp hn
  have hnIcc := Finset.mem_Icc.mp hnData.1
  have hglobalLog : 0 < Real.log (globalRadius K) :=
    Real.log_pos (by exact_mod_cast one_lt_globalRadius K)
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hnIcc.1
  have hinnerReal : (0 : ℝ) < innerShiftRadius K h := by
    exact_mod_cast innerShiftRadius_pos K h
  have hlogNonneg : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogLe : Real.log n ≤ Real.log (innerShiftRadius K h) :=
    Real.strictMonoOn_log.monotoneOn hnReal hinnerReal
      (by exact_mod_cast hnIcc.2)
  have hdivLe := (div_le_div_iff_of_pos_right hglobalLog).2 hlogLe
  have hfactor : (0 : ℝ) < ((100 ^ (h : ℕ) : ℕ) : ℝ) := by positivity
  apply quarter_le_selbergCutoff
  · exact mul_nonneg hfactor.le (div_nonneg hlogNonneg hglobalLog.le)
  · calc
      ((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (Real.log n / Real.log (globalRadius K)) ≤
          ((100 ^ (h : ℕ) : ℕ) : ℝ) *
            (Real.log (innerShiftRadius K h) /
              Real.log (globalRadius K)) :=
        mul_le_mul_of_nonneg_left hdivLe hfactor.le
      _ = ((100 ^ (h : ℕ) : ℕ) : ℝ) *
          (1 / (2 * ((100 ^ (h : ℕ) : ℕ) : ℝ))) := by
        rw [log_innerShiftRadius_div_log_globalRadius hK
          (mem_nearShifts.mp h.property).2]
      _ = 1 / 2 := by field_simp

theorem sixteenth_innerMajorant_le_coordinateEnergy {K : ℕ}
    (hK : 0 < K) (h : nearShifts K) :
    (1 / 16 : ℝ) * innerCoordinateMajorant K h ≤
      coordinateEnergy K h := by
  rw [← innerCoordinateMass_eq_majorant]
  unfold coordinateEnergy
  calc
    (1 / 16 : ℝ) *
        (∑ n ∈ innerCoordinateSupport K h,
          (1 : ℝ) / Nat.totient n) =
        ∑ n ∈ innerCoordinateSupport K h,
          (1 / 16 : ℝ) * ((1 : ℝ) / Nat.totient n) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ innerCoordinateSupport K h,
        coordinateCutoff K h n ^ 2 / Nat.totient n := by
      apply Finset.sum_le_sum
      intro n hn
      have hcut := quarter_le_coordinateCutoff_inner hK h hn
      have hcut0 := coordinateCutoff_nonneg K h n
      have hsq : (1 / 16 : ℝ) ≤ coordinateCutoff K h n ^ 2 := by
        nlinarith
      have htot : (0 : ℝ) ≤ Nat.totient n := by positivity
      calc
        (1 / 16 : ℝ) * ((1 : ℝ) / Nat.totient n) =
            (1 / 16 : ℝ) / Nat.totient n := by ring
        _ ≤ coordinateCutoff K h n ^ 2 / Nat.totient n :=
          div_le_div_of_nonneg_right hsq htot
    _ ≤ ∑ n ∈ varyingCoordinateSupport K h,
        coordinateCutoff K h n ^ 2 / Nat.totient n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (innerCoordinateSupport_subset_varying hK h)
      intro n hn hnot
      positivity

/-- The unrestricted varying-box cutoff energy. -/
def varyingCutoffEnergy (K : ℕ) : ℝ :=
  ∑ u ∈ varyingTupleBox K,
    tupleCutoff K
        (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 *
      reciprocalTotientTupleWeight (nearShifts K) u

/-- The part of the varying-box cutoff energy lost to a prime collision
between two coordinates. -/
def varyingCutoffCollisionEnergy (K : ℕ) : ℝ :=
  ∑ u ∈ (varyingTupleBox K).filter fun u =>
      ¬Squarefree (divisorTupleProduct (nearShifts K) u),
    tupleCutoff K
        (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 *
      reciprocalTotientTupleWeight (nearShifts K) u

theorem cutoff_reciprocalWeight_eq_coordinateProduct (K : ℕ)
    (u : nearShifts K → ℕ) :
    tupleCutoff K
        (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 *
        reciprocalTotientTupleWeight (nearShifts K) u =
      ∏ h : nearShifts K,
        (coordinateCutoff K h (u h) ^ 2 / Nat.totient (u h)) := by
  rw [tupleCutoff_eq_coordinateProduct]
  unfold reciprocalTotientTupleWeight
  rw [← Finset.prod_pow]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h hh
  ring

theorem varyingCutoffEnergy_eq_product (K : ℕ) :
    varyingCutoffEnergy K = productCoordinateEnergy K := by
  unfold varyingCutoffEnergy varyingTupleBox productCoordinateEnergy
  calc
    (∑ u ∈ Fintype.piFinset (varyingCoordinateSupport K),
        tupleCutoff K
            (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 *
          reciprocalTotientTupleWeight (nearShifts K) u) =
        ∑ u ∈ Fintype.piFinset (varyingCoordinateSupport K),
          ∏ h : nearShifts K,
            (coordinateCutoff K h (u h) ^ 2 / Nat.totient (u h)) := by
      apply Finset.sum_congr rfl
      intro u hu
      exact cutoff_reciprocalWeight_eq_coordinateProduct K u
    _ = ∏ h : nearShifts K,
        ∑ n ∈ varyingCoordinateSupport K h,
          coordinateCutoff K h n ^ 2 / Nat.totient n := by
      exact (Finset.prod_univ_sum (varyingCoordinateSupport K)
        (fun h n => coordinateCutoff K h n ^ 2 / Nat.totient n)).symm
    _ = _ := rfl

theorem varyingCutoffCollisionEnergy_nonneg (K : ℕ) :
    0 ≤ varyingCutoffCollisionEnergy K := by
  unfold varyingCutoffCollisionEnergy
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (sq_nonneg _) (by
    unfold reciprocalTotientTupleWeight
    positivity)

/-- The independent part of the varying box is contained in the actual
Maynard support. -/
theorem varyingTupleBox_mem_sieveSupport_of_squarefree {K : ℕ}
    (hK : 0 < K) {u : nearShifts K → ℕ} (hu : u ∈ varyingTupleBox K)
    (hsq : Squarefree (divisorTupleProduct (nearShifts K) u)) :
    u ∈ sieveDivisorSupport K := by
  unfold sieveDivisorSupport
  rw [maynardDivisorTupleSupport_eq_preSievedSimplex_filter,
    Finset.mem_filter]
  refine ⟨?_, hsq⟩
  rw [mem_preSievedSimplexTupleSupport_iff]
  exact ⟨varyingTupleBox_subset_preSievedCommon hK hu,
    (varyingTupleBox_product_le_radiusProduct hu).trans_lt
      (by simpa [globalRadius] using radiusProduct_lt_intervalStart hK)⟩

/-- The true diagonal contains the independent varying-box energy. -/
theorem varyingEnergy_sub_collision_le_sieveDiagonal {K : ℕ}
    (hK : 0 < K) :
    varyingCutoffEnergy K - varyingCutoffCollisionEnergy K ≤
      maynardYDiagonalSum (nearShifts K) (globalRadius K)
        (preSieveModulus K) (sieveY K) := by
  let G : (nearShifts K → ℕ) → ℝ := fun u =>
    tupleCutoff K
        (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 *
      reciprocalTotientTupleWeight (nearShifts K) u
  have hsplit := Finset.sum_filter_add_sum_filter_not (varyingTupleBox K)
    (fun u => ¬Squarefree (divisorTupleProduct (nearShifts K) u)) G
  have hindependent :
      varyingCutoffEnergy K - varyingCutoffCollisionEnergy K =
        ∑ u ∈ (varyingTupleBox K).filter fun u =>
          Squarefree (divisorTupleProduct (nearShifts K) u), G u := by
    unfold varyingCutoffEnergy varyingCutoffCollisionEnergy
    change (∑ u ∈ varyingTupleBox K, G u) -
        (∑ u ∈ (varyingTupleBox K).filter
          (fun u => ¬Squarefree (divisorTupleProduct (nearShifts K) u)),
          G u) = _
    have hnotnot :
        (varyingTupleBox K).filter
            (fun u => ¬¬Squarefree (divisorTupleProduct (nearShifts K) u)) =
          (varyingTupleBox K).filter
            (fun u => Squarefree (divisorTupleProduct (nearShifts K) u)) := by
      ext u
      simp
    rw [hnotnot] at hsplit
    linarith
  rw [hindependent]
  unfold maynardYDiagonalSum
  calc
    (∑ u ∈ (varyingTupleBox K).filter fun u =>
        Squarefree (divisorTupleProduct (nearShifts K) u), G u) =
        ∑ u ∈ (varyingTupleBox K).filter (fun u =>
            Squarefree (divisorTupleProduct (nearShifts K) u)),
          sieveY K u ^ 2 /
            ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) := by
      apply Finset.sum_congr rfl
      intro u hu
      have huData := Finset.mem_filter.mp hu
      have huSupport := varyingTupleBox_mem_sieveSupport_of_squarefree hK
        huData.1 huData.2
      unfold G sieveY maynardYValue reciprocalTotientTupleWeight
      rw [if_pos ⟨(isMaynardDivisorTuple_of_mem_support huSupport).1,
        (isMaynardDivisorTuple_of_mem_support huSupport).2.1,
        (isMaynardDivisorTuple_of_mem_support huSupport).2.2⟩]
      rw [show (∏ h : nearShifts K, (1 : ℝ) / Nat.totient (u h)) =
          1 / ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) by
        simp only [one_div, Finset.prod_inv_distrib]]
      ring
    _ ≤ ∑ u ∈ maynardDivisorTupleSupport (nearShifts K) (globalRadius K)
          (preSieveModulus K),
        sieveY K u ^ 2 /
          ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu
        have huData := Finset.mem_filter.mp hu
        exact varyingTupleBox_mem_sieveSupport_of_squarefree hK
          huData.1 huData.2
      · intro u hu hnot
        have huMaynard := isMaynardDivisorTuple_of_mem_support hu
        have hden : (0 : ℝ) < ∏ h : nearShifts K,
            (Nat.totient (u h) : ℝ) := by
          apply Finset.prod_pos
          intro h hh
          exact_mod_cast Nat.totient_pos.mpr
            (Nat.pos_of_ne_zero (huMaynard.coordinate_squarefree h).ne_zero)
        exact div_nonneg (sq_nonneg _) hden.le

/-- Unweighted reciprocal-totient mass of collisions in the varying box. -/
def varyingCollisionMass (K : ℕ) : ℝ :=
  ∑ u ∈ (varyingTupleBox K).filter fun u =>
      ¬Squarefree (divisorTupleProduct (nearShifts K) u),
    reciprocalTotientTupleWeight (nearShifts K) u

theorem varyingCutoffCollisionEnergy_le_mass (K : ℕ) :
    varyingCutoffCollisionEnergy K ≤ varyingCollisionMass K := by
  unfold varyingCutoffCollisionEnergy varyingCollisionMass
  apply Finset.sum_le_sum
  intro u hu
  have hcut0 := tupleCutoff_nonneg K
    (fun h => Real.log (u h) / Real.log (globalRadius K))
  have hcut1 := abs_tupleCutoff_le_one K
    (fun h => Real.log (u h) / Real.log (globalRadius K))
  rw [abs_of_nonneg hcut0] at hcut1
  have hsq : tupleCutoff K
      (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 ≤ 1 := by
    nlinarith
  have hw : 0 ≤ reciprocalTotientTupleWeight (nearShifts K) u := by
    unfold reciprocalTotientTupleWeight
    positivity
  calc
    tupleCutoff K
          (fun h => Real.log (u h) / Real.log (globalRadius K)) ^ 2 *
        reciprocalTotientTupleWeight (nearShifts K) u ≤
        1 * reciprocalTotientTupleWeight (nearShifts K) u :=
      mul_le_mul_of_nonneg_right hsq hw
    _ = _ := one_mul _

def varyingPrimeCoordinateSupport (K : ℕ) (h : nearShifts K) (p : ℕ) :
    Finset ℕ :=
  (varyingCoordinateSupport K h).filter fun n => p ∣ n

theorem varyingPrimeCoordinateSupport_subset (K : ℕ)
    (h : nearShifts K) (p : ℕ) :
    varyingPrimeCoordinateSupport K h p ⊆
      squarefreeCoprimePrimeDivisorSupport (preSieveModulus K)
        (shiftRadius K h) p := by
  intro n hn
  have hnData := Finset.mem_filter.mp hn
  have hnVary := Finset.mem_filter.mp hnData.1
  rw [squarefreeCoprimePrimeDivisorSupport, Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr ⟨hnVary.2.1,
      (Finset.mem_range.mp hnVary.1).le⟩,
    hnVary.2.2.1, hnVary.2.2.2, hnData.2⟩

theorem varyingPrimeCoordinateEnergy_le {K p : ℕ} (hp : p.Prime)
    (h : nearShifts K) :
    (∑ n ∈ varyingPrimeCoordinateSupport K h p,
        (1 : ℝ) / Nat.totient n) ≤
      (1 : ℝ) / Nat.totient p * varyingCoordinateMajorant K h := by
  calc
    (∑ n ∈ varyingPrimeCoordinateSupport K h p,
        (1 : ℝ) / Nat.totient n) ≤
        ∑ n ∈ squarefreeCoprimePrimeDivisorSupport (preSieveModulus K)
            (shiftRadius K h) p,
          (1 : ℝ) / Nat.totient n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (varyingPrimeCoordinateSupport_subset K h p)
      intro n hn hnot
      positivity
    _ ≤ (1 : ℝ) / Nat.totient p * varyingCoordinateMajorant K h := by
      simpa [varyingCoordinateMajorant] using
        (squarefreeCoprimePrimeDivisorMean_le
          (W := preSieveModulus K) (Q := shiftRadius K h) hp)

def varyingPairPrimeBox (K : ℕ) (a b : nearShifts K) (p : ℕ) :
    Finset (nearShifts K → ℕ) :=
  Fintype.piFinset fun h =>
    if h = a ∨ h = b then varyingPrimeCoordinateSupport K h p
    else varyingCoordinateSupport K h

theorem varying_filter_pair_subset_box (K : ℕ)
    (a b : nearShifts K) (p : ℕ) :
    (varyingTupleBox K).filter (fun u => p ∣ u a ∧ p ∣ u b) ⊆
      varyingPairPrimeBox K a b p := by
  intro u hu
  have huData := Finset.mem_filter.mp hu
  rw [varyingPairPrimeBox, Fintype.mem_piFinset]
  intro h
  have huh := Fintype.mem_piFinset.mp huData.1 h
  by_cases hha : h = a
  · subst h
    simp [varyingPrimeCoordinateSupport, huh, huData.2.1]
  by_cases hhb : h = b
  · subst h
    simp [varyingPrimeCoordinateSupport, huh, huData.2.2]
  · simp [hha, hhb, huh]

theorem varying_pair_prime_mass_le {K p : ℕ} {a b : nearShifts K}
    (hab : a ≠ b) (hp : p.Prime) :
    (∑ u ∈ (varyingTupleBox K).filter
        (fun u => p ∣ u a ∧ p ∣ u b),
      reciprocalTotientTupleWeight (nearShifts K) u) ≤
      ((1 : ℝ) / Nat.totient p) ^ 2 *
        ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
  let c : ℝ := (1 : ℝ) / Nat.totient p
  calc
    (∑ u ∈ (varyingTupleBox K).filter
        (fun u => p ∣ u a ∧ p ∣ u b),
      reciprocalTotientTupleWeight (nearShifts K) u) ≤
        ∑ u ∈ varyingPairPrimeBox K a b p,
          reciprocalTotientTupleWeight (nearShifts K) u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (varying_filter_pair_subset_box K a b p)
      intro u hu hnot
      unfold reciprocalTotientTupleWeight
      positivity
    _ = ∏ h : nearShifts K,
        ∑ n ∈ (if h = a ∨ h = b then
            varyingPrimeCoordinateSupport K h p
          else varyingCoordinateSupport K h),
          (1 : ℝ) / Nat.totient n := by
      unfold varyingPairPrimeBox
      exact reciprocalTotientTupleWeight_sum_pi_eq_prod _
    _ ≤ ∏ h : nearShifts K,
        (if h = a ∨ h = b then c * varyingCoordinateMajorant K h
          else varyingCoordinateMajorant K h) := by
      apply Finset.prod_le_prod
      · intro h hh
        positivity
      · intro h hh
        by_cases hs : h = a ∨ h = b
        · rw [if_pos hs, if_pos hs]
          simpa [c] using varyingPrimeCoordinateEnergy_le hp h
        · rw [if_neg hs, if_neg hs]
          exact preSievedCoordinateInvTotientSum_le
            (preSieveModulus K) (shiftRadius K h)
    _ = c ^ 2 * ∏ h : nearShifts K, varyingCoordinateMajorant K h := by
      have hfactor :
          (∏ h : nearShifts K, if h = a ∨ h = b then c else 1) = c ^ 2 := by
        simpa using (coordinatePrimeCollisionMass_eq
          (H := nearShifts K) hab (M := (1 : ℝ)) (P := c))
      simp_rw [show ∀ h : nearShifts K,
          (if h = a ∨ h = b then c * varyingCoordinateMajorant K h
            else varyingCoordinateMajorant K h) =
          (if h = a ∨ h = b then c else 1) *
            varyingCoordinateMajorant K h by
        intro h
        split_ifs <;> ring]
      rw [Finset.prod_mul_distrib, hfactor]
    _ = _ := rfl

def varyingCollisionPairPrimeUnion (K : ℕ) :
    Finset (nearShifts K → ℕ) :=
  (collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
      (globalRadius K)).biUnion fun x =>
    (varyingTupleBox K).filter fun u => x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2

theorem varyingCollisionBox_subset_pairPrimeUnion {K : ℕ} (hK : 0 < K) :
    (varyingTupleBox K).filter (fun u =>
        ¬Squarefree (divisorTupleProduct (nearShifts K) u)) ⊆
      varyingCollisionPairPrimeUnion K := by
  classical
  intro u hu
  have huData := Finset.mem_filter.mp hu
  have huCommon := varyingTupleBox_subset_preSievedCommon hK huData.1
  have hprodLt : divisorTupleProduct (nearShifts K) u < globalRadius K :=
    (varyingTupleBox_product_le_radiusProduct huData.1).trans_lt
      (by simpa [globalRadius] using radiusProduct_lt_intervalStart hK)
  have huSimplex : u ∈ preSievedSimplexTupleSupport (nearShifts K)
      (globalRadius K) (preSieveModulus K) := by
    rw [mem_preSievedSimplexTupleSupport_iff]
    exact ⟨huCommon, hprodLt⟩
  have huNot : u ∉ sieveDivisorSupport K := by
    intro huMaynard
    exact huData.2 (sieveDivisorSupport_isMaynard K u huMaynard).2.2
  obtain ⟨a, b, p, hab, hp, hpGt, hpa, hpb⟩ :=
    exists_shared_prime_gt_of_independent_not_maynard huSimplex huNot
  have hcoordPos := (varyingTupleBox_coordinate huData.1 a).2.1
  have hpLeCoord : p ≤ u a := Nat.le_of_dvd hcoordPos hpa
  have hcoordLeProd : u a ≤ divisorTupleProduct (nearShifts K) u :=
    Nat.le_of_dvd
      (by
        unfold divisorTupleProduct
        exact Finset.prod_pos fun i hi =>
          (varyingTupleBox_coordinate huData.1 i).2.1)
      (divisorTupleCoordinate_dvd_product u a)
  have hpLeGlobal : p ≤ globalRadius K :=
    (hpLeCoord.trans hcoordLeProd).trans hprodLt.le
  have habMem : (a, b) ∈ offDiagonalPairs (nearShifts K) := by
    rw [offDiagonalPairs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hab⟩
  have hpMem : p ∈ roughPrimeSupport (tinyCutoff K) (globalRadius K) := by
    rw [roughPrimeSupport, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, hpLeGlobal⟩, hp⟩
  rw [varyingCollisionPairPrimeUnion, Finset.mem_biUnion]
  exact ⟨((a, b), p), Finset.mem_product.mpr ⟨habMem, hpMem⟩,
    Finset.mem_filter.mpr ⟨huData.1, hpa, hpb⟩⟩

theorem varyingCollisionMass_le_pairPrimeSum {K : ℕ} (hK : 0 < K) :
    varyingCollisionMass K ≤
      ∑ x ∈ collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
          (globalRadius K),
        ∑ u ∈ (varyingTupleBox K).filter
            (fun u => x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2),
          reciprocalTotientTupleWeight (nearShifts K) u := by
  unfold varyingCollisionMass
  calc
    (∑ u ∈ (varyingTupleBox K).filter (fun u =>
        ¬Squarefree (divisorTupleProduct (nearShifts K) u)),
        reciprocalTotientTupleWeight (nearShifts K) u) ≤
        ∑ u ∈ varyingCollisionPairPrimeUnion K,
          reciprocalTotientTupleWeight (nearShifts K) u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (varyingCollisionBox_subset_pairPrimeUnion hK)
      intro u hu hnot
      unfold reciprocalTotientTupleWeight
      positivity
    _ ≤ _ := sum_biUnion_le_sum _ _ _ fun u => by
      unfold reciprocalTotientTupleWeight
      positivity

theorem varyingCollisionMass_le_majorant {K : ℕ} (hK : 0 < K) :
    varyingCollisionMass K ≤
      ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (∏ h : nearShifts K, varyingCoordinateMajorant K h) *
          (8 / (tinyCutoff K : ℝ)) := by
  let M : ℝ := ∏ h : nearShifts K, varyingCoordinateMajorant K h
  calc
    varyingCollisionMass K ≤
        ∑ x ∈ collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
            (globalRadius K),
          ∑ u ∈ (varyingTupleBox K).filter
              (fun u => x.2 ∣ u x.1.1 ∧ x.2 ∣ u x.1.2),
            reciprocalTotientTupleWeight (nearShifts K) u :=
      varyingCollisionMass_le_pairPrimeSum hK
    _ ≤ ∑ x ∈ collisionPairPrimeIndex (nearShifts K) (tinyCutoff K)
          (globalRadius K), primeTotientSquareWeight x.2 * M := by
      apply Finset.sum_le_sum
      intro x hx
      have hxData := Finset.mem_product.mp hx
      have hab : x.1.1 ≠ x.1.2 := (Finset.mem_filter.mp hxData.1).2
      have hp : x.2.Prime := (Finset.mem_filter.mp hxData.2).2
      have hpair := varying_pair_prime_mass_le (K := K) hab hp
      simpa [primeTotientSquareWeight, M, mul_comm, mul_left_comm,
        mul_assoc] using hpair
    _ = ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (M * ∑ p ∈ roughPrimeSupport (tinyCutoff K) (globalRadius K),
          primeTotientSquareWeight p) := by
      unfold collisionPairPrimeIndex
      rw [Finset.sum_product]
      simp only [Prod.snd]
      rw [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_mul]
      ring
    _ ≤ ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (M * (8 / (tinyCutoff K : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · apply mul_le_mul_of_nonneg_left
          (roughPrimeWeightSum_le (tinyCutoff_pos K))
        unfold M varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
        positivity
      · positivity
    _ = _ := by
      unfold M
      ring

theorem varyingMajorant_le_ninetySix_energy {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) (h : nearShifts K) :
    varyingCoordinateMajorant K h ≤ 96 * coordinateEnergy K h := by
  have hvary := varyingCoordinateMajorant_le_six_inner hA hreg h
  have henergy := sixteenth_innerMajorant_le_coordinateEnergy hreg.1 h
  nlinarith

theorem varyingMajorantProduct_le_energy {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    (∏ h : nearShifts K, varyingCoordinateMajorant K h) ≤
      96 ^ K * productCoordinateEnergy K := by
  calc
    (∏ h : nearShifts K, varyingCoordinateMajorant K h) ≤
        ∏ h : nearShifts K, (96 * coordinateEnergy K h) := by
      apply Finset.prod_le_prod
      · intro h hh
        unfold varyingCoordinateMajorant squarefreeCoprimeInvTotientMean
        positivity
      · intro h hh
        exact varyingMajorant_le_ninetySix_energy hA hreg h
    _ = (∏ _h : nearShifts K, (96 : ℝ)) *
        ∏ h : nearShifts K, coordinateEnergy K h := by
      rw [Finset.prod_mul_distrib]
    _ = 96 ^ K * productCoordinateEnergy K := by
      simp [productCoordinateEnergy, Fintype.card_coe, nearShifts_card]

theorem thirtyTwo_mul_sq_mul_ninetySixPow_le_tinyCutoff
    {K : ℕ} (hK : 0 < K) :
    32 * K ^ 2 * 96 ^ K ≤ tinyCutoff K := by
  exact (calc
    32 * K ^ 2 * 96 ^ K ≤ 3 * 2 ^ 18 * K ^ 2 * 96 ^ K := by
      gcongr <;> norm_num
    _ ≤ tinyCutoff K := cross_numeric_numerator_le_tinyCutoff hK)

theorem collision_energy_factor_le_quarter {K : ℕ} (hK : 0 < K) :
    ((offDiagonalPairs (nearShifts K)).card : ℝ) * 96 ^ K *
        (8 / (tinyCutoff K : ℝ)) ≤ 1 / 4 := by
  have hD : (0 : ℝ) < tinyCutoff K := by
    exact_mod_cast tinyCutoff_pos K
  have hcard : ((offDiagonalPairs (nearShifts K)).card : ℝ) ≤ K ^ 2 := by
    exact_mod_cast offDiagonalPairs_near_card_le K
  have hnat : (((32 * K ^ 2 * 96 ^ K : ℕ) : ℝ)) ≤ tinyCutoff K := by
    exact_mod_cast thirtyTwo_mul_sq_mul_ninetySixPow_le_tinyCutoff hK
  rw [show ((offDiagonalPairs (nearShifts K)).card : ℝ) * 96 ^ K *
      (8 / (tinyCutoff K : ℝ)) =
        (8 * ((offDiagonalPairs (nearShifts K)).card : ℝ) * 96 ^ K) /
          tinyCutoff K by ring]
  apply (div_le_iff₀ hD).2
  calc
    8 * ((offDiagonalPairs (nearShifts K)).card : ℝ) * 96 ^ K ≤
        8 * (K : ℝ) ^ 2 * 96 ^ K := by gcongr
    _ ≤ (1 / 4 : ℝ) * tinyCutoff K := by
      have := hnat
      push_cast at this
      nlinarith

theorem varyingCutoffCollisionEnergy_le_quarter {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    varyingCutoffCollisionEnergy K ≤
      (1 / 4 : ℝ) * productCoordinateEnergy K := by
  have hmass := varyingCutoffCollisionEnergy_le_mass K
  have hcollision := varyingCollisionMass_le_majorant hreg.1
  have hvary := varyingMajorantProduct_le_energy hA hreg
  have hfactor := collision_energy_factor_le_quarter hreg.1
  have henergy : 0 ≤ productCoordinateEnergy K :=
    productCoordinateEnergy_nonneg K
  calc
    varyingCutoffCollisionEnergy K ≤ varyingCollisionMass K := hmass
    _ ≤ ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (∏ h : nearShifts K, varyingCoordinateMajorant K h) *
          (8 / (tinyCutoff K : ℝ)) := hcollision
    _ ≤ ((offDiagonalPairs (nearShifts K)).card : ℝ) *
        (96 ^ K * productCoordinateEnergy K) *
          (8 / (tinyCutoff K : ℝ)) := by
      gcongr
    _ = (((offDiagonalPairs (nearShifts K)).card : ℝ) * 96 ^ K *
        (8 / (tinyCutoff K : ℝ))) * productCoordinateEnergy K := by ring
    _ ≤ (1 / 4 : ℝ) * productCoordinateEnergy K :=
      mul_le_mul_of_nonneg_right hfactor henergy

theorem sixteenthPow_innerMass_le_productEnergy {K : ℕ} (hK : 0 < K) :
    (1 / 16 : ℝ) ^ K * innerTupleMass K ≤ productCoordinateEnergy K := by
  rw [innerTupleMass_eq_majorant_product]
  unfold productCoordinateEnergy
  calc
    (1 / 16 : ℝ) ^ K *
        (∏ h : nearShifts K, innerCoordinateMajorant K h) =
        ∏ h : nearShifts K,
          ((1 / 16 : ℝ) * innerCoordinateMajorant K h) := by
      rw [Finset.prod_mul_distrib]
      simp [Fintype.card_coe, nearShifts_card]
    _ ≤ ∏ h : nearShifts K, coordinateEnergy K h := by
      apply Finset.prod_le_prod
      · intro h hh
        unfold innerCoordinateMajorant squarefreeCoprimeInvTotientMean
        positivity
      · intro h hh
        exact sixteenth_innerMajorant_le_coordinateEnergy hK h

theorem abs_sieveCrossCorrection_le_quarterEnergy {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    |incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K)| ≤
      (1 / 4 : ℝ) * productCoordinateEnergy K := by
  have hcross := abs_sieveCrossCorrection_le_quarterDiagonal hA hreg
  have henergy := sixteenthPow_innerMass_le_productEnergy hreg.1
  calc
    |incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
        (sieveDivisorSupport K) (sieveCoefficient K)| ≤
        (1 / 4 : ℝ) * (((1 / 4 : ℝ) ^ K) ^ 2) *
          innerTupleMass K := hcross
    _ = (1 / 4 : ℝ) *
        ((1 / 16 : ℝ) ^ K * innerTupleMass K) := by
      have hp : (((1 / 4 : ℝ) ^ K) ^ 2) = (1 / 16 : ℝ) ^ K := by
        rw [← pow_mul, show K * 2 = 2 * K by omega, pow_mul]
        norm_num
      rw [hp]
      ring
    _ ≤ (1 / 4 : ℝ) * productCoordinateEnergy K := by
      gcongr

/-- The exact unperturbed CRT bracket controls half of the independent
coordinate energy. -/
theorem half_productEnergy_le_sieveBracket {A : ℝ}
    (hA : ∀ {D P Q : ℕ}, 0 < P → Squarefree (primorial D * P) →
      |squarefreeCoprimeInvTotientMean (primorial D * P) Q -
          coprimeHarmonicDensity (primorial D * P) * Real.log Q| ≤
        10 * coprimeHarmonicDensity (primorial D * P) *
          (A + Real.log D + primeLogDivisorMass P + Real.log 2))
    {K : ℕ} (hreg : NormalizationRegular A K) :
    (1 / 2 : ℝ) * productCoordinateEnergy K ≤
      maynardYDiagonalSum (nearShifts K) (globalRadius K)
          (preSieveModulus K) (sieveY K) -
        incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
          (sieveDivisorSupport K) (sieveCoefficient K) := by
  have hdiag0 := varyingEnergy_sub_collision_le_sieveDiagonal hreg.1
  rw [varyingCutoffEnergy_eq_product] at hdiag0
  have hcollision := varyingCutoffCollisionEnergy_le_quarter hA hreg
  have hcross := abs_sieveCrossCorrection_le_quarterEnergy hA hreg
  have hcrossSelf := le_abs_self
    (incompatibleDivisorPairCommonDivisorTupleSum (nearShifts K)
      (sieveDivisorSupport K) (sieveCoefficient K))
  linarith

/-- Sharp coordinate support, independent of the current enlarged modulus. -/
def IsVaryingSupported (K : ℕ) (y : (nearShifts K → ℕ) → ℝ) : Prop :=
  ∀ ⦃r⦄, y r ≠ 0 → ∀ h : nearShifts K, r h < shiftRadius K h

theorem sieveY_varyingSupported (K : ℕ) : IsVaryingSupported K (sieveY K) :=
  fun _ hr h => sieveY_ne_zero_coordinate_lt hr h

theorem erasePrimeY_varyingSupported {K R W p : ℕ}
    {y : (nearShifts K → ℕ) → ℝ} (hp : 0 < p)
    (hy : IsVaryingSupported K y) :
    IsVaryingSupported K (erasePrimeY R W p y) := by
  intro r hr i
  by_contra hri
  have hyr : y r = 0 := by
    by_contra hyne
    exact hri (hy hyne i)
  have hyins : ∀ h : nearShifts K,
      y (insertTuplePrime p h r) = 0 := by
    intro h
    by_contra hyne
    have hlt := hy hyne i
    by_cases hi : i = h
    · subst i
      simp only [insertTuplePrime_apply_same] at hlt
      have hle : r h ≤ p * r h := by
        exact Nat.le_mul_of_pos_left (r h) hp
      exact hri (hle.trans_lt hlt)
    · exact hri (by simpa [insertTuplePrime, hi] using hlt)
  apply hr
  unfold erasePrimeY
  split_ifs
  · rw [hyr]
    simp [hyins]
  · rfl

theorem differencePrimeY_varyingSupported {K R W p : ℕ}
    {y : (nearShifts K → ℕ) → ℝ} (hp : 0 < p)
    (hy : IsVaryingSupported K y) (m : nearShifts K) :
    IsVaryingSupported K (differencePrimeY R W p m y) := by
  intro r hr i
  by_contra hri
  have hyr : y r = 0 := by
    by_contra hyne
    exact hri (hy hyne i)
  have hyins : ∀ h : nearShifts K,
      y (insertTuplePrime p h r) = 0 := by
    intro h
    by_contra hyne
    have hlt := hy hyne i
    by_cases hi : i = h
    · subst i
      simp only [insertTuplePrime_apply_same] at hlt
      have hle : r h ≤ p * r h := Nat.le_mul_of_pos_left (r h) hp
      exact hri (hle.trans_lt hlt)
    · exact hri (by simpa [insertTuplePrime, hi] using hlt)
  apply hr
  unfold differencePrimeY
  split_ifs
  · rw [hyr]
    simp [hyins]
  · rfl

/-- A sharply supported `Y`-diagonal is bounded by its quadratic energy on
the varying box. -/
theorem maynardYDiagonalSum_le_varyingBox
    {K R W : ℕ} {y : (nearShifts K → ℕ) → ℝ}
    (hmod : preSieveModulus K ∣ W)
    (hySharp : IsVaryingSupported K y) :
    maynardYDiagonalSum (nearShifts K) R W y ≤
      ∑ u ∈ varyingTupleBox K,
        y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u := by
  let D := maynardDivisorTupleSupport (nearShifts K) R W
  let A := D.filter fun u => y u ≠ 0
  let G : (nearShifts K → ℕ) → ℝ := fun u =>
    y u ^ 2 * reciprocalTotientTupleWeight (nearShifts K) u
  have hA : A ⊆ varyingTupleBox K := by
    intro u hu
    have huData := Finset.mem_filter.mp hu
    rw [varyingTupleBox, Fintype.mem_piFinset]
    intro h
    rw [varyingCoordinateSupport, preSievedCommonCoordinateSupport,
      Finset.mem_filter]
    have huMaynard := isMaynardDivisorTuple_of_mem_support huData.1
    have hpos : 0 < u h :=
      Nat.pos_of_ne_zero (huMaynard.coordinate_squarefree h).ne_zero
    exact ⟨Finset.mem_range.mpr (hySharp huData.2 h), hpos,
      huMaynard.coordinate_squarefree h,
      (huMaynard.coordinate_coprime_W h).coprime_dvd_right hmod⟩
  calc
    maynardYDiagonalSum (nearShifts K) R W y = ∑ u ∈ D, G u := by
      unfold maynardYDiagonalSum G reciprocalTotientTupleWeight D
      apply Finset.sum_congr rfl
      intro u hu
      rw [show (∏ h : nearShifts K, (1 : ℝ) / Nat.totient (u h)) =
          1 / ∏ h : nearShifts K, (Nat.totient (u h) : ℝ) by
        simp only [one_div, Finset.prod_inv_distrib]]
      ring
    _ = ∑ u ∈ A, G u := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u huD huNot
      have hyzero : y u = 0 := by
        by_contra hyne
        exact huNot (Finset.mem_filter.mpr ⟨huD, hyne⟩)
      simp [G, hyzero]
    _ ≤ ∑ u ∈ varyingTupleBox K, G u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hA
      intro u hu hnot
      unfold G reciprocalTotientTupleWeight
      positivity
    _ = _ := rfl

theorem selbergCutoff_eq_max_sq {t : ℝ} (ht : 0 ≤ t) :
    selbergCutoff t = (max (1 - t) 0) ^ 2 := by
  unfold selbergCutoff
  rw [min_eq_right]
  have hmax0 : 0 ≤ max (1 - t) 0 := le_max_right _ _
  have hmax1 : max (1 - t) 0 ≤ 1 := by
    exact max_le (by linarith) (by norm_num)
  nlinarith

/-- The quadratic cutoff is `2`-Lipschitz on the nonnegative half-line. -/
theorem abs_selbergCutoff_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |selbergCutoff a - selbergCutoff b| ≤ 2 * |a - b| := by
  let ga : ℝ := max (1 - a) 0
  let gb : ℝ := max (1 - b) 0
  have hga0 : 0 ≤ ga := le_max_right _ _
  have hgb0 : 0 ≤ gb := le_max_right _ _
  have hga1 : ga ≤ 1 := by
    dsimp only [ga]
    exact max_le (by linarith) (by norm_num)
  have hgb1 : gb ≤ 1 := by
    dsimp only [gb]
    exact max_le (by linarith) (by norm_num)
  have hdiff : |ga - gb| ≤ |a - b| := by
    dsimp [ga, gb]
    have h := abs_max_sub_max_le_abs (1 - a) (1 - b) (0 : ℝ)
    simpa [abs_sub_comm] using h
  rw [selbergCutoff_eq_max_sq ha, selbergCutoff_eq_max_sq hb]
  change |ga ^ 2 - gb ^ 2| ≤ _
  rw [show ga ^ 2 - gb ^ 2 = (ga - gb) * (ga + gb) by ring, abs_mul]
  have hsum : |ga + gb| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg hga0 hgb0)]
    linarith
  calc
    |ga - gb| * |ga + gb| ≤ |a - b| * 2 :=
      mul_le_mul hdiff hsum (abs_nonneg _) (abs_nonneg _)
    _ = 2 * |a - b| := by ring

/-- Normalized logarithmic displacement caused by multiplying coordinate
`h` by `p`. -/
def primeLogDisplacement (K : ℕ) (h : nearShifts K) (p : ℕ) : ℝ :=
  ((100 ^ (h : ℕ) : ℕ) : ℝ) *
    (Real.log p / Real.log (globalRadius K))

theorem primeLogDisplacement_nonneg {K p : ℕ} (_hp : 1 ≤ p)
    (h : nearShifts K) :
    0 ≤ primeLogDisplacement K h p := by
  unfold primeLogDisplacement
  exact mul_nonneg (by positivity)
    (div_nonneg (Real.log_natCast_nonneg p) (Real.log_nonneg
      (by exact_mod_cast (one_lt_globalRadius K).le)))

theorem coordinateCutoff_mul_sub_le {K p n : ℕ} (hp : 1 ≤ p)
    (hn : 1 ≤ n) (h : nearShifts K) :
    |coordinateCutoff K h n - coordinateCutoff K h (p * n)| ≤
      2 * primeLogDisplacement K h p := by
  have hglobalLog : 0 < Real.log (globalRadius K) :=
    Real.log_pos (by exact_mod_cast one_lt_globalRadius K)
  let a : ℝ := ((100 ^ (h : ℕ) : ℕ) : ℝ) *
    (Real.log n / Real.log (globalRadius K))
  let δ : ℝ := primeLogDisplacement K h p
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by positivity)
      (div_nonneg (Real.log_natCast_nonneg n) hglobalLog.le)
  have hδ : 0 ≤ δ := primeLogDisplacement_nonneg hp h
  have harg : ((100 ^ (h : ℕ) : ℕ) : ℝ) *
      (Real.log (p * n) / Real.log (globalRadius K)) = a + δ := by
    dsimp [a, δ, primeLogDisplacement]
    rw [Real.log_mul (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hp))
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn))]
    ring
  unfold coordinateCutoff
  rw [Nat.cast_mul, harg]
  have hLip := abs_selbergCutoff_sub_le ha (add_nonneg ha hδ)
  have habs : |a - (a + δ)| = δ := by
    rw [show a - (a + δ) = -δ by ring, abs_neg, abs_of_nonneg hδ]
  change |selbergCutoff a - selbergCutoff (a + δ)| ≤ 2 * δ
  calc
    |selbergCutoff a - selbergCutoff (a + δ)| ≤
        2 * |a - (a + δ)| := hLip
    _ = 2 * δ := by rw [habs]

theorem abs_sieveY_le_coordinateProduct (K : ℕ)
    (r : nearShifts K → ℕ) :
    |sieveY K r| ≤ ∏ h : nearShifts K, coordinateCutoff K h (r h) := by
  unfold sieveY maynardYValue
  split_ifs with hr
  · rw [abs_of_nonneg (tupleCutoff_nonneg K _)]
    exact le_rfl
  · rw [abs_zero]
    apply Finset.prod_nonneg
    intro h hh
    exact coordinateCutoff_nonneg K h (r h)

def insertedCoordinateEnergy (K : ℕ) (h : nearShifts K) (p : ℕ) : ℝ :=
  ∑ n ∈ varyingCoordinateSupport K h,
    coordinateCutoff K h (p * n) ^ 2 / Nat.totient n

def differenceCoordinateEnergy (K : ℕ) (h : nearShifts K) (p : ℕ) : ℝ :=
  ∑ n ∈ varyingCoordinateSupport K h,
    (coordinateCutoff K h n - coordinateCutoff K h (p * n)) ^ 2 /
      Nat.totient n

theorem insertedCoordinateEnergy_nonneg (K : ℕ) (h : nearShifts K)
    (p : ℕ) : 0 ≤ insertedCoordinateEnergy K h p := by
  unfold insertedCoordinateEnergy
  positivity

theorem differenceCoordinateEnergy_nonneg (K : ℕ) (h : nearShifts K)
    (p : ℕ) : 0 ≤ differenceCoordinateEnergy K h p := by
  unfold differenceCoordinateEnergy
  positivity

theorem insertedCoordinateEnergy_le_majorant (K : ℕ)
    (h : nearShifts K) (p : ℕ) :
    insertedCoordinateEnergy K h p ≤ varyingCoordinateMajorant K h := by
  unfold insertedCoordinateEnergy varyingCoordinateMajorant
    squarefreeCoprimeInvTotientMean varyingCoordinateSupport
  calc
    (∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
          (shiftRadius K h),
        coordinateCutoff K h (p * n) ^ 2 / Nat.totient n) ≤
        ∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
          (shiftRadius K h), (1 : ℝ) / Nat.totient n := by
      apply Finset.sum_le_sum
      intro n hn
      have hcut0 := coordinateCutoff_nonneg K h (p * n)
      have hcut1 := coordinateCutoff_le_one K h (p * n)
      have hsq : coordinateCutoff K h (p * n) ^ 2 ≤ 1 := by nlinarith
      exact div_le_div_of_nonneg_right hsq (by positivity)
    _ ≤ ∑ n ∈ Finset.Icc 1 (shiftRadius K h),
        if Squarefree n ∧ Nat.Coprime n (preSieveModulus K) then
          (1 : ℝ) / Nat.totient n else 0 := by
      rw [show (∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
          (shiftRadius K h), (1 : ℝ) / Nat.totient n) =
          ∑ n ∈ preSievedCommonCoordinateSupport (preSieveModulus K)
            (shiftRadius K h),
            if Squarefree n ∧ Nat.Coprime n (preSieveModulus K) then
              (1 : ℝ) / Nat.totient n else 0 by
        apply Finset.sum_congr rfl
        intro n hn
        have hnData := Finset.mem_filter.mp hn
        rw [if_pos ⟨hnData.2.2.1, hnData.2.2.2⟩]]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hnData := Finset.mem_filter.mp hn
        exact Finset.mem_Icc.mpr ⟨hnData.2.1,
          (Finset.mem_range.mp hnData.1).le⟩
      · intro n hn hnot
        split_ifs <;> positivity
    _ = _ := rfl

theorem differenceCoordinateEnergy_le {K p : ℕ} (hp : 1 ≤ p)
    (h : nearShifts K) :
    differenceCoordinateEnergy K h p ≤
      4 * primeLogDisplacement K h p ^ 2 *
        varyingCoordinateMajorant K h := by
  unfold differenceCoordinateEnergy
  calc
    (∑ n ∈ varyingCoordinateSupport K h,
        (coordinateCutoff K h n - coordinateCutoff K h (p * n)) ^ 2 /
          Nat.totient n) ≤
        ∑ n ∈ varyingCoordinateSupport K h,
          (2 * primeLogDisplacement K h p) ^ 2 / Nat.totient n := by
      apply Finset.sum_le_sum
      intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hdiff := coordinateCutoff_mul_sub_le hp hnData.2.1 h
      have hδ := primeLogDisplacement_nonneg hp h
      have hsq :
          (coordinateCutoff K h n - coordinateCutoff K h (p * n)) ^ 2 ≤
            (2 * primeLogDisplacement K h p) ^ 2 := by
        rw [← sq_abs]
        exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hδ)).mpr
          hdiff
      exact div_le_div_of_nonneg_right hsq (by positivity)
    _ = 4 * primeLogDisplacement K h p ^ 2 *
        (∑ n ∈ varyingCoordinateSupport K h,
          (1 : ℝ) / Nat.totient n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ 4 * primeLogDisplacement K h p ^ 2 *
        varyingCoordinateMajorant K h := by
      apply mul_le_mul_of_nonneg_left
      · exact preSievedCoordinateInvTotientSum_le
          (preSieveModulus K) (shiftRadius K h)
      · positivity


end Erdos248
