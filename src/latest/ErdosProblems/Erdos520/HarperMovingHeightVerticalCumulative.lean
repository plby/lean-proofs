import ErdosProblems.Erdos520.HarperMovingHeightCumulative
import ErdosProblems.Erdos520.HarperGoodEventBarrierBridge

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Sharp cumulative drift on the prefix-local vertical mesh

The prefix-local mesh moves coordinate `i` by inverse local scale times
`O((i+1)\u207b\u00b2)`.  The elementary bound below makes the total scale budget
at most `1/32`, independently of both the path length and the height cutoff.
Combining it with the mesh-free cumulative arithmetic theorem gives the
direct checkpoint endpoint consumed by the barrier recursion.
-/

theorem sum_range_inv_nat_succ_sq_le_two (m : ℕ) :
    (∑ i ∈ Finset.range m, ((((i + 1 : ℕ) : ℝ) ^ 2)⁻¹)) ≤ 2 := by
  have hset : Finset.Ioo 0 (m + 1) = Finset.Ico 1 (m + 1) := by
    ext i
    simp only [Finset.mem_Ioo, Finset.mem_Ico]
    omega
  calc
    (∑ i ∈ Finset.range m, ((((i + 1 : ℕ) : ℝ) ^ 2)⁻¹)) =
        ∑ i ∈ Finset.range m, ((((1 + i : ℕ) : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 3
      omega
    _ = ∑ i ∈ Finset.Ico 1 (m + 1), (((i : ℝ) ^ 2)⁻¹) := by
      symm
      simpa using!
        (Finset.sum_Ico_eq_sum_range
          (fun i : ℕ ↦ (((i : ℝ) ^ 2)⁻¹)) 1 (m + 1))
    _ = ∑ i ∈ Finset.Ioo 0 (m + 1), (((i : ℝ) ^ 2)⁻¹) := by
      rw [hset]
    _ ≤ 2 / ((0 : ℝ) + 1) := by
      simpa using! (sum_Ioo_inv_sq_le (α := ℝ) 0 (m + 1))
    _ = 2 := by norm_num

/-- Reindex an initial interval in `Fin n` as the corresponding smaller
finite type. -/
theorem sum_Iic_eq_sum_fin_prefix {n : ℕ} (f : ℕ → ℝ) (k : Fin n) :
    (∑ i ∈ Finset.Iic k, f i.val) =
      ∑ i : Fin (k.val + 1), f i.val := by
  change harperPathPartialSum (fun i : Fin n ↦ f i.val) k = _
  rw [harperPathPartialSum_eq_sum_prefix]
  rfl

/-- Every prefix of the new scheduled checkpoint mesh spends at most
`1/32` of scale-local displacement. -/
theorem sum_Iic_harperScheduledVerticalScaleBudget_le_one_thirtyTwo
    {n : ℕ} (k : Fin n) :
    (∑ i ∈ Finset.Iic k,
        (1 : ℝ) /
          (64 * ((((i.val + 1 : ℕ) : ℝ) ^ 2)))) ≤
      (1 / 32 : ℝ) := by
  have hnonneg : ∀ i : Fin n,
      0 ≤ (1 : ℝ) /
        (64 * ((((i.val + 1 : ℕ) : ℝ) ^ 2))) := by
    intro i
    positivity
  have hsubset :
      (∑ i ∈ Finset.Iic k,
          (1 : ℝ) /
            (64 * ((((i.val + 1 : ℕ) : ℝ) ^ 2)))) ≤
        ∑ i : Fin n,
          (1 : ℝ) /
            (64 * ((((i.val + 1 : ℕ) : ℝ) ^ 2))) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Iic k).subset_univ
      (fun i _hi _hnot ↦ hnonneg i)
  calc
    (∑ i ∈ Finset.Iic k,
        (1 : ℝ) /
          (64 * ((((i.val + 1 : ℕ) : ℝ) ^ 2)))) ≤
        ∑ i : Fin n,
          (1 : ℝ) /
            (64 * ((((i.val + 1 : ℕ) : ℝ) ^ 2))) := hsubset
    _ = ∑ i ∈ Finset.range n,
          (1 : ℝ) / (64 * ((((i + 1 : ℕ) : ℝ) ^ 2))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using!
        (Fin.sum_univ_eq_sum_range
          (fun i : ℕ ↦
            (1 : ℝ) / (64 * ((((i + 1 : ℕ) : ℝ) ^ 2)))) n)
    _ = (1 / 64 : ℝ) *
          (∑ i ∈ Finset.range n,
            ((((i + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi0 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
      field_simp
    _ ≤ (1 / 64 : ℝ) * 2 :=
      mul_le_mul_of_nonneg_left (sum_range_inv_nat_succ_sq_le_two n)
        (by norm_num)
    _ = (1 / 32 : ℝ) := by norm_num

/-- Direct sharp cumulative arithmetic on the actual moving-height vertical
checkpoint path.  The reciprocal-prefix and drift estimates use the same
constants, while the complete checkpoint perturbation is the explicit
absolute surcharge `9/64`. -/
theorem exists_harperScheduledMovingHeightVerticalCumulativeDrift_close :
    ∃ c₀ > 0, ∃ C₀ > 0, ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start →
          harperBlockEndpoint (start + n) ≤ y →
            ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ k : Fin n,
              |(∑ i ∈ Finset.Iic k,
                  harperScheduledReciprocalMass y
                    (start + (i : ℕ))) -
                  ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
                    harperScheduledErrorTail
                      (harperScheduledReciprocalEnvelope c₀ C₀) start ∧
                |harperScheduledVerticalCumulativeDrift
                    y start n t k -
                    ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
                  harperScheduledErrorTail
                      (harperScheduledReciprocalEnvelope c₀ C₀) start +
                    (1 / 2 : ℝ) *
                      harperScheduledErrorTail
                        (harperScheduledOscillationEnvelope M c C) start +
                    2 * harperScheduledErrorTail
                        harperScheduledSquareEnvelope start +
                    (9 / 64 : ℝ) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, hcum⟩ :=
    exists_harperScheduledMovingHeightCumulativeMainMean_close_of_scale_sum
  refine ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, ?_⟩
  intro M start n y hstart hy t htLower htUpper k
  have h := hcum M start n y hstart hy t
    (harperScheduledVerticalCheckpoint start n t)
    (fun i : Fin n ↦
      (1 : ℝ) / (64 * (((i.val + 1 : ℕ) : ℝ) ^ 2)))
    (1 / 32 : ℝ) htLower htUpper
    (fun i ↦ by positivity)
    (harperScheduledVerticalCheckpoint_refinedOffDiagonalCondition
      start n t)
    (sum_Iic_harperScheduledVerticalScaleBudget_le_one_thirtyTwo) k
  rw [show (9 / 2 : ℝ) * (1 / 32 : ℝ) = 9 / 64 by norm_num] at h
  simpa only [harperScheduledVerticalCumulativeDrift] using! h

/-- The corresponding sharp cumulative theorem on every shrinking central
dyadic band.  Its constants and checkpoint surcharge are independent of the
band index `d`. -/
theorem exists_harperScheduledCentralBandVerticalCumulativeDrift_close :
    ∃ c₀ > 0, ∃ C₀ > 0, ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ d start n y : ℕ, J + d ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| →
            |t| ≤ (1 / 2 : ℝ) ^ d → ∀ k : Fin n,
              |(∑ i ∈ Finset.Iic k,
                  harperScheduledReciprocalMass y
                    (start + (i : ℕ))) -
                  ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
                    harperScheduledErrorTail
                      (harperScheduledReciprocalEnvelope c₀ C₀) start ∧
                |harperScheduledVerticalCumulativeDrift
                    y start n t k -
                    ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
                  harperScheduledErrorTail
                      (harperScheduledReciprocalEnvelope c₀ C₀) start +
                    (1 / 2 : ℝ) *
                      harperScheduledErrorTail
                        (harperScheduledDyadicOscillationEnvelope d c C) start +
                    2 * harperScheduledErrorTail
                        harperScheduledSquareEnvelope start +
                    (9 / 64 : ℝ) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, Jcum, hcum⟩ :=
    exists_harperScheduledDyadicCumulativeErrorBounds
  obtain ⟨Jperturb, hperturb⟩ :=
    exists_harperScheduledMovingHeightMainMeanPerturbation
  let J := max Jcum Jperturb
  refine ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, ?_⟩
  intro d start n y hstart hy t htLower htUpper k
  let m : ℕ := k.val + 1
  have hmle : m ≤ n := by
    dsimp [m]
    omega
  have hym : harperBlockEndpoint (start + m) ≤ y :=
    (monotone_harperBlockEndpoint (Nat.add_le_add_left hmle start)).trans hy
  have htUpperOne : |t| ≤ 1 :=
    htUpper.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have herr := hcum d start m y (by omega) hym
    (fun _ : Fin m ↦ t) (fun _ : Fin m ↦ t)
    (fun _ ↦ htLower) (fun _ ↦ htUpperOne) (fun _ ↦ by simp)
  have hreciprocalPrefix :
      |(∑ i ∈ Finset.Iic k,
          harperScheduledReciprocalMass y (start + (i : ℕ))) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
        harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start := by
    rw [sum_Iic_eq_sum_fin_prefix
      (fun q ↦ harperScheduledReciprocalMass y (start + q)) k]
    simpa only [m] using! herr.1
  have hmeanPoint : ∀ i : Fin m,
      harperLogMainBlockMean y
          (harperScheduledPrimeBlock y (start + (i : ℕ))) t t =
        harperScheduledReciprocalMass y (start + (i : ℕ)) +
          (1 / 2 : ℝ) *
            harperScheduledOscillationMass y
              (start + (i : ℕ)) (2 * t) -
          harperScheduledDiagonalCorrection y
            (start + (i : ℕ)) t := by
    intro i
    simpa only [harperScheduledReciprocalMass,
      harperScheduledOscillationMass,
      harperScheduledDiagonalCorrection] using!
        harperScheduledDiagonalMainMean_eq y (start + (i : ℕ)) t
  have hmeanSum :
      (∑ i : Fin m,
          harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) =
        (∑ i : Fin m,
          harperScheduledReciprocalMass y (start + (i : ℕ))) +
          (1 / 2 : ℝ) *
            (∑ i : Fin m,
              harperScheduledOscillationMass y
                (start + (i : ℕ)) (2 * t)) -
          ∑ i : Fin m,
            harperScheduledDiagonalCorrection y
              (start + (i : ℕ)) t := by
    calc
      (∑ i : Fin m,
          harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) =
          ∑ i : Fin m,
            (harperScheduledReciprocalMass y (start + (i : ℕ)) +
              (1 / 2 : ℝ) *
                harperScheduledOscillationMass y
                  (start + (i : ℕ)) (2 * t) -
              harperScheduledDiagonalCorrection y
                (start + (i : ℕ)) t) :=
        Finset.sum_congr rfl (fun i _hi ↦ hmeanPoint i)
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.mul_sum]
  have hoscillationSum :
      |∑ i : Fin m,
          harperScheduledOscillationMass y
            (start + (i : ℕ)) (2 * t)| ≤
        harperScheduledErrorTail
          (harperScheduledDyadicOscillationEnvelope d c C) start := by
    calc
      |∑ i : Fin m,
          harperScheduledOscillationMass y
            (start + (i : ℕ)) (2 * t)| ≤
          ∑ i : Fin m,
            |harperScheduledOscillationMass y
              (start + (i : ℕ)) (2 * t)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ harperScheduledErrorTail
          (harperScheduledDyadicOscillationEnvelope d c C) start := herr.2.1
  have hcorrection0 : 0 ≤
      ∑ i : Fin m,
        harperScheduledDiagonalCorrection y
          (start + (i : ℕ)) t :=
    Finset.sum_nonneg fun i _hi ↦
      harperScheduledDiagonalCorrection_nonneg y (start + (i : ℕ)) t
  have hcorrection :
      (∑ i : Fin m,
          harperScheduledDiagonalCorrection y
            (start + (i : ℕ)) t) ≤
        2 * harperScheduledErrorTail
          harperScheduledSquareEnvelope start := by
    calc
      (∑ i : Fin m,
          harperScheduledDiagonalCorrection y
            (start + (i : ℕ)) t) ≤
          ∑ i : Fin m,
            2 * harperScheduledSquareMass y (start + (i : ℕ)) :=
        Finset.sum_le_sum fun i _hi ↦
          harperScheduledDiagonalCorrection_le_twice_squareMass
            y (start + (i : ℕ)) t
      _ = 2 * (∑ i : Fin m,
          harperScheduledSquareMass y (start + (i : ℕ))) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * harperScheduledErrorTail
          harperScheduledSquareEnvelope start :=
        mul_le_mul_of_nonneg_left herr.2.2 (by norm_num)
  have hdiagonalFin :
      |(∑ i : Fin m,
          harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
          (m : ℝ) * Real.log 2| ≤
        harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) *
            harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start := by
    rw [hmeanSum]
    let R : ℝ := ∑ i : Fin m,
      harperScheduledReciprocalMass y (start + (i : ℕ))
    let O : ℝ := ∑ i : Fin m,
      harperScheduledOscillationMass y (start + (i : ℕ)) (2 * t)
    let Q : ℝ := ∑ i : Fin m,
      harperScheduledDiagonalCorrection y (start + (i : ℕ)) t
    have hR : |R - (m : ℝ) * Real.log 2| ≤
        harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start := by
      simpa only [R] using! herr.1
    have hO : |O| ≤ harperScheduledErrorTail
        (harperScheduledDyadicOscillationEnvelope d c C) start := by
      simpa only [O] using! hoscillationSum
    have hQ0 : 0 ≤ Q := by
      simpa only [Q] using! hcorrection0
    have hQ : Q ≤
        2 * harperScheduledErrorTail harperScheduledSquareEnvelope start := by
      simpa only [Q] using! hcorrection
    change |R + (1 / 2 : ℝ) * O - Q - (m : ℝ) * Real.log 2| ≤ _
    calc
      |R + (1 / 2 : ℝ) * O - Q - (m : ℝ) * Real.log 2| =
          |(R - (m : ℝ) * Real.log 2) +
            (1 / 2 : ℝ) * O - Q| := by
        congr 1
        ring
      _ ≤ |R - (m : ℝ) * Real.log 2| +
          (1 / 2 : ℝ) * |O| + Q := by
        calc
          |(R - (m : ℝ) * Real.log 2) +
              (1 / 2 : ℝ) * O - Q| ≤
              |(R - (m : ℝ) * Real.log 2) +
                (1 / 2 : ℝ) * O| + |Q| := abs_sub _ _
          _ ≤ (|R - (m : ℝ) * Real.log 2| +
                |(1 / 2 : ℝ) * O|) + |Q| :=
            add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
              abs_of_nonneg hQ0]
      _ ≤ harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) *
            harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start := by
        exact add_le_add
          (add_le_add hR
            (mul_le_mul_of_nonneg_left hO (by norm_num))) hQ
  have hdiagonalPrefix :
      |(∑ i ∈ Finset.Iic k,
          harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
        harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) *
            harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start := by
    rw [sum_Iic_eq_sum_fin_prefix
      (fun q ↦ harperLogMainBlockMean y
        (harperScheduledPrimeBlock y (start + q)) t t) k]
    simpa only [m] using! hdiagonalFin
  have hyi : ∀ i : Fin n,
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    intro i
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hperturbPoint : ∀ i : Fin n,
      |harperScheduledMainMeanVectorVarying y start n t
            (harperScheduledVerticalCheckpoint start n t) i -
          harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| ≤
        (9 / 2 : ℝ) *
          ((1 : ℝ) / (64 * (((i.val + 1 : ℕ) : ℝ) ^ 2))) := by
    intro i
    simpa only [harperScheduledMainMeanVectorVarying] using!
      hperturb 0 (start + (i : ℕ)) y (by norm_num; omega) (hyi i)
        t (harperScheduledVerticalCheckpoint start n t i)
        ((1 : ℝ) / (64 * (((i.val + 1 : ℕ) : ℝ) ^ 2)))
        (by positivity)
        (harperScheduledVerticalCheckpoint_refinedOffDiagonalCondition
          start n t i)
  have hperturbPrefix :
      |(∑ i ∈ Finset.Iic k,
          harperScheduledMainMeanVectorVarying y start n t
            (harperScheduledVerticalCheckpoint start n t) i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| ≤
        (9 / 64 : ℝ) := by
    calc
      |(∑ i ∈ Finset.Iic k,
          harperScheduledMainMeanVectorVarying y start n t
            (harperScheduledVerticalCheckpoint start n t) i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| =
        |∑ i ∈ Finset.Iic k,
          (harperScheduledMainMeanVectorVarying y start n t
              (harperScheduledVerticalCheckpoint start n t) i -
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ Finset.Iic k,
          |harperScheduledMainMeanVectorVarying y start n t
              (harperScheduledVerticalCheckpoint start n t) i -
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          (9 / 2 : ℝ) *
            ((1 : ℝ) / (64 * (((i.val + 1 : ℕ) : ℝ) ^ 2))) :=
        Finset.sum_le_sum fun i _hi ↦ hperturbPoint i
      _ = (9 / 2 : ℝ) *
          (∑ i ∈ Finset.Iic k,
            ((1 : ℝ) / (64 * (((i.val + 1 : ℕ) : ℝ) ^ 2)))) := by
        rw [Finset.mul_sum]
      _ ≤ (9 / 2 : ℝ) * (1 / 32 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (sum_Iic_harperScheduledVerticalScaleBudget_le_one_thirtyTwo k)
          (by norm_num)
      _ = (9 / 64 : ℝ) := by norm_num
  refine ⟨hreciprocalPrefix, ?_⟩
  unfold harperScheduledVerticalCumulativeDrift
  calc
    |(∑ i ∈ Finset.Iic k,
        harperScheduledMainMeanVectorVarying y start n t
          (harperScheduledVerticalCheckpoint start n t) i) -
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
      |(∑ i ∈ Finset.Iic k,
          harperScheduledMainMeanVectorVarying y start n t
            (harperScheduledVerticalCheckpoint start n t) i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| +
        |(∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| := by
      have htriangle := abs_add_le
        ((∑ i ∈ Finset.Iic k,
            harperScheduledMainMeanVectorVarying y start n t
              (harperScheduledVerticalCheckpoint start n t) i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)
        ((∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2)
      convert! htriangle using 1 <;> ring_nf
    _ ≤ (9 / 64 : ℝ) +
        (harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) *
            harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start) :=
      add_le_add hperturbPrefix hdiagonalPrefix
    _ = harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) *
            harperScheduledErrorTail
              (harperScheduledDyadicOscillationEnvelope d c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start +
          (9 / 64 : ℝ) := by ring

/-- A single absolute constant controls both the reciprocal normalizer error
and the checkpoint drift error on every central dyadic band and every prefix.
-/
theorem
    exists_harperScheduledCentralBandVerticalCumulativeDrift_constant_bound :
    ∃ K ≥ 0, ∃ J : ℕ,
      ∀ d start n y : ℕ, J + d ≤ start →
        harperBlockEndpoint (start + n) ≤ y →
          ∀ t : ℝ,
            (1 / 2 : ℝ) ^ (d + 1) < |t| →
            |t| ≤ (1 / 2 : ℝ) ^ d → ∀ k : Fin n,
              |(∑ i ∈ Finset.Iic k,
                  harperScheduledReciprocalMass y
                    (start + (i : ℕ))) -
                  ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ K ∧
                |harperScheduledVerticalCumulativeDrift
                    y start n t k -
                    ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤ K := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, hclose⟩ :=
    exists_harperScheduledCentralBandVerticalCumulativeDrift_close
  let K : ℝ :=
    (∑' j : ℕ, harperScheduledReciprocalEnvelope c₀ C₀ j) +
      (1 / 2 : ℝ) *
        (8 + 7 * (∑' j : ℕ, harperScheduledThetaEnvelope c C j)) +
      2 * (∑' j : ℕ, harperScheduledSquareEnvelope j) +
      (9 / 64 : ℝ)
  have hrecTsum : 0 ≤
      ∑' j : ℕ, harperScheduledReciprocalEnvelope c₀ C₀ j :=
    tsum_nonneg (harperScheduledReciprocalEnvelope_nonneg hC₀.le)
  have hthetaTsum : 0 ≤
      ∑' j : ℕ, harperScheduledThetaEnvelope c C j :=
    tsum_nonneg (harperScheduledThetaEnvelope_nonneg hC.le)
  have hsquareTsum : 0 ≤
      ∑' j : ℕ, harperScheduledSquareEnvelope j :=
    tsum_nonneg harperScheduledSquareEnvelope_nonneg
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, J, ?_⟩
  intro d start n y hstart hy t htLower htUpper k
  have h := hclose d start n y hstart hy t htLower htUpper k
  have hrecTail :
      harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start ≤
        ∑' j : ℕ, harperScheduledReciprocalEnvelope c₀ C₀ j :=
    harperScheduledErrorTail_le_tsum
      (harperScheduledReciprocalEnvelope_nonneg hC₀.le)
      (summable_harperScheduledReciprocalEnvelope hc₀ hC₀.le) start
  have hoscTail :
      harperScheduledErrorTail
          (harperScheduledDyadicOscillationEnvelope d c C) start ≤
        8 + 7 * (∑' j : ℕ, harperScheduledThetaEnvelope c C j) :=
    harperScheduledDyadicOscillationTail_le hc hC.le (by omega)
  have hsquareTail :
      harperScheduledErrorTail harperScheduledSquareEnvelope start ≤
        ∑' j : ℕ, harperScheduledSquareEnvelope j :=
    harperScheduledErrorTail_le_tsum
      harperScheduledSquareEnvelope_nonneg
      summable_harperScheduledSquareEnvelope start
  constructor
  · exact h.1.trans (by
      dsimp [K]
      nlinarith)
  · exact h.2.trans (by
      dsimp [K]
      nlinarith)

end Problem520
end Erdos
