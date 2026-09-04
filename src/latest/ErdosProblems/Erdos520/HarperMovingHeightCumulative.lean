import ErdosProblems.Erdos520.HarperMovingHeightMoments
import ErdosProblems.Erdos520.HarperVaryingLogPath

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory ProbabilityTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Cumulative arithmetic on growing noncentral windows

The `clog 2 (M+1)` shift not only makes every individual oscillatory block
small; it makes the complete error tail uniformly bounded in `M`.  This file
packages the resulting prefix estimates, inverse-product estimate, and the
sharp cumulative checkpoint drift needed by the barrier bridge.
-/

/-- The nonnegative diagonal second-harmonic correction is controlled by
twice the inverse-square prime mass.  This low-level form is useful when the
correction is summed over an arbitrarily long moving-height path. -/
theorem harperScheduledDiagonalCorrection_le_twice_squareMass
    (y j : ℕ) (t : ℝ) :
    harperScheduledDiagonalCorrection y j t ≤
      2 * harperScheduledSquareMass y j := by
  unfold harperScheduledDiagonalCorrection harperScheduledSquareMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p.1 := by
    exact_mod_cast (Nat.prime_of_mem_primesBelow p.property).pos
  have hnum :
      1 + Real.cos (2 * (t * Real.log (p.1 : ℝ))) ≤ 2 := by
    linarith [Real.cos_le_one (2 * (t * Real.log (p.1 : ℝ)))]
  have hden0 : (0 : ℝ) < (p.1 : ℝ) * (p.1 : ℝ) := mul_pos hp0 hp0
  have hden : (p.1 : ℝ) * (p.1 : ℝ) ≤
      (p.1 : ℝ) * (p.1 + 1) := by
    nlinarith
  calc
    (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
          ((p.1 : ℝ) * (p.1 + 1)) ≤
        2 / ((p.1 : ℝ) * (p.1 + 1)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ 2 / ((p.1 : ℝ) * (p.1 : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) hden0 hden
    _ = 2 * (p.1 : ℝ)⁻¹ ^ 2 := by field_simp

/-- Each diagonal quadratic drift differs from `log 2` by the three
summable arithmetic envelopes, uniformly on every growing noncentral
window after the explicit logarithmic start shift. -/
theorem exists_harperScheduledMovingHeightDiagonalMainMeanErrorBounds :
    ∃ c₀ > 0, ∃ C₀ > 0, ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ M j y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ j →
          harperBlockEndpoint (j + 1) ≤ y →
            ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
              |harperScheduledReciprocalMass y j - Real.log 2| ≤
                  harperScheduledReciprocalEnvelope c₀ C₀ j ∧
                |harperLogMainBlockMean y
                      (harperScheduledPrimeBlock y j) t t - Real.log 2| ≤
                  harperScheduledReciprocalEnvelope c₀ C₀ j +
                    (1 / 2 : ℝ) *
                      harperScheduledOscillationEnvelope M c C j +
                    2 * harperScheduledSquareEnvelope j := by
  obtain ⟨c₀, hc₀, C₀, hC₀, Jbase, hbase⟩ :=
    exists_harperScheduledSummableBlockErrorBounds 1
  obtain ⟨c, hc, C, hC, Josc, hosc⟩ :=
    exists_harperScheduledMovingHeightOscillationBounds
  let J := max Jbase Josc
  refine ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, ?_⟩
  intro M j y hj hy t htLower htUpper
  have hbase' := hbase j (by omega) y hy
  have hrec := hbase'.1
  have hsquare := hbase'.2.2
  have hosc' :
      |harperScheduledOscillationMass y j (2 * t)| ≤
        harperScheduledOscillationEnvelope M c C j := by
    apply hosc M j y (by omega) hy
    · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left htUpper (by norm_num)
  let reciprocalMass : ℝ := harperScheduledReciprocalMass y j
  let oscillatoryMass : ℝ := harperScheduledOscillationMass y j (2 * t)
  let correction : ℝ := harperScheduledDiagonalCorrection y j t
  have hcorrection0 : 0 ≤ correction := by
    exact harperScheduledDiagonalCorrection_nonneg y j t
  have hcorrection : correction ≤
      2 * harperScheduledSquareEnvelope j := by
    calc
      correction ≤ 2 * harperScheduledSquareMass y j :=
        harperScheduledDiagonalCorrection_le_twice_squareMass y j t
      _ ≤ 2 * harperScheduledSquareEnvelope j :=
        mul_le_mul_of_nonneg_left hsquare (by norm_num)
  have hmeanIdentity :
      harperLogMainBlockMean y
          (harperScheduledPrimeBlock y j) t t =
        reciprocalMass + (1 / 2 : ℝ) * oscillatoryMass - correction := by
    simpa only [reciprocalMass, oscillatoryMass, correction,
      harperScheduledReciprocalMass, harperScheduledOscillationMass,
      harperScheduledDiagonalCorrection] using!
        harperScheduledDiagonalMainMean_eq y j t
  refine ⟨hrec, ?_⟩
  rw [hmeanIdentity]
  calc
    |reciprocalMass + (1 / 2 : ℝ) * oscillatoryMass - correction -
          Real.log 2| =
        |(reciprocalMass - Real.log 2) +
          (1 / 2 : ℝ) * oscillatoryMass - correction| := by
      congr 1
      ring
    _ ≤ |reciprocalMass - Real.log 2| +
          |(1 / 2 : ℝ) * oscillatoryMass| + |correction| := by
      calc
        |(reciprocalMass - Real.log 2) +
            (1 / 2 : ℝ) * oscillatoryMass - correction| ≤
            |(reciprocalMass - Real.log 2) +
              (1 / 2 : ℝ) * oscillatoryMass| + |correction| :=
          abs_sub _ _
        _ ≤ |reciprocalMass - Real.log 2| +
              |(1 / 2 : ℝ) * oscillatoryMass| + |correction| :=
          add_le_add (abs_add_le _ _) le_rfl
    _ = |reciprocalMass - Real.log 2| +
          (1 / 2 : ℝ) * |oscillatoryMass| + correction := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg hcorrection0]
    _ ≤ harperScheduledReciprocalEnvelope c₀ C₀ j +
          (1 / 2 : ℝ) *
            harperScheduledOscillationEnvelope M c C j +
          2 * harperScheduledSquareEnvelope j := by
      dsimp only [reciprocalMass, oscillatoryMass]
      exact add_le_add
        (add_le_add hrec
          (mul_le_mul_of_nonneg_left hosc' (by norm_num))) hcorrection

/-- Reciprocal, oscillatory, and square errors for every finite path are
controlled by tails independent of the path length.  The oscillatory tail
itself is bounded by one absolute constant uniformly in `M`. -/
theorem exists_harperScheduledMovingHeightCumulativeErrorBounds :
    ∃ c₀ > 0, ∃ C₀ > 0, ∃ c > 0, ∃ C > 0, ∃ K ≥ 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start →
          harperBlockEndpoint (start + n) ≤ y →
            ∀ u : Fin n → ℝ,
              (∀ i, 1 ≤ |u i|) → (∀ i, |u i| ≤ M) →
                |(∑ i : Fin n,
                    harperScheduledReciprocalMass y
                      (start + (i : ℕ))) -
                      (n : ℝ) * Real.log 2| ≤
                    harperScheduledErrorTail
                      (harperScheduledReciprocalEnvelope c₀ C₀) start ∧
                (∑ i : Fin n,
                    |harperScheduledOscillationMass y
                      (start + (i : ℕ)) (2 * u i)|) ≤
                    harperScheduledErrorTail
                      (harperScheduledOscillationEnvelope M c C) start ∧
                harperScheduledErrorTail
                    (harperScheduledOscillationEnvelope M c C) start ≤ K ∧
                (∑ i : Fin n,
                    harperScheduledSquareMass y
                      (start + (i : ℕ))) ≤
                    harperScheduledErrorTail
                      harperScheduledSquareEnvelope start := by
  obtain ⟨c₀, hc₀, C₀, hC₀, Jbase, hbase⟩ :=
    exists_harperScheduledCumulativeReciprocalSquareBounds
  obtain ⟨c, hc, C, hC, Josc, hosc⟩ :=
    exists_harperScheduledMovingHeightOscillationBounds
  obtain ⟨Jtheta, htheta⟩ := Filter.eventually_atTop.1
    (eventually_harperScheduledThetaEnvelope_le_invLog_sq hc hC.le)
  let J := max Jbase (max Josc Jtheta)
  let A : ℝ := 1 + 5 * (C + 1)
  let K : ℝ := 2 * A * (1 / 2 : ℝ) ^ J
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, K, hK, J, ?_⟩
  intro M start n y hstart hy u huLower huUpper
  have hstartBase : Jbase ≤ start := by omega
  have hstartOsc : Josc ≤ start := by omega
  have hstartTheta : Jtheta ≤ start := by omega
  have hbase' := hbase start n y hstartBase hy
  have hyi : ∀ i : Fin n,
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    intro i
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hpoint : ∀ i : Fin n,
      |harperScheduledOscillationMass y
          (start + (i : ℕ)) (2 * u i)| ≤
        harperScheduledOscillationEnvelope M c C
          (start + (i : ℕ)) := by
    intro i
    apply hosc M (start + (i : ℕ)) y (by omega) (hyi i)
    · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      linarith [huLower i]
    · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (huUpper i) (by norm_num)
  have hoscPrefix :
      (∑ i : Fin n,
          |harperScheduledOscillationMass y
            (start + (i : ℕ)) (2 * u i)|) ≤
        harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start := by
    calc
      (∑ i : Fin n,
          |harperScheduledOscillationMass y
            (start + (i : ℕ)) (2 * u i)|) ≤
          ∑ i : Fin n,
            harperScheduledOscillationEnvelope M c C
              (start + (i : ℕ)) :=
        Finset.sum_le_sum fun i _hi ↦ hpoint i
      _ ≤ harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start :=
        sum_fin_le_harperScheduledErrorTail
          (harperScheduledOscillationEnvelope_nonneg M hC.le)
          (summable_harperScheduledOscillationEnvelope M hc hC.le)
          start n
  have hterm : ∀ k : ℕ,
      harperScheduledOscillationEnvelope M c C (k + start) ≤
        A * (1 / 2 : ℝ) ^ (J + k) := by
    intro k
    have hshiftK :
        (J + k) + Nat.clog 2 (M + 1) ≤ k + start := by omega
    have hthetaK : harperScheduledThetaEnvelope c C (k + start) ≤
        (C + 1) * invLog (harperBlockEndpoint (k + start)) ^ 2 :=
      htheta (k + start) (by omega)
    have henv := harperScheduledOscillationEnvelope_le_clog_shift
      hC.le hshiftK hthetaK
    have hpow : (1 / 2 : ℝ) ^ (2 * (J + k)) ≤
        (1 / 2 : ℝ) ^ (J + k) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc
      harperScheduledOscillationEnvelope M c C (k + start) ≤
          (1 / 2 : ℝ) ^ (J + k) +
            5 * (C + 1) * (1 / 2 : ℝ) ^ (2 * (J + k)) := henv
      _ ≤ (1 / 2 : ℝ) ^ (J + k) +
            5 * (C + 1) * (1 / 2 : ℝ) ^ (J + k) := by
        gcongr
      _ = A * (1 / 2 : ℝ) ^ (J + k) := by
        dsimp [A]
        ring
  have hleft : Summable (fun k : ℕ ↦
      harperScheduledOscillationEnvelope M c C (k + start)) :=
    (summable_nat_add_iff start).2
      (summable_harperScheduledOscillationEnvelope M hc hC.le)
  have hright : Summable (fun k : ℕ ↦
      A * (1 / 2 : ℝ) ^ (J + k)) := by
    apply (summable_geometric_two.mul_left (A * (1 / 2 : ℝ) ^ J)).congr
    intro k
    rw [pow_add]
    ring
  have hoscTail : harperScheduledErrorTail
      (harperScheduledOscillationEnvelope M c C) start ≤ K := by
    calc
      harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start =
          ∑' k : ℕ,
            harperScheduledOscillationEnvelope M c C (k + start) := rfl
      _ ≤ ∑' k : ℕ, A * (1 / 2 : ℝ) ^ (J + k) :=
        hleft.tsum_le_tsum hterm hright
      _ = ∑' k : ℕ,
          (A * (1 / 2 : ℝ) ^ J) * (1 / 2 : ℝ) ^ k := by
        congr 1
        funext k
        rw [pow_add]
        ring
      _ = (A * (1 / 2 : ℝ) ^ J) * 2 := by
        rw [summable_geometric_two.tsum_mul_left, tsum_geometric_two]
      _ = K := by dsimp [K]; ring
  exact ⟨hbase'.1, hoscPrefix, hoscTail, hbase'.2⟩

/-- A summable family of supplied scale-local checkpoint errors gives a
sharp cumulative drift estimate.  The theorem is deliberately independent
of a particular mesh: a mesh only has to supply nonnegative coordinate
budgets `delta` whose prefix sums are bounded by `D`. -/
theorem
    exists_harperScheduledMovingHeightCumulativeMainMean_close_of_scale_sum :
    ∃ c₀ > 0, ∃ C₀ > 0, ∃ c > 0, ∃ C > 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start →
          harperBlockEndpoint (start + n) ≤ y →
            ∀ t : ℝ, ∀ u : Fin n → ℝ, ∀ delta : Fin n → ℝ,
              ∀ D : ℝ,
                1 ≤ |t| → |t| ≤ M →
                  (∀ i, 0 ≤ delta i) →
                  (∀ i, |u i - t| *
                    Real.log (harperBlockEndpoint
                      (start + (i : ℕ) + 1) : ℝ) ≤ delta i) →
                  (∀ k : Fin n, ∑ i ∈ Finset.Iic k, delta i ≤ D) →
                    ∀ k : Fin n,
                      |(∑ i ∈ Finset.Iic k,
                          harperScheduledReciprocalMass y
                            (start + (i : ℕ))) -
                          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
                            harperScheduledErrorTail
                              (harperScheduledReciprocalEnvelope c₀ C₀)
                              start ∧
                        |(∑ i ∈ Finset.Iic k,
                            harperScheduledMainMeanVectorVarying
                              y start n t u i) -
                            ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
                          harperScheduledErrorTail
                              (harperScheduledReciprocalEnvelope c₀ C₀)
                              start +
                            (1 / 2 : ℝ) *
                              harperScheduledErrorTail
                                (harperScheduledOscillationEnvelope M c C)
                                start +
                            2 * harperScheduledErrorTail
                                harperScheduledSquareEnvelope start +
                            (9 / 2 : ℝ) * D := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, Jdiag, hdiag⟩ :=
    exists_harperScheduledMovingHeightDiagonalMainMeanErrorBounds
  obtain ⟨Jperturb, hperturb⟩ :=
    exists_harperScheduledMovingHeightMainMeanPerturbation
  let J := max Jdiag Jperturb
  refine ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, J, ?_⟩
  intro M start n y hstart hy t u delta D htLower htUpper
    hdelta hscale hdeltaSum k
  have hyi : ∀ i : Fin n,
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    intro i
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hdiagPoint : ∀ i : Fin n,
      |harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t -
          Real.log 2| ≤
        harperScheduledReciprocalEnvelope c₀ C₀
            (start + (i : ℕ)) +
          (1 / 2 : ℝ) *
            harperScheduledOscillationEnvelope M c C
              (start + (i : ℕ)) +
          2 * harperScheduledSquareEnvelope (start + (i : ℕ)) := by
    intro i
    exact (hdiag M (start + (i : ℕ)) y (by omega) (hyi i) t
      htLower htUpper).2
  have hrecPoint : ∀ i : Fin n,
      |harperScheduledReciprocalMass y (start + (i : ℕ)) -
          Real.log 2| ≤
        harperScheduledReciprocalEnvelope c₀ C₀
          (start + (i : ℕ)) := by
    intro i
    exact (hdiag M (start + (i : ℕ)) y (by omega) (hyi i) t
      htLower htUpper).1
  have hperturbPoint : ∀ i : Fin n,
      |harperScheduledMainMeanVectorVarying y start n t u i -
          harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| ≤
        (9 / 2 : ℝ) * delta i := by
    intro i
    simpa only [harperScheduledMainMeanVectorVarying] using!
      hperturb M (start + (i : ℕ)) y (by omega) (hyi i)
        t (u i) (delta i) (hdelta i) (hscale i)
  have hrecPrefix :
      (∑ i ∈ Finset.Iic k,
          harperScheduledReciprocalEnvelope c₀ C₀
            (start + (i : ℕ))) ≤
        harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start := by
    calc
      (∑ i ∈ Finset.Iic k,
          harperScheduledReciprocalEnvelope c₀ C₀
            (start + (i : ℕ))) ≤
          ∑ i : Fin n, harperScheduledReciprocalEnvelope c₀ C₀
            (start + (i : ℕ)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Iic k).subset_univ
          (fun i _hi _hnot ↦
            harperScheduledReciprocalEnvelope_nonneg hC₀.le _)
      _ ≤ harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start :=
        sum_fin_le_harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope_nonneg hC₀.le)
          (summable_harperScheduledReciprocalEnvelope hc₀ hC₀.le)
          start n
  have hreciprocalPrefix :
      |(∑ i ∈ Finset.Iic k,
          harperScheduledReciprocalMass y (start + (i : ℕ))) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
        harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start := by
    have hreindex :
        (∑ i ∈ Finset.Iic k,
            harperScheduledReciprocalMass y (start + (i : ℕ))) -
            ((k.val + 1 : ℕ) : ℝ) * Real.log 2 =
          ∑ i ∈ Finset.Iic k,
            (harperScheduledReciprocalMass y (start + (i : ℕ)) -
              Real.log 2) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Iic]
    rw [hreindex]
    calc
      |∑ i ∈ Finset.Iic k,
          (harperScheduledReciprocalMass y (start + (i : ℕ)) -
            Real.log 2)| ≤
          ∑ i ∈ Finset.Iic k,
            |harperScheduledReciprocalMass y (start + (i : ℕ)) -
              Real.log 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          harperScheduledReciprocalEnvelope c₀ C₀
            (start + (i : ℕ)) :=
        Finset.sum_le_sum fun i _hi ↦ hrecPoint i
      _ ≤ harperScheduledErrorTail
          (harperScheduledReciprocalEnvelope c₀ C₀) start := hrecPrefix
  have hoscPrefix :
      (∑ i ∈ Finset.Iic k,
          harperScheduledOscillationEnvelope M c C
            (start + (i : ℕ))) ≤
        harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start := by
    calc
      (∑ i ∈ Finset.Iic k,
          harperScheduledOscillationEnvelope M c C
            (start + (i : ℕ))) ≤
          ∑ i : Fin n, harperScheduledOscillationEnvelope M c C
            (start + (i : ℕ)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Iic k).subset_univ
          (fun i _hi _hnot ↦
            harperScheduledOscillationEnvelope_nonneg M hC.le _)
      _ ≤ harperScheduledErrorTail
          (harperScheduledOscillationEnvelope M c C) start :=
        sum_fin_le_harperScheduledErrorTail
          (harperScheduledOscillationEnvelope_nonneg M hC.le)
          (summable_harperScheduledOscillationEnvelope M hc hC.le)
          start n
  have hsquarePrefix :
      (∑ i ∈ Finset.Iic k,
          harperScheduledSquareEnvelope (start + (i : ℕ))) ≤
        harperScheduledErrorTail harperScheduledSquareEnvelope start := by
    calc
      (∑ i ∈ Finset.Iic k,
          harperScheduledSquareEnvelope (start + (i : ℕ))) ≤
          ∑ i : Fin n,
            harperScheduledSquareEnvelope (start + (i : ℕ)) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.Iic k).subset_univ
          (fun i _hi _hnot ↦ harperScheduledSquareEnvelope_nonneg _)
      _ ≤ harperScheduledErrorTail harperScheduledSquareEnvelope start :=
        sum_fin_le_harperScheduledErrorTail
          harperScheduledSquareEnvelope_nonneg
          summable_harperScheduledSquareEnvelope start n
  have hdiagPrefix :
      |(∑ i ∈ Finset.Iic k,
          harperLogMainBlockMean y
            (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
        harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) * harperScheduledErrorTail
            (harperScheduledOscillationEnvelope M c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start := by
    have hreindex :
        (∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
            ((k.val + 1 : ℕ) : ℝ) * Real.log 2 =
          ∑ i ∈ Finset.Iic k,
            (harperLogMainBlockMean y
                (harperScheduledPrimeBlock y (start + (i : ℕ))) t t -
              Real.log 2) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Iic]
    rw [hreindex]
    calc
      |∑ i ∈ Finset.Iic k,
          (harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t -
            Real.log 2)| ≤
          ∑ i ∈ Finset.Iic k,
            |harperLogMainBlockMean y
                (harperScheduledPrimeBlock y (start + (i : ℕ))) t t -
              Real.log 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k,
          (harperScheduledReciprocalEnvelope c₀ C₀
              (start + (i : ℕ)) +
            (1 / 2 : ℝ) *
              harperScheduledOscillationEnvelope M c C
                (start + (i : ℕ)) +
            2 * harperScheduledSquareEnvelope
              (start + (i : ℕ))) :=
        Finset.sum_le_sum fun i _hi ↦ hdiagPoint i
      _ = (∑ i ∈ Finset.Iic k,
              harperScheduledReciprocalEnvelope c₀ C₀
                (start + (i : ℕ))) +
            (1 / 2 : ℝ) *
              (∑ i ∈ Finset.Iic k,
                harperScheduledOscillationEnvelope M c C
                  (start + (i : ℕ))) +
            2 * (∑ i ∈ Finset.Iic k,
              harperScheduledSquareEnvelope (start + (i : ℕ))) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ harperScheduledErrorTail
              (harperScheduledReciprocalEnvelope c₀ C₀) start +
            (1 / 2 : ℝ) * harperScheduledErrorTail
              (harperScheduledOscillationEnvelope M c C) start +
            2 * harperScheduledErrorTail
              harperScheduledSquareEnvelope start := by
        exact add_le_add
          (add_le_add hrecPrefix
            (mul_le_mul_of_nonneg_left hoscPrefix (by norm_num)))
          (mul_le_mul_of_nonneg_left hsquarePrefix (by norm_num))
  have hperturbPrefix :
      |(∑ i ∈ Finset.Iic k,
          harperScheduledMainMeanVectorVarying y start n t u i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| ≤
        (9 / 2 : ℝ) * D := by
    calc
      |(∑ i ∈ Finset.Iic k,
          harperScheduledMainMeanVectorVarying y start n t u i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| =
        |∑ i ∈ Finset.Iic k,
          (harperScheduledMainMeanVectorVarying y start n t u i -
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)| := by
        rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ Finset.Iic k,
          |harperScheduledMainMeanVectorVarying y start n t u i -
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Iic k, (9 / 2 : ℝ) * delta i :=
        Finset.sum_le_sum fun i _hi ↦ hperturbPoint i
      _ = (9 / 2 : ℝ) * (∑ i ∈ Finset.Iic k, delta i) := by
        rw [Finset.mul_sum]
      _ ≤ (9 / 2 : ℝ) * D :=
        mul_le_mul_of_nonneg_left (hdeltaSum k) (by norm_num)
  refine ⟨hreciprocalPrefix, ?_⟩
  calc
    |(∑ i ∈ Finset.Iic k,
        harperScheduledMainMeanVectorVarying y start n t u i) -
        ((k.val + 1 : ℕ) : ℝ) * Real.log 2| ≤
      |(∑ i ∈ Finset.Iic k,
          harperScheduledMainMeanVectorVarying y start n t u i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t| +
        |(∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2| := by
      have htriangle := abs_add_le
        ((∑ i ∈ Finset.Iic k,
            harperScheduledMainMeanVectorVarying y start n t u i) -
          ∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t)
        ((∑ i ∈ Finset.Iic k,
            harperLogMainBlockMean y
              (harperScheduledPrimeBlock y (start + (i : ℕ))) t t) -
          ((k.val + 1 : ℕ) : ℝ) * Real.log 2)
      convert! htriangle using 1 <;> ring_nf
    _ ≤ (9 / 2 : ℝ) * D +
        (harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) * harperScheduledErrorTail
            (harperScheduledOscillationEnvelope M c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start) :=
      add_le_add hperturbPrefix hdiagPrefix
    _ = harperScheduledErrorTail
            (harperScheduledReciprocalEnvelope c₀ C₀) start +
          (1 / 2 : ℝ) * harperScheduledErrorTail
            (harperScheduledOscillationEnvelope M c C) start +
          2 * harperScheduledErrorTail
            harperScheduledSquareEnvelope start +
          (9 / 2 : ℝ) * D := by ring

/-- The varying-height inverse Euler product has one absolute prefactor,
uniform in the growing cutoff `M` and the path length. -/
theorem exists_harperScheduledMovingHeightVaryingInverseEulerProduct_constant_bound :
    ∃ K ≥ 0, ∃ J : ℕ,
      ∀ M start n y : ℕ,
        J + Nat.clog 2 (M + 1) ≤ start →
          harperBlockEndpoint (start + n) ≤ y →
            ∀ u : Fin n → ℝ,
              (∀ i, 1 ≤ |u i|) → (∀ i, |u i| ≤ M) →
                (∫ eta,
                    harperScheduledVaryingInverseEulerProduct
                      y start n u eta ∂harperFairCubeLaw y) ≤
                  Real.exp K *
                    ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
                      (1 + (p.1 : ℝ)⁻¹) := by
  obtain ⟨c₀, hc₀, C₀, hC₀, c, hc, C, hC, Kosc, hKosc,
      J, hcum⟩ :=
    exists_harperScheduledMovingHeightCumulativeErrorBounds
  let K : ℝ := 2 * Kosc +
    17 * (∑' j : ℕ, harperScheduledSquareEnvelope j)
  have hSquareTsum : 0 ≤ ∑' j : ℕ, harperScheduledSquareEnvelope j :=
    tsum_nonneg harperScheduledSquareEnvelope_nonneg
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, J, ?_⟩
  intro M start n y hstart hy u huLower huUpper
  have herr := hcum M start n y hstart hy u huLower huUpper
  have hexponent :=
    harperScheduledVaryingInverseExponent_le_log_osc_square
      y start n u
  have hsquareTail : harperScheduledErrorTail
      harperScheduledSquareEnvelope start ≤
        ∑' j : ℕ, harperScheduledSquareEnvelope j :=
    harperScheduledErrorTail_le_tsum
      harperScheduledSquareEnvelope_nonneg
      summable_harperScheduledSquareEnvelope start
  have hexponentBound :
      harperScheduledVaryingInverseExponent y start n u ≤
        (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹)) + K := by
    have hosc := herr.2.1
    have hoscK := herr.2.2.1
    have hsquare := herr.2.2.2
    dsimp [K]
    nlinarith
  have hprodexp :
      Real.exp (∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹)) =
        ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : ℝ)⁻¹) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro p _hp
    rw [Real.exp_log]
    positivity
  calc
    (∫ eta,
        harperScheduledVaryingInverseEulerProduct y start n u eta
          ∂harperFairCubeLaw y) ≤
        Real.exp (harperScheduledVaryingInverseExponent y start n u) :=
      integral_harperScheduledVaryingInverseEulerProduct_le_exp
        y start n u
    _ ≤ Real.exp
        ((∑ p ∈ harperScheduledPrimeRangeFrom y start n,
          Real.log (1 + (p.1 : ℝ)⁻¹)) + K) :=
      Real.exp_le_exp.mpr hexponentBound
    _ = Real.exp K *
        ∏ p ∈ harperScheduledPrimeRangeFrom y start n,
          (1 + (p.1 : ℝ)⁻¹) := by
      rw [Real.exp_add, hprodexp]
      ring

end Problem520
end Erdos
