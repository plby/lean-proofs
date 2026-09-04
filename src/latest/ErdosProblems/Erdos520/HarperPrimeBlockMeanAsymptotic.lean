import ErdosProblems.Erdos520.HarperPrimeBlockAsymptotic
import ErdosProblems.Erdos520.HarperCubicTail

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory Topology
open scoped BigOperators

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Asymptotic diagonal drift of scheduled Harper blocks

The strong-PNT asymptotics for reciprocal and oscillatory prime mass imply
that the quadratic logarithmic drift tends uniformly to `log 2` on every
fixed noncentral frequency window.  The deterministic cubic Taylor budget
then transfers the same limit to the true logarithmic block mean.
-/

/-- The nonnegative second-harmonic correction in the diagonal quadratic
logarithmic mean. -/
noncomputable def harperScheduledDiagonalCorrection
    (y j : ℕ) (t : ℝ) : ℝ :=
  ∑ p ∈ harperScheduledPrimeBlock y j,
    (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
      ((p.1 : ℝ) * (p.1 + 1))

theorem harperScheduledDiagonalCorrection_nonneg
    (y j : ℕ) (t : ℝ) :
    0 ≤ harperScheduledDiagonalCorrection y j t := by
  unfold harperScheduledDiagonalCorrection
  exact Finset.sum_nonneg fun p hp ↦
    harperDiagonalCorrection_nonneg (by
      have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
      omega) t

/-- The diagonal second-harmonic correction is at most `2/A` times the
reciprocal mass of a scheduled block with lower endpoint `A`. -/
theorem harperScheduledDiagonalCorrection_le
    (y j : ℕ) (t : ℝ) :
    harperScheduledDiagonalCorrection y j t ≤
      (2 / (harperBlockEndpoint j : ℝ)) *
        ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ := by
  unfold harperScheduledDiagonalCorrection
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpNat : 0 < p.1 := by
    have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
    omega
  have hpReal : (0 : ℝ) < p.1 := by exact_mod_cast hpNat
  have hANat : 0 < harperBlockEndpoint j := harperBlockEndpoint_pos j
  have hAReal : (0 : ℝ) < harperBlockEndpoint j := by exact_mod_cast hANat
  have hApNat : harperBlockEndpoint j ≤ p.1 :=
    ((mem_harperScheduledPrimeBlock p).mp hp).1.le
  have hApOneReal : (harperBlockEndpoint j : ℝ) ≤ p.1 + 1 := by
    exact_mod_cast (hApNat.trans (Nat.le_add_right p.1 1))
  have hnum :
      1 + Real.cos (2 * (t * Real.log (p.1 : ℝ))) ≤ 2 := by
    linarith [Real.cos_le_one (2 * (t * Real.log (p.1 : ℝ)))]
  have hdenPos : (0 : ℝ) < (p.1 : ℝ) * (p.1 + 1) := by positivity
  have hsmallDenPos :
      (0 : ℝ) < (p.1 : ℝ) * harperBlockEndpoint j := by positivity
  have hdenOrder :
      (p.1 : ℝ) * harperBlockEndpoint j ≤
        (p.1 : ℝ) * (p.1 + 1) :=
    mul_le_mul_of_nonneg_left hApOneReal hpReal.le
  calc
    (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
        ((p.1 : ℝ) * (p.1 + 1)) ≤
      2 / ((p.1 : ℝ) * (p.1 + 1)) :=
        div_le_div_of_nonneg_right hnum hdenPos.le
    _ ≤ 2 / ((p.1 : ℝ) * harperBlockEndpoint j) :=
      div_le_div_of_nonneg_left (by norm_num) hsmallDenPos hdenOrder
    _ = (2 / (harperBlockEndpoint j : ℝ)) * (p.1 : ℝ)⁻¹ := by
      field_simp

theorem exists_eventually_harperScheduledDiagonalCorrection_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y → ∀ t : ℝ,
        harperScheduledDiagonalCorrection y j t < ε := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  have hcast : Tendsto (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hend
  have hinv : Tendsto
      (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ)⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hcast
  have hthreeConst : Tendsto (fun _ : ℕ ↦ (3 : ℝ)) atTop (𝓝 3) :=
    tendsto_const_nhds
  have hthree : Tendsto
      (fun j : ℕ ↦ 3 * (harperBlockEndpoint j : ℝ)⁻¹)
      atTop (𝓝 0) := by
    convert! hthreeConst.mul hinv using 1 <;> norm_num
  have hevent : ∀ᶠ j : ℕ in atTop,
      3 * (harperBlockEndpoint j : ℝ)⁻¹ < ε :=
    (tendsto_order.mp hthree).2 ε hε
  obtain ⟨Jsmall, hsmall⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max Jmass Jsmall, ?_⟩
  intro j hj y hy t
  have hjmass : Jmass ≤ j := (le_max_left Jmass Jsmall).trans hj
  have hjsmall : Jsmall ≤ j := (le_max_right Jmass Jsmall).trans hj
  calc
    harperScheduledDiagonalCorrection y j t ≤
        (2 / (harperBlockEndpoint j : ℝ)) *
          ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹ :=
      harperScheduledDiagonalCorrection_le y j t
    _ ≤ (2 / (harperBlockEndpoint j : ℝ)) * (3 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (hmass j hjmass y hy).2 (by positivity)
    _ = 3 * (harperBlockEndpoint j : ℝ)⁻¹ := by ring
    _ < ε := hsmall j hjsmall

/-- The quadratic logarithmic drift of a scheduled diagonal block converges
uniformly to `log 2` on every fixed noncentral frequency window. -/
theorem exists_eventually_harperScheduledDiagonalMainMean_close
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          |harperLogMainBlockMean y
              (harperScheduledPrimeBlock y j) t t - Real.log 2| < ε := by
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_close_log_two hthird
  obtain ⟨Josc, hosc⟩ :=
    exists_eventually_harperScheduledPrimeOscillation_le M hthird
  obtain ⟨Jcorrection, hcorrection⟩ :=
    exists_eventually_harperScheduledDiagonalCorrection_lt hthird
  refine ⟨max Jmass (max Josc Jcorrection), ?_⟩
  intro j hj y hy t htLower htUpper
  have hjmass : Jmass ≤ j :=
    (le_max_left Jmass (max Josc Jcorrection)).trans hj
  have hjosc : Josc ≤ j :=
    (le_max_left Josc Jcorrection).trans
      ((le_max_right Jmass (max Josc Jcorrection)).trans hj)
  have hjcorrection : Jcorrection ≤ j :=
    (le_max_right Josc Jcorrection).trans
      ((le_max_right Jmass (max Josc Jcorrection)).trans hj)
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
  let correction : ℝ := harperScheduledDiagonalCorrection y j t
  have hmassj : |reciprocalMass - Real.log 2| < ε / 3 := by
    exact hmass j hjmass y hy
  have habsTwo : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htauLower : 2 ≤ |2 * t| := by rw [habsTwo]; linarith
  have htauUpper : |2 * t| ≤ 2 * M := by
    rw [habsTwo]
    exact mul_le_mul_of_nonneg_left htUpper (by norm_num)
  have hoscj : |oscillatoryMass| ≤ ε / 3 := by
    exact hosc j hjosc y hy (2 * t) htauLower htauUpper
  have hcorrectionj : correction < ε / 3 := by
    exact hcorrection j hjcorrection y hy t
  have hcorrectionNonneg : 0 ≤ correction := by
    exact harperScheduledDiagonalCorrection_nonneg y j t
  have hmeanIdentity :
      harperLogMainBlockMean y
          (harperScheduledPrimeBlock y j) t t =
        reciprocalMass + (1 / 2 : ℝ) * oscillatoryMass - correction := by
    simpa only [reciprocalMass, oscillatoryMass, correction,
      harperScheduledDiagonalCorrection] using!
        harperScheduledDiagonalMainMean_eq y j t
  rw [hmeanIdentity, abs_lt]
  have hmassLower := neg_lt_of_abs_lt hmassj
  have hmassUpper := lt_of_abs_lt hmassj
  have hoscLower := neg_le_of_abs_le hoscj
  have hoscUpper := le_of_abs_le hoscj
  constructor <;> nlinarith

/-- A convenient numerical drift interval for the quadratic logarithmic
block. -/
theorem exists_eventually_harperScheduledDiagonalMainMean_half_one
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (1 / 2 : ℝ) <
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t ∧
            harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t < 1 := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalMainMean_close M
      (by norm_num : (0 : ℝ) < 1 / 10)
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper
  have hclose := hJ j hj y hy t htLower htUpper
  have hlower := neg_lt_of_abs_lt hclose
  have hupper := lt_of_abs_lt hclose
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The exact tilted expectation of the true logarithmic increment over one
scheduled block. -/
noncomputable def harperScheduledTrueLogBlockMean
    (y j : ℕ) (t : ℝ) : ℝ :=
  ∫ eta, harperLogBlockSum y (harperScheduledPrimeBlock y j) t eta
    ∂harperTiltedCubeLaw y t

/-- The deterministic cubic Taylor budget of a scheduled block vanishes
uniformly in its ambient cutoff. -/
theorem exists_eventually_harperScheduledCubicRemainder_lt
    {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockCubicRemainder y (harperScheduledPrimeBlock y j) < ε := by
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  have hcast : Tendsto (fun j : ℕ ↦ (harperBlockEndpoint j : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hend
  have hsqrt : Tendsto
      (fun j : ℕ ↦ Real.sqrt (harperBlockEndpoint j : ℝ))
      atTop atTop := Real.tendsto_sqrt_atTop.comp hcast
  have hinv : Tendsto
      (fun j : ℕ ↦ (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hsqrt
  have hconst : Tendsto (fun _ : ℕ ↦ (4 / 3 : ℝ))
      atTop (𝓝 (4 / 3 : ℝ)) := tendsto_const_nhds
  have hscale : Tendsto
      (fun j : ℕ ↦
        (4 / 3 : ℝ) *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹)
      atTop (𝓝 0) := by
    convert! hconst.mul hinv using 1 <;> norm_num
  have hevent : ∀ᶠ j : ℕ in atTop,
      (4 / 3 : ℝ) *
          (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ < ε :=
    (tendsto_order.mp hscale).2 ε hε
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨J, ?_⟩
  intro j hj y
  exact (harperBlockCubicRemainder_scheduled_le y j).trans_lt (hJ j hj)

/-- The exact true logarithmic block mean has the same uniform limit
`log 2` as its quadratic approximation. -/
theorem exists_eventually_harperScheduledTrueLogBlockMean_close
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          |harperScheduledTrueLogBlockMean y j t - Real.log 2| < ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Jmain, hmain⟩ :=
    exists_eventually_harperScheduledDiagonalMainMean_close M hhalf
  obtain ⟨Jcubic, hcubic⟩ :=
    exists_eventually_harperScheduledCubicRemainder_lt hhalf
  refine ⟨max Jmain Jcubic, ?_⟩
  intro j hj y hy t htLower htUpper
  have hjmain : Jmain ≤ j := (le_max_left Jmain Jcubic).trans hj
  have hjcubic : Jcubic ≤ j := (le_max_right Jmain Jcubic).trans hj
  let mainMean : ℝ :=
    harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t t
  have hmainj : |mainMean - Real.log 2| < ε / 2 :=
    hmain j hjmain y hy t htLower htUpper
  have hTaylor :
      |harperScheduledTrueLogBlockMean y j t - mainMean| ≤
        harperBlockCubicRemainder y (harperScheduledPrimeBlock y j) := by
    unfold harperScheduledTrueLogBlockMean
    exact abs_integral_harperLogBlockSum_sub_mainMean_le
      y (harperScheduledPrimeBlock y j)
      (fun p hp ↦ four_le_prime_of_mem_harperScheduledPrimeBlock hp) t t
  have hTaylorSmall :
      |harperScheduledTrueLogBlockMean y j t - mainMean| < ε / 2 :=
    hTaylor.trans_lt (hcubic j hjcubic y)
  calc
    |harperScheduledTrueLogBlockMean y j t - Real.log 2| =
        |(harperScheduledTrueLogBlockMean y j t - mainMean) +
          (mainMean - Real.log 2)| := by ring_nf
    _ ≤ |harperScheduledTrueLogBlockMean y j t - mainMean| +
        |mainMean - Real.log 2| := abs_add_le _ _
    _ < ε := by linarith

/-- The same convenient numerical drift interval for the exact logarithmic
block mean. -/
theorem exists_eventually_harperScheduledTrueLogBlockMean_half_one
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (1 / 2 : ℝ) < harperScheduledTrueLogBlockMean y j t ∧
            harperScheduledTrueLogBlockMean y j t < 1 := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledTrueLogBlockMean_close M
      (by norm_num : (0 : ℝ) < 1 / 10)
  refine ⟨J, ?_⟩
  intro j hj y hy t htLower htUpper
  have hclose := hJ j hj y hy t htLower htUpper
  have hlower := neg_lt_of_abs_lt hclose
  have hupper := lt_of_abs_lt hclose
  constructor <;> nlinarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

end Problem520
end Erdos
