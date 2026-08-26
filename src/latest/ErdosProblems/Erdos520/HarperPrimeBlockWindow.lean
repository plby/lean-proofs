import ErdosProblems.Erdos520.HarperPrimeBlockArithmetic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Function Filter Finset MeasureTheory Topology
open scoped BigOperators Interval

noncomputable section

namespace Erdos
namespace Problem520

/-!
# Uniform prime-block bounds on noncentral Harper windows

The strong-PNT estimate in `HarperPrimeBlockArithmetic` is explicit but still
depends on the oscillatory frequency.  The local-shell argument only needs a
fixed compact noncentral window: `2 ≤ |tau| ≤ 2 * M`.  This file makes the
estimate uniform on that window and combines it with the reciprocal-prime
mass bounds to obtain numerical diagonal variance and drift estimates.
-/

theorem tendsto_mediumThetaScheduledDelta_zero
    {c C : ℝ} (hc : 0 < c) :
    Tendsto
      (fun j : ℕ => mediumThetaBlockDelta c C
        (harperBlockEndpoint j) (harperBlockEndpoint (j + 1)))
      atTop (𝓝 0) := by
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  have hcast : Tendsto (fun j : ℕ => (harperBlockEndpoint j : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hend
  have h := (tendsto_mediumThetaSquareDelta_zero (C := C) hc).comp hcast
  apply h.congr'
  filter_upwards [] with j
  rw [harperBlockEndpoint_succ,
    mediumThetaBlockDelta_square_eq]
  rfl

theorem tendsto_invLog_harperBlockEndpoint_zero :
    Tendsto (fun j : ℕ => invLog (harperBlockEndpoint j))
      atTop (𝓝 0) := by
  have hend : Tendsto harperBlockEndpoint atTop atTop :=
    strictMono_harperBlockEndpoint.tendsto_atTop
  have hcast : Tendsto (fun j : ℕ => (harperBlockEndpoint j : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp hend
  simpa [invLog] using!
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hcast)

/-- Strong-PNT cancellation, uniformly over every fixed nonzero compact
frequency window used by the noncentral Harper shells. -/
theorem exists_eventually_harperScheduledPrimeOscillation_le
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ tau : ℝ, 2 ≤ |tau| → |tau| ≤ 2 * M →
          |∑ p ∈ harperScheduledPrimeBlock y j,
              Real.cos (tau * Real.log (p.1 : ℝ)) / p.1| ≤ ε := by
  obtain ⟨c, hc, C, hC, J₀, hraw⟩ :=
    exists_mediumPNT_harperScheduledPrimeOscillation_bound
  let delta : ℕ → ℝ := fun j ↦ mediumThetaBlockDelta c C
    (harperBlockEndpoint j) (harperBlockEndpoint (j + 1))
  let ell : ℕ → ℝ := fun j ↦ invLog (harperBlockEndpoint j)
  have hdelta : Tendsto delta atTop (𝓝 0) := by
    exact tendsto_mediumThetaScheduledDelta_zero hc
  have hell : Tendsto ell atTop (𝓝 0) := by
    exact tendsto_invLog_harperBlockEndpoint_zero
  let envelope : ℕ → ℝ := fun j ↦
    ell j + 2 * delta j * ell j + delta j * (1 + 2 * (M : ℝ))
  have htwo : Tendsto (fun j ↦ 2 * delta j * ell j) atTop (𝓝 0) := by
    simpa using! (tendsto_const_nhds.mul hdelta).mul hell
  have hwindow : Tendsto
      (fun j ↦ delta j * (1 + 2 * (M : ℝ))) atTop (𝓝 0) := by
    simpa using! hdelta.mul tendsto_const_nhds
  have henvelope : Tendsto envelope atTop (𝓝 0) := by
    simpa [envelope, add_assoc] using! hell.add (htwo.add hwindow)
  have hevent : ∀ᶠ j : ℕ in atTop, envelope j < ε :=
    (tendsto_order.mp henvelope).2 ε hε
  obtain ⟨J₁, hJ₁⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max J₀ J₁, ?_⟩
  intro j hj y hy tau htauLower htauUpper
  have hj₀ : J₀ ≤ j := (le_max_left J₀ J₁).trans hj
  have hj₁ : J₁ ≤ j := (le_max_right J₀ J₁).trans hj
  have hbase := hraw j hj₀ y hy tau (by
    have : 0 < |tau| := lt_of_lt_of_le (by norm_num) htauLower
    exact (abs_pos.mp this))
  have hdeltaNonneg : 0 ≤ delta j := by
    dsimp [delta]
    unfold mediumThetaBlockDelta
    positivity
  have hendpointOne : 1 < harperBlockEndpoint j :=
    lt_of_lt_of_le (by norm_num) (harperBlockEndpoint_ge_sixteen j)
  have hellNonneg : 0 ≤ ell j := by
    exact (invLog_pos (by exact_mod_cast hendpointOne)).le
  have htauDiv : 2 / |tau| ≤ 1 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) htauLower)).2
    linarith
  have hratio :
      ((harperBlockEndpoint (j + 1) : ℝ) /
          harperBlockEndpoint j) = (harperBlockEndpoint j : ℝ) := by
    rw [harperBlockEndpoint_succ]
    push_cast
    have hA : (harperBlockEndpoint j : ℝ) ≠ 0 := by positivity
    field_simp
  have hlogNonzero : Real.log (harperBlockEndpoint j : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hendpointOne)).ne'
  have hlogCancel :
      Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
          harperBlockEndpoint j) * ell j = 1 := by
    rw [hratio]
    dsimp [ell, invLog]
    exact mul_inv_cancel₀ hlogNonzero
  calc
    |∑ p ∈ harperScheduledPrimeBlock y j,
        Real.cos (tau * Real.log (p.1 : ℝ)) / p.1| ≤
        (2 / |tau| + 2 * delta j +
            delta j * (1 + |tau|) *
              Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
                harperBlockEndpoint j)) * ell j := by
      simpa only [delta, ell] using! hbase
    _ = (2 / |tau|) * ell j + 2 * delta j * ell j +
          delta j * (1 + |tau|) *
            (Real.log ((harperBlockEndpoint (j + 1) : ℝ) /
              harperBlockEndpoint j) * ell j) := by ring
    _ = (2 / |tau|) * ell j + 2 * delta j * ell j +
          delta j * (1 + |tau|) := by rw [hlogCancel, mul_one]
    _ ≤ ell j + 2 * delta j * ell j +
          delta j * (1 + 2 * (M : ℝ)) := by
      have hfirst : (2 / |tau|) * ell j ≤ ell j := by
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right htauDiv hellNonneg
      exact add_le_add
        (add_le_add hfirst le_rfl)
        (mul_le_mul_of_nonneg_left (by linarith) hdeltaNonneg)
    _ = envelope j := by rfl
    _ ≤ ε := (hJ₁ j hj₁).le

/-- The fixed numerical form retained for the coarse moment bounds. -/
theorem exists_eventually_harperScheduledPrimeOscillation_le_eighth
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ tau : ℝ, 2 ≤ |tau| → |tau| ≤ 2 * M →
          |∑ p ∈ harperScheduledPrimeBlock y j,
              Real.cos (tau * Real.log (p.1 : ℝ)) / p.1| ≤ 1 / 8 := by
  exact exists_eventually_harperScheduledPrimeOscillation_le M
    (by norm_num : (0 : ℝ) < 1 / 8)

theorem harperDiagonalPrimeMainMean_eq
    {p : ℕ} (hp : 0 < p) (t : ℝ) :
    harperLinearPrimeMean p t t - harperPrimeSecondHarmonic p t =
      (p : ℝ)⁻¹ +
        Real.cos (2 * (t * Real.log (p : ℝ))) / (2 * p) -
        (1 + Real.cos (2 * (t * Real.log (p : ℝ)))) /
          ((p : ℝ) * (p + 1)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hsqrt : Real.sqrt (p : ℝ) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hpR.le
  unfold harperLinearPrimeMean harperPrimeSecondHarmonic harperTiltBias
  rw [Real.cos_two_mul]
  have hsqrtNe : Real.sqrt (p : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hpR
  field_simp [hsqrtNe]
  rw [hsqrt]
  ring

theorem sum_harperScheduledPrimeBlock_cos_sq_div
    (y j : ℕ) (t : ℝ) :
    (∑ p ∈ harperScheduledPrimeBlock y j,
        Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) =
      (1 / 2 : ℝ) *
        ((∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) +
          ∑ p ∈ harperScheduledPrimeBlock y j,
            Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1) := by
  rw [mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [show (2 * t) * Real.log (p.1 : ℝ) =
      2 * (t * Real.log (p.1 : ℝ)) by ring,
    Real.cos_two_mul]
  ring

theorem three_fourths_mul_cos_sq_sum_le_blockVariance
    (y j : ℕ) (t : ℝ) :
    (3 / 4 : ℝ) *
        (∑ p ∈ harperScheduledPrimeBlock y j,
          Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1) ≤
      harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t t := by
  unfold harperLinearBlockVariance
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  unfold harperLinearPrimeCenteredVariance
  rw [harperPrimeCoefficient_sq (by
    have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
    omega)]
  let coeff : ℝ := Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1
  have hcoeff : 0 ≤ coeff :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hbias := three_fourths_le_one_sub_harperTiltBias_sq
    (sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp) t
  calc
    (3 / 4 : ℝ) * coeff = coeff * (3 / 4 : ℝ) := by ring
    _ ≤ coeff * (1 - harperTiltBias p.1 t ^ 2) :=
      mul_le_mul_of_nonneg_left hbias hcoeff

theorem blockVariance_le_cos_sq_sum
    (y j : ℕ) (t : ℝ) :
    harperLinearBlockVariance y (harperScheduledPrimeBlock y j) t t ≤
      ∑ p ∈ harperScheduledPrimeBlock y j,
        Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1 := by
  unfold harperLinearBlockVariance
  apply Finset.sum_le_sum
  intro p hp
  unfold harperLinearPrimeCenteredVariance
  rw [harperPrimeCoefficient_sq (by
    have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
    omega)]
  exact mul_le_of_le_one_right (by positivity)
    (one_sub_harperTiltBias_sq_le_one p.1 t)

/-- Every sufficiently late scheduled block has uniformly nondegenerate
diagonal variance throughout a fixed noncentral local-shell window. -/
theorem exists_eventually_harperScheduledDiagonalVariance_bounds
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (3 / 64 : ℝ) ≤
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t ∧
            harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t ≤ 13 / 16 := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Josc, hosc⟩ :=
    exists_eventually_harperScheduledPrimeOscillation_le_eighth M
  refine ⟨max Jmass Josc, ?_⟩
  intro j hj y hy t htLower htUpper
  have hjmass : Jmass ≤ j := (le_max_left Jmass Josc).trans hj
  have hjosc : Josc ≤ j := (le_max_right Jmass Josc).trans hj
  have hmassj := hmass j hjmass y hy
  have habsTwo : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htauLower : 2 ≤ |2 * t| := by rw [habsTwo]; linarith
  have htauUpper : |2 * t| ≤ 2 * M := by
    rw [habsTwo]
    exact mul_le_mul_of_nonneg_left htUpper (by norm_num)
  have hoscj := hosc j hjosc y hy (2 * t) htauLower htauUpper
  let cosineMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos (t * Real.log (p.1 : ℝ)) ^ 2 / p.1
  have hcosineIdentity : cosineMass =
      (1 / 2 : ℝ) *
        ((∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) +
          ∑ p ∈ harperScheduledPrimeBlock y j,
            Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1) := by
    exact sum_harperScheduledPrimeBlock_cos_sq_div y j t
  have hcosineLower : (1 / 16 : ℝ) ≤ cosineMass := by
    rw [hcosineIdentity]
    have hoscLower := neg_le_of_abs_le hoscj
    nlinarith [hmassj.1]
  have hcosineUpper : cosineMass ≤ 13 / 16 := by
    rw [hcosineIdentity]
    have hoscUpper := le_of_abs_le hoscj
    nlinarith [hmassj.2]
  constructor
  · calc
      (3 / 64 : ℝ) = (3 / 4 : ℝ) * (1 / 16 : ℝ) := by norm_num
      _ ≤ (3 / 4 : ℝ) * cosineMass := by gcongr
      _ ≤ harperLinearBlockVariance y
          (harperScheduledPrimeBlock y j) t t := by
        exact three_fourths_mul_cos_sq_sum_le_blockVariance y j t
  · exact (blockVariance_le_cos_sq_sum y j t).trans hcosineUpper

theorem sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock
    {y j : ℕ} {p : HarperPrimeIndex y}
    (hp : p ∈ harperScheduledPrimeBlock y j) :
    64 ≤ p.1 := by
  have hexp : 6 ≤ 16 * 2 ^ j := by
    have hpow : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hscale : 64 ≤ harperBlockEndpoint j := by
    unfold harperBlockEndpoint
    have hmono := Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
    norm_num at hmono ⊢
    exact hmono
  have hp' := (mem_harperScheduledPrimeBlock p).mp hp
  omega

theorem harperDiagonalCorrection_nonneg
    {p : ℕ} (hp : 0 < p) (t : ℝ) :
    0 ≤ (1 + Real.cos (2 * (t * Real.log (p : ℝ)))) /
      ((p : ℝ) * (p + 1)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  exact div_nonneg
    (by linarith [Real.neg_one_le_cos (2 * (t * Real.log (p : ℝ)))])
    (mul_nonneg hpR.le (by positivity))

theorem harperDiagonalCorrection_le_inv_thirtyTwo
    {p : ℕ} (hp : 64 ≤ p) (t : ℝ) :
    (1 + Real.cos (2 * (t * Real.log (p : ℝ)))) /
        ((p : ℝ) * (p + 1)) ≤
      (1 / 32 : ℝ) * (p : ℝ)⁻¹ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp64 : (64 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : (0 : ℝ) < (p : ℝ) * (p + 1) := by positivity
  apply (div_le_iff₀ hden).2
  have hright :
      (1 / 32 : ℝ) * (p : ℝ)⁻¹ * ((p : ℝ) * (p + 1)) =
        ((p : ℝ) + 1) / 32 := by
    field_simp
  rw [hright]
  nlinarith [Real.cos_le_one (2 * (t * Real.log (p : ℝ)))]

theorem harperScheduledDiagonalMainMean_eq
    (y j : ℕ) (t : ℝ) :
    harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t t =
      (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) +
        (1 / 2 : ℝ) *
          (∑ p ∈ harperScheduledPrimeBlock y j,
            Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1) -
        ∑ p ∈ harperScheduledPrimeBlock y j,
          (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
            ((p.1 : ℝ) * (p.1 + 1)) := by
  unfold harperLogMainBlockMean
  calc
    (∑ p ∈ harperScheduledPrimeBlock y j,
        (harperLinearPrimeMean p.1 t t -
          harperPrimeSecondHarmonic p.1 t)) =
        ∑ p ∈ harperScheduledPrimeBlock y j,
          ((p.1 : ℝ)⁻¹ +
            Real.cos (2 * (t * Real.log (p.1 : ℝ))) / (2 * p.1) -
            (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
              ((p.1 : ℝ) * (p.1 + 1))) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact harperDiagonalPrimeMainMean_eq (by
        have := sixteen_le_prime_of_mem_harperScheduledPrimeBlock hp
        omega) t
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
      apply congrArg₂ (· - ·) ?_ rfl
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro p hp
      rw [show 2 * (t * Real.log (p.1 : ℝ)) =
          (2 * t) * Real.log (p.1 : ℝ) by ring]
      ring

/-- The quadratic logarithmic increment has positive bounded diagonal drift
on every sufficiently late block in a fixed noncentral shell window. -/
theorem exists_eventually_harperScheduledDiagonalMainMean_bounds
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          (1 / 8 : ℝ) ≤
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t ∧
            harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t ≤ 2 := by
  obtain ⟨Jmass, hmass⟩ :=
    exists_eventually_harperScheduledPrimeBlock_inv_bounds
  obtain ⟨Josc, hosc⟩ :=
    exists_eventually_harperScheduledPrimeOscillation_le_eighth M
  refine ⟨max Jmass Josc, ?_⟩
  intro j hj y hy t htLower htUpper
  have hjmass : Jmass ≤ j := (le_max_left Jmass Josc).trans hj
  have hjosc : Josc ≤ j := (le_max_right Jmass Josc).trans hj
  have hmassj := hmass j hjmass y hy
  have habsTwo : |2 * t| = 2 * |t| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htauLower : 2 ≤ |2 * t| := by rw [habsTwo]; linarith
  have htauUpper : |2 * t| ≤ 2 * M := by
    rw [habsTwo]
    exact mul_le_mul_of_nonneg_left htUpper (by norm_num)
  have hoscj := hosc j hjosc y hy (2 * t) htauLower htauUpper
  let reciprocalMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹
  let oscillatoryMass : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      Real.cos ((2 * t) * Real.log (p.1 : ℝ)) / p.1
  let correction : ℝ :=
    ∑ p ∈ harperScheduledPrimeBlock y j,
      (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
        ((p.1 : ℝ) * (p.1 + 1))
  have hcorrectionNonneg : 0 ≤ correction := by
    dsimp [correction]
    exact Finset.sum_nonneg fun p hp ↦
      harperDiagonalCorrection_nonneg (by
        have := sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hp
        omega) t
  have hcorrectionUpper : correction ≤ (1 / 32 : ℝ) * reciprocalMass := by
    dsimp [correction, reciprocalMass]
    calc
      (∑ p ∈ harperScheduledPrimeBlock y j,
          (1 + Real.cos (2 * (t * Real.log (p.1 : ℝ)))) /
            ((p.1 : ℝ) * (p.1 + 1))) ≤
          ∑ p ∈ harperScheduledPrimeBlock y j,
            (1 / 32 : ℝ) * (p.1 : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        exact harperDiagonalCorrection_le_inv_thirtyTwo
          (sixtyFour_le_prime_of_mem_harperScheduledPrimeBlock hp) t
      _ = (1 / 32 : ℝ) *
          (∑ p ∈ harperScheduledPrimeBlock y j, (p.1 : ℝ)⁻¹) := by
        rw [Finset.mul_sum]
  have hmeanIdentity :
      harperLogMainBlockMean y (harperScheduledPrimeBlock y j) t t =
        reciprocalMass + (1 / 2 : ℝ) * oscillatoryMass - correction := by
    exact harperScheduledDiagonalMainMean_eq y j t
  have hreciprocalLower : (1 / 4 : ℝ) ≤ reciprocalMass := hmassj.1
  have hreciprocalUpper : reciprocalMass ≤ 3 / 2 := hmassj.2
  have hoscLower : (-1 / 8 : ℝ) ≤ oscillatoryMass :=
    by
      dsimp [oscillatoryMass]
      nlinarith [neg_le_of_abs_le hoscj]
  have hoscUpper : oscillatoryMass ≤ 1 / 8 :=
    le_of_abs_le hoscj
  constructor
  · rw [hmeanIdentity]
    nlinarith
  · rw [hmeanIdentity]
    nlinarith

/-- Combined arithmetic input for diagonal blocks in all noncentral local
shells below a fixed truncation. -/
theorem exists_eventually_harperScheduledDiagonalMoment_bounds
    (M : ℕ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ y : ℕ,
      harperBlockEndpoint (j + 1) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ((3 / 64 : ℝ) ≤
              harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t ∧
            harperLinearBlockVariance y
                (harperScheduledPrimeBlock y j) t t ≤ 13 / 16) ∧
          ((1 / 8 : ℝ) ≤
              harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t ∧
            harperLogMainBlockMean y
                (harperScheduledPrimeBlock y j) t t ≤ 2) := by
  obtain ⟨Jvariance, hvariance⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_bounds M
  obtain ⟨Jmean, hmean⟩ :=
    exists_eventually_harperScheduledDiagonalMainMean_bounds M
  refine ⟨max Jvariance Jmean, ?_⟩
  intro j hj y hy t htLower htUpper
  exact ⟨
    hvariance j ((le_max_left Jvariance Jmean).trans hj)
      y hy t htLower htUpper,
    hmean j ((le_max_right Jvariance Jmean).trans hj)
      y hy t htLower htUpper⟩

end Problem520
end Erdos
