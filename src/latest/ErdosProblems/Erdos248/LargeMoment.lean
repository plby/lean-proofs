import ErdosProblems.Erdos248.EventMass
import ErdosProblems.Erdos248.MomentCombinatorics
import ErdosProblems.Erdos248.RangeMomentIdentities
import ErdosProblems.Erdos248.MomentScaleBounds
import ErdosProblems.Erdos248.PrimeSumBounds
import ErdosProblems.Erdos248.BadMassAssembly
import ErdosProblems.Erdos248.TailMarkov

/-!
# Erdős Problem 248: fourth moments for the large-prime ranges

This file turns the uniform correlations for products of at most four large
primes into a centered fourth-moment bound.  The factor `K^4` gained in the
individual correlation error is retained until the collision-pattern sum;
this is what makes the resulting constant independent of the sieve scale.
-/

noncomputable section

open scoped BigOperators
open BoundedGaps.Maynard

namespace Erdos248

local instance largeMomentDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- A single constant dominating both reciprocal-prime estimates. -/
def largePrimeUniformReciprocalConstant : ℝ :=
  1 + largePrimeReciprocalConstant + farPrimeReciprocalConstant

theorem largePrimeUniformReciprocalConstant_pos :
    0 < largePrimeUniformReciprocalConstant := by
  unfold largePrimeUniformReciprocalConstant
  have hl := largePrimeReciprocalConstant_nonneg
  have hf := farPrimeReciprocalConstant_nonneg
  linarith

theorem largePrimeReciprocalConstant_le_uniform :
    largePrimeReciprocalConstant ≤ largePrimeUniformReciprocalConstant := by
  unfold largePrimeUniformReciprocalConstant
  have hf := farPrimeReciprocalConstant_nonneg
  linarith

theorem farPrimeReciprocalConstant_le_uniform :
    farPrimeReciprocalConstant ≤ largePrimeUniformReciprocalConstant := by
  unfold largePrimeUniformReciprocalConstant
  have hl := largePrimeReciprocalConstant_nonneg
  linarith

/-- The relative error before summing the collision patterns. -/
def largePrimeRelativeCorrelationError (K : ℕ) : ℝ :=
  (intervalStart K : ℝ) / preSieveModulus K *
    productCoordinateEnergy K * (50536448 / (K : ℝ) ^ 4)

theorem largePrimeRelativeCorrelationError_nonneg (K : ℕ) :
    0 ≤ largePrimeRelativeCorrelationError K := by
  unfold largePrimeRelativeCorrelationError
  exact mul_nonneg
    (mul_nonneg (by positivity) (productCoordinateEnergy_nonneg K))
    (div_nonneg (by norm_num) (by positivity))

private theorem prod_inv_eq_inv_prod {P : Finset ℕ} :
    (∏ p ∈ P, (1 : ℝ) / p) =
      1 / ((∏ p ∈ P, p : ℕ) : ℝ) := by
  simp only [one_div, Finset.prod_inv_distrib]
  congr 1
  push_cast
  rfl

/-- The explicit event-correlation error is a relative reciprocal-product
error plus the common absolute interval floor. -/
theorem primeProductEventError_le_largeRelative
    {K : ℕ} (hK : 0 < K) {P : Finset ℕ} (hcard : P.card ≤ 4)
    (hPprime : ∀ p ∈ P, p.Prime)
    (hPcut : ∀ p ∈ P, tinyCutoff K < p) :
    (intervalStart K : ℝ) /
          (preSieveModulus K * ∏ p ∈ P, p) *
        ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
            257 * roughCrossTupleTotientSquareTail (nearShifts K)
              (tinyCutoff K) (globalRadius K)) *
          96 ^ K * productCoordinateEnergy K) +
        (radiusProduct K : ℝ) ^ 6 * 257 ≤
      largePrimeRelativeCorrelationError K *
          (∏ p ∈ P, (1 : ℝ) / p) +
        (radiusProduct K : ℝ) ^ 6 * 257 := by
  have hKreal : (0 : ℝ) < (K : ℝ) ^ 4 := by positivity
  have hD := primeProductRelativeError_mul_fourth_le
    hK hcard hPprime hPcut
  have hD' :
      (2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
          257 * roughCrossTupleTotientSquareTail (nearShifts K)
            (tinyCutoff K) (globalRadius K)) * 96 ^ K ≤
        50536448 / (K : ℝ) ^ 4 := by
    rw [le_div_iff₀ hKreal]
    simpa [mul_assoc] using hD
  have hX : 0 ≤ (intervalStart K : ℝ) / preSieveModulus K := by positivity
  have hE := productCoordinateEnergy_nonneg K
  rw [prod_inv_eq_inv_prod]
  have hprodPos : (0 : ℝ) < ((∏ p ∈ P, p : ℕ) : ℝ) := by
    exact_mod_cast primeProduct_pos hPprime
  have hW : (0 : ℝ) < preSieveModulus K := by
    exact_mod_cast preSieveModulus_pos K
  have hmain :
      (intervalStart K : ℝ) /
            (preSieveModulus K * ∏ p ∈ P, p) *
          ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
              257 * roughCrossTupleTotientSquareTail (nearShifts K)
                (tinyCutoff K) (globalRadius K)) *
            96 ^ K * productCoordinateEnergy K) ≤
        largePrimeRelativeCorrelationError K *
          (1 / ((∏ p ∈ P, p : ℕ) : ℝ)) := by
    unfold largePrimeRelativeCorrelationError
    calc
      (intervalStart K : ℝ) /
              (preSieveModulus K * ∏ p ∈ P, p) *
            ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
                257 * roughCrossTupleTotientSquareTail (nearShifts K)
                  (tinyCutoff K) (globalRadius K)) *
              96 ^ K * productCoordinateEnergy K) =
          ((intervalStart K : ℝ) / preSieveModulus K) *
            productCoordinateEnergy K *
            ((2048 * (∑ p ∈ P, (K : ℝ) / Nat.totient p) +
                257 * roughCrossTupleTotientSquareTail (nearShifts K)
                  (tinyCutoff K) (globalRadius K)) * 96 ^ K) *
            (1 / ((∏ p ∈ P, p : ℕ) : ℝ)) := by
              push_cast
              field_simp
              <;> ring
      _ ≤ ((intervalStart K : ℝ) / preSieveModulus K) *
            productCoordinateEnergy K *
            (50536448 / (K : ℝ) ^ 4) *
            (1 / ((∏ p ∈ P, p : ℕ) : ℝ)) := by
          gcongr
      _ = (((intervalStart K : ℝ) / preSieveModulus K) *
            productCoordinateEnergy K *
            (50536448 / (K : ℝ) ^ 4)) *
            (1 / ((∏ p ∈ P, p : ℕ) : ℝ)) := by ring
  gcongr

/-- Centered fourth moment of the divisor count attached to a finite prime
range. -/
def largePrimeCenteredFourthMoment (K k : ℕ) (I : Finset ℕ) : ℝ :=
  weightedFourthMoment
    (Finset.Ico (intervalStart K) (2 * intervalStart K))
    (sieveWeight K)
    (fun n ↦ ∑ p ∈ I, realIndicator (p ∣ n + k) -
      ∑ p ∈ I, (1 : ℝ) / p)

/-- An intentionally generous fixed coefficient for the large-prime fourth
moment. -/
def largePrimeFourthMomentConstant : ℝ :=
  3 * largePrimeUniformReciprocalConstant ^ 2 +
    largePrimeUniformReciprocalConstant +
    64 * 15 * 50536448 *
      (1 + largePrimeUniformReciprocalConstant) ^ 4 + 1

theorem largePrimeFourthMomentConstant_pos :
    0 < largePrimeFourthMomentConstant := by
  unfold largePrimeFourthMomentConstant
  have hB := largePrimeUniformReciprocalConstant_pos.le
  positivity

private theorem largePrimeCenteredFourthMoment_eq_centeredIndicatorSum
    (K k : ℕ) (I : Finset ℕ) :
    largePrimeCenteredFourthMoment K k I =
      weightedFourthMoment
        (Finset.Ico (intervalStart K) (2 * intervalStart K))
        (sieveWeight K)
        (centeredIndicatorSum I (fun _ ↦ 1) (fun p ↦ (1 : ℝ) / p)
          (fun p n ↦ p ∣ n + k)) := by
  unfold largePrimeCenteredFourthMoment centeredIndicatorSum centeredIndicator
  congr 1
  funext n
  simp only [one_mul, Finset.sum_sub_distrib]

/-- Abstract fourth-moment assembly.  The two reciprocal-sum assumptions
separate the uses of the scale `K` (correlation-error cancellation) and the
shift `k` (the Bernoulli main term). -/
theorem largePrimeCenteredFourthMoment_le_of_correlations
    {A : ℝ} (hA : HasUniformWirsingBound A)
    {K k : ℕ} (hreg : NormalizationRegular A K) (hk1 : 1 ≤ k)
    (I : Finset ℕ)
    (hIcard : I.card ≤ shiftRadius K 1)
    (hprime : ∀ p ∈ I, p.Prime)
    (hsumK : (∑ p ∈ I, (1 : ℝ) / p) ≤
      largePrimeUniformReciprocalConstant * (K : ℝ))
    (hsumk : (∑ p ∈ I, (1 : ℝ) / p) ≤
      largePrimeUniformReciprocalConstant * (k : ℝ))
    (hcorr : ∀ J, J ⊆ I → J.card ≤ 4 →
      |primeProductEventMass K k J -
          sieveMass K / (∏ p ∈ J, p : ℕ)| ≤
        largePrimeRelativeCorrelationError K *
            (∏ p ∈ J, (1 : ℝ) / p) +
          (radiusProduct K : ℝ) ^ 6 * 257) :
    largePrimeCenteredFourthMoment K k I ≤
      largePrimeFourthMomentConstant * (k : ℝ) ^ 2 * sieveMass K := by
  let s := Finset.Ico (intervalStart K) (2 * intervalStart K)
  let u : ℕ → ℝ := fun p ↦ (1 : ℝ) / p
  let E₀ : ℝ := (radiusProduct K : ℝ) ^ 6 * 257
  let ε : ℝ := largePrimeRelativeCorrelationError K
  let err : Finset ℕ → ℝ := fun J ↦ ε * (∏ p ∈ J, u p) + E₀
  let S : ℝ := ∑ p ∈ I, u p
  let B : ℝ := largePrimeUniformReciprocalConstant
  have hK : 0 < K := hreg.1
  have hmass : 0 < sieveMass K := sieveMass_pos hA hreg
  have hS0 : 0 ≤ S := by
    dsimp [S, u]
    exact Finset.sum_nonneg fun p hp ↦ by positivity
  have hu0 : ∀ p ∈ I, 0 ≤ u p := by
    intro p hp
    dsimp [u]
    positivity
  have hu1 : ∀ p ∈ I, u p ≤ 1 := by
    intro p hp
    dsimp [u]
    exact (div_le_one (by exact_mod_cast (hprime p hp).pos)).2
      (by exact_mod_cast (hprime p hp).pos)
  have hε0 : 0 ≤ ε := by
    dsimp [ε]
    exact largePrimeRelativeCorrelationError_nonneg K
  have hE₀0 : 0 ≤ E₀ := by dsimp [E₀]; positivity
  have herr0 : ∀ J ⊆ I, J.card ≤ 4 → 0 ≤ err J := by
    intro J hJI hJcard
    dsimp [err]
    exact add_nonneg (mul_nonneg hε0 (Finset.prod_nonneg fun p hp ↦ by
      exact hu0 p (hJI hp))) hE₀0
  have hjoint : ∀ J : Finset ℕ, J ⊆ I → J.card ≤ 4 →
      |weightedMass s (sieveWeight K) (fun n ↦ ∀ p ∈ J, p ∣ n + k) -
        sieveMass K * ∏ p ∈ J, u p| ≤ err J := by
    intro J hJI hJcard
    rw [weightedMass_primeDivisibility_eq_primeProductEventMass]
    have hprod : sieveMass K * (∏ p ∈ J, u p) =
        sieveMass K / ((∏ p ∈ J, p : ℕ) : ℝ) := by
      dsimp [u]
      rw [prod_inv_eq_inv_prod]
      ring
    rw [hprod]
    exact hcorr J hJI hJcard
  have htransfer := abs_weightedFourthMoment_sub_jointModel_le
    s I (sieveWeight K) (fun _ ↦ 1) u (fun p n ↦ p ∣ n + k)
    (sieveMass K) err hjoint
  have hmodel := jointModelCenteredFourth_le I (fun _ ↦ 1) u
    (sieveMass K) hmass.le hu0 hu1
  have hcollision := jointCenteredFourthError_one_le_relative_add_floor
    I u err ε E₀ hε0 hE₀0 hu0 hu1 herr0 (by
      intro J hJI hJcard
      exact le_rfl)
  have hmomentModel :
      weightedFourthMoment s (sieveWeight K)
          (centeredIndicatorSum I (fun _ ↦ 1) u
            (fun p n ↦ p ∣ n + k)) ≤
        jointModelCenteredFourth I (fun _ ↦ 1) u (sieveMass K) +
          jointCenteredFourthError I (fun _ ↦ 1) u err := by
    linarith [le_of_abs_le htransfer]
  have hS_K : S ≤ B * (K : ℝ) := by simpa [S, B, u] using hsumK
  have hS_k : S ≤ B * (k : ℝ) := by simpa [S, B, u] using hsumk
  have hB0 : 0 ≤ B := largePrimeUniformReciprocalConstant_pos.le
  have hmodelBound :
      jointModelCenteredFourth I (fun _ ↦ 1) u (sieveMass K) ≤
        sieveMass K * ((3 * B ^ 2 + B) * (k : ℝ) ^ 2) := by
    calc
      jointModelCenteredFourth I (fun _ ↦ 1) u (sieveMass K) ≤
          sieveMass K * (3 * (∑ p ∈ I, (1 : ℝ) ^ 2 * u p) ^ 2 +
            ∑ p ∈ I, (1 : ℝ) ^ 4 * u p) := hmodel
      _ = sieveMass K * (3 * S ^ 2 + S) := by simp [S]
      _ ≤ sieveMass K * ((3 * B ^ 2 + B) * (k : ℝ) ^ 2) := by
        have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
        have hSk2 : S ^ 2 ≤ (B * (k : ℝ)) ^ 2 := by nlinarith
        apply mul_le_mul_of_nonneg_left _ hmass.le
        have hk0 : (0 : ℝ) ≤ k := by positivity
        nlinarith [mul_nonneg hB0 hk0]
  have hscaledEnergy :
      (intervalStart K : ℝ) / preSieveModulus K *
          productCoordinateEnergy K < 4 * sieveMass K := by
    have hq := quarter_scaled_energy_lt_sieveMass hA hreg
    nlinarith
  have hcollisionScale : (1 + S) ^ 4 ≤
      ((1 + B) * (K : ℝ)) ^ 4 := by
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hone : 1 + S ≤ (1 + B) * (K : ℝ) := by
      have hK0 : (0 : ℝ) ≤ K := by positivity
      nlinarith [mul_nonneg hB0 hK0]
    exact pow_le_pow_left₀ (by linarith) hone 4
  have hrelative :
      16 * ε * (15 * (1 + S) ^ 4) ≤
        sieveMass K *
          (64 * 15 * 50536448 * (1 + B) ^ 4) := by
    have hK4 : (0 : ℝ) < (K : ℝ) ^ 4 := by positivity
    have hcancel :
        (50536448 / (K : ℝ) ^ 4) *
            (((1 + B) * (K : ℝ)) ^ 4) =
          50536448 * (1 + B) ^ 4 := by
      field_simp
    dsimp [ε, largePrimeRelativeCorrelationError]
    calc
      16 * ((intervalStart K : ℝ) / preSieveModulus K *
            productCoordinateEnergy K * (50536448 / (K : ℝ) ^ 4)) *
            (15 * (1 + S) ^ 4) ≤
          16 * ((intervalStart K : ℝ) / preSieveModulus K *
            productCoordinateEnergy K * (50536448 / (K : ℝ) ^ 4)) *
            (15 * (((1 + B) * (K : ℝ)) ^ 4)) := by
              gcongr
      _ = ((intervalStart K : ℝ) / preSieveModulus K *
            productCoordinateEnergy K) *
          (16 * 15 * 50536448 * (1 + B) ^ 4) := by
            calc
              16 * ((intervalStart K : ℝ) / preSieveModulus K *
                    productCoordinateEnergy K *
                      (50536448 / (K : ℝ) ^ 4)) *
                    (15 * ((1 + B) * (K : ℝ)) ^ 4) =
                  ((intervalStart K : ℝ) / preSieveModulus K *
                    productCoordinateEnergy K) * (16 * 15 *
                      ((50536448 / (K : ℝ) ^ 4) *
                        (((1 + B) * (K : ℝ)) ^ 4))) := by ring
              _ = ((intervalStart K : ℝ) / preSieveModulus K *
                    productCoordinateEnergy K) *
                  (16 * 15 * (50536448 * (1 + B) ^ 4)) := by rw [hcancel]
              _ = ((intervalStart K : ℝ) / preSieveModulus K *
                    productCoordinateEnergy K) *
                  (16 * 15 * 50536448 * (1 + B) ^ 4) := by ring
      _ ≤ sieveMass K *
          (64 * 15 * 50536448 * (1 + B) ^ 4) := by
            have hfactor : 0 ≤
                16 * 15 * 50536448 * (1 + B) ^ 4 := by positivity
            have := mul_le_mul_of_nonneg_right hscaledEnergy.le hfactor
            nlinarith
  have hfloor := accumulatedFourthIntervalError_lt_sieveMass
    hA hreg hIcard
  have herrorBound :
      jointCenteredFourthError I (fun _ ↦ 1) u err ≤
        sieveMass K *
          (64 * 15 * 50536448 * (1 + B) ^ 4 + 1) := by
    calc
      jointCenteredFourthError I (fun _ ↦ 1) u err ≤
          16 * ε * (15 * (1 + ∑ p ∈ I, u p) ^ 4) +
            16 * (I.card : ℝ) ^ 4 * E₀ := hcollision
      _ = 16 * ε * (15 * (1 + S) ^ 4) +
            16 * (I.card : ℝ) ^ 4 * E₀ := by rfl
      _ ≤ sieveMass K *
            (64 * 15 * 50536448 * (1 + B) ^ 4) + sieveMass K := by
          exact add_le_add hrelative hfloor.le
      _ = sieveMass K *
          (64 * 15 * 50536448 * (1 + B) ^ 4 + 1) := by ring
  rw [largePrimeCenteredFourthMoment_eq_centeredIndicatorSum]
  change weightedFourthMoment s (sieveWeight K)
      (centeredIndicatorSum I (fun _ ↦ 1) u (fun p n ↦ p ∣ n + k)) ≤ _
  calc
    weightedFourthMoment s (sieveWeight K)
        (centeredIndicatorSum I (fun _ ↦ 1) u
          (fun p n ↦ p ∣ n + k)) ≤
      jointModelCenteredFourth I (fun _ ↦ 1) u (sieveMass K) +
        jointCenteredFourthError I (fun _ ↦ 1) u err := hmomentModel
    _ ≤ sieveMass K * ((3 * B ^ 2 + B) * (k : ℝ) ^ 2) +
        sieveMass K *
          (64 * 15 * 50536448 * (1 + B) ^ 4 + 1) :=
      add_le_add hmodelBound herrorBound
    _ ≤ largePrimeFourthMomentConstant * (k : ℝ) ^ 2 * sieveMass K := by
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      dsimp [B]
      unfold largePrimeFourthMomentConstant
      have hconst : 0 ≤
          64 * 15 * 50536448 *
            (1 + largePrimeUniformReciprocalConstant) ^ 4 + 1 := by positivity
      have hconstGrow :
          64 * 15 * 50536448 *
                (1 + largePrimeUniformReciprocalConstant) ^ 4 + 1 ≤
            (64 * 15 * 50536448 *
                (1 + largePrimeUniformReciprocalConstant) ^ 4 + 1) *
              (k : ℝ) ^ 2 := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
      calc
        sieveMass K *
              ((3 * largePrimeUniformReciprocalConstant ^ 2 +
                  largePrimeUniformReciprocalConstant) * (k : ℝ) ^ 2) +
            sieveMass K *
              (64 * 15 * 50536448 *
                (1 + largePrimeUniformReciprocalConstant) ^ 4 + 1) ≤
            sieveMass K *
              ((3 * largePrimeUniformReciprocalConstant ^ 2 +
                  largePrimeUniformReciprocalConstant) * (k : ℝ) ^ 2) +
            sieveMass K *
              ((64 * 15 * 50536448 *
                  (1 + largePrimeUniformReciprocalConstant) ^ 4 + 1) *
                (k : ℝ) ^ 2) := by gcongr
        _ = (3 * largePrimeUniformReciprocalConstant ^ 2 +
                largePrimeUniformReciprocalConstant +
                64 * 15 * 50536448 *
                  (1 + largePrimeUniformReciprocalConstant) ^ 4 + 1) *
              (k : ℝ) ^ 2 * sieveMass K := by ring

/-! ## Centered Markov extraction -/

/-- If `I` represents the actual large-prime count and its reciprocal mean
is at most `B*k`, then a raw threshold `T*k` is at centered distance at least
`D*k` whenever `B+D ≤ T`. -/
theorem fourth_mul_largePrimeBadMass_le_centeredMoment
    {K T k : ℕ} {I : Finset ℕ} {B D : ℝ}
    (hk1 : 1 ≤ k) (hD : 0 ≤ D)
    (hBT : B + D ≤ (T : ℝ))
    (hmean : (∑ p ∈ I, (1 : ℝ) / p) ≤ B * (k : ℝ))
    (hcount : ∀ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
      (largePrimeCount K k n : ℝ) =
        ∑ p ∈ I, realIndicator (p ∣ n + k)) :
    (D * (k : ℝ)) ^ 4 * largePrimeBadMass K T k ≤
      largePrimeCenteredFourthMoment K k I := by
  let s := Finset.Ico (intervalStart K) (2 * intervalStart K)
  let Z : ℕ → ℝ := fun n ↦
    ∑ p ∈ I, realIndicator (p ∣ n + k) -
      ∑ p ∈ I, (1 : ℝ) / p
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hDk : 0 ≤ D * (k : ℝ) := mul_nonneg hD hk0
  have hmassLe :
      largePrimeBadMass K T k ≤
        weightedMass s (sieveWeight K)
          (fun n ↦ D * (k : ℝ) ≤ |Z n|) := by
    rw [largePrimeBadMass_eq_weightedMass]
    unfold weightedMass weightedSum
    apply Finset.sum_le_sum
    intro n hn
    change sieveWeight K n * realIndicator
        (T * k < largePrimeCount K k n) ≤
      sieveWeight K n * realIndicator (D * (k : ℝ) ≤ |Z n|)
    by_cases hbad : T * k < largePrimeCount K k n
    · have hrawNat : T * k < largePrimeCount K k n := hbad
      have hraw : (T : ℝ) * (k : ℝ) <
          ∑ p ∈ I, realIndicator (p ∣ n + k) := by
        rw [← hcount n hn]
        exact_mod_cast hrawNat
      have hcenter : D * (k : ℝ) ≤ Z n := by
        dsimp [Z]
        nlinarith
      have habs : D * (k : ℝ) ≤ |Z n| :=
        hcenter.trans (le_abs_self (Z n))
      simp [hbad, habs, realIndicator]
    · rw [realIndicator_of_false hbad]
      simp only [mul_zero]
      exact mul_nonneg (sieveWeight_nonneg K n) (realIndicator_nonneg _)
  have hmarkov := fourth_mul_weightedMass_threshold_abs_le_fourthMoment
    hDk (fun n hn ↦ sieveWeight_nonneg K n)
    (s := s) (Z := Z)
  calc
    (D * (k : ℝ)) ^ 4 * largePrimeBadMass K T k ≤
        (D * (k : ℝ)) ^ 4 *
          weightedMass s (sieveWeight K)
            (fun n ↦ D * (k : ℝ) ≤ |Z n|) :=
      mul_le_mul_of_nonneg_left hmassLe (by positivity)
    _ ≤ weightedFourthMoment s (sieveWeight K) Z := hmarkov
    _ = largePrimeCenteredFourthMoment K k I := by rfl

/-- Consumer form of the final fourth-moment tail calculation. -/
theorem largePrimeBadMass_le_sixteenth_of_centeredMoment
    {K T k : ℕ} {I : Finset ℕ} {B D : ℝ}
    (hk1 : 1 ≤ k) (hD : 0 < D)
    (hBT : B + D ≤ (T : ℝ))
    (hmean : (∑ p ∈ I, (1 : ℝ) / p) ≤ B * (k : ℝ))
    (hcount : ∀ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
      (largePrimeCount K k n : ℝ) =
        ∑ p ∈ I, realIndicator (p ∣ n + k))
    (hmass : 0 ≤ sieveMass K)
    (hsize : 16 * largePrimeFourthMomentConstant ≤ D ^ 4)
    (hmoment : largePrimeCenteredFourthMoment K k I ≤
      largePrimeFourthMomentConstant * (k : ℝ) ^ 2 * sieveMass K) :
    largePrimeBadMass K T k ≤
      sieveMass K * (1 / (16 * (k : ℝ) ^ 2)) := by
  have hmarkov := fourth_mul_largePrimeBadMass_le_centeredMoment
    hk1 hD.le hBT hmean hcount
  apply tail_le_sixteenth_inv_sq_of_fourthMoment
    hD largePrimeFourthMomentConstant_pos hmass
      (by exact_mod_cast hk1) (largePrimeBadMass_nonneg K T k) hsize
  exact hmarkov.trans hmoment

end Erdos248
