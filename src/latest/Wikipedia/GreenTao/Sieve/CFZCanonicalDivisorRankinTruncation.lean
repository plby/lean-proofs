import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorTruncation
import Wikipedia.GreenTao.Sieve.CFZCarryFourierTailPolylog

/-!
# Rankin bounds for canonical coordinatewise divisor truncation

The pointwise cardinality majorant for the canonical divisor-cutoff
discrepancy is much too large.  This file retains the actual norms of all
divisor phases and paired Fourier prime coefficients.

There is an important scale distinction.  The norm of a divisor phase is

`d ^ (-1 / log R)`.

Consequently a Rankin exponent compatible with prime summability is itself
of order `1 / log R`; its threshold gain is only a fixed exponential
constant.  Thus absolute values do not imply raw pointwise decay, even on a
growing Fourier box (the phase norm is frequency-independent).  The usable
result is instead a sharp arithmetic mass multiplying the common Schwartz
density.  Arbitrarily high Fourier moments then control the complementary
integral.  Cancellation of the full integral, coming from Fourier inversion
and compact support of the cutoff, is the separate interior step.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Topology

/-! ## Exact phase scale and the critical Rankin obstruction -/

theorem SmoothSieveCutoff.norm_divisorMultiplicativePhase_eq_rpow
    {R d : ℕ} (_hR : 1 < R) (hd : 0 < d) (t : ℝ) :
    ‖divisorMultiplicativePhase R d t‖ =
      (d : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) := by
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  rw [divisorMultiplicativePhase,
    SmoothSieveCutoff.norm_cutoffMultiplicativePhase,
    Real.rpow_def_of_pos hdReal]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- A Rankin exponent `θ / log R` produces the fixed threshold factor
`exp (-θ)`, not a quantity tending to zero. -/
theorem rpow_natCast_neg_mul_inv_log
    {R : ℕ} (hR : 1 < R) (θ : ℝ) :
    (R : ℝ) ^ (-θ * (Real.log (R : ℝ))⁻¹) =
      Real.exp (-θ) := by
  have hRReal : 0 < (R : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hR)
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  rw [Real.rpow_def_of_pos hRReal]
  congr 1
  field_simp [hlog.ne']

/-- Deterministic Rankin inequality for one excluded divisor. -/
theorem SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_rankin
    {R d : ℕ} (hR : 1 < R) (hRd : R ≤ d)
    {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    ‖divisorMultiplicativePhase R d t‖ ≤
      (R : ℝ) ^ (-δ) *
        (d : ℝ) ^ (δ - (Real.log (R : ℝ))⁻¹) := by
  have hRpos : 0 < R := Nat.zero_lt_of_lt hR
  have hd : 0 < d := hRpos.trans_le hRd
  have hRReal : 0 < (R : ℝ) := by exact_mod_cast hRpos
  have hdReal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlogle :
      Real.log (R : ℝ) ≤ Real.log (d : ℝ) :=
    Real.log_le_log hRReal (by exact_mod_cast hRd)
  rw [SmoothSieveCutoff.norm_divisorMultiplicativePhase_eq_rpow
    hR hd t]
  rw [Real.rpow_def_of_pos hdReal,
    Real.rpow_def_of_pos hRReal,
    Real.rpow_def_of_pos hdReal,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hδ (sub_nonneg.mpr hlogle)]

/-- Critical-scale version of Rankin's inequality.  The displayed
`exp (-θ)` makes the absence of pointwise asymptotic decay explicit. -/
theorem SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_rankin_log
    {R d : ℕ} (hR : 1 < R) (hRd : R ≤ d)
    {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ) :
    ‖divisorMultiplicativePhase R d t‖ ≤
      Real.exp (-θ) *
        (d : ℝ) ^
          ((θ - 1) * (Real.log (R : ℝ))⁻¹) := by
  have hlog : 0 ≤ Real.log (R : ℝ) :=
    (Real.log_pos (by exact_mod_cast hR : (1 : ℝ) < R)).le
  have h :=
    SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_rankin
      hR hRd
      (mul_nonneg hθ (inv_nonneg.mpr hlog))
      t
  have hthreshold :
      (R : ℝ) ^ (-(θ * (Real.log (R : ℝ))⁻¹)) =
        Real.exp (-θ) := by
    convert rpow_natCast_neg_mul_inv_log hR θ using 1
    ring_nf
  rw [hthreshold] at h
  convert h using 1
  ring_nf

/-! ## Actual coefficient and phase masses -/

/-- The product of the actual paired-prime coefficient norms in one
support fiber. -/
noncomputable def fixedFamilyPrimeSupportActualCoefficientMass
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℝ :=
  ∏ p : {p // p ∈ P},
    ∏ q ∈ support p,
      ‖pairedFourierPrimeCoefficient
        R (p : ℕ) (t q) (u q)‖

theorem norm_fixedFamilyPrimeSupportCoefficient_eq_actualMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖fixedFamilyPrimeSupportCoefficient R t u support‖ =
      fixedFamilyPrimeSupportActualCoefficientMass R t u support := by
  classical
  unfold fixedFamilyPrimeSupportCoefficient
    fixedFamilyPrimeLocalCoefficient
    fixedFamilyPrimeSupportActualCoefficientMass
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro p _hp
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    norm_prod]

/-- Frequency-independent Rankin majorant for the actual support
coefficient. -/
noncomputable def fixedFamilyPrimeSupportRpowCoefficientMass
    {κ : Type*} [Fintype κ]
    (R : ℕ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℝ :=
  ∏ p : {p // p ∈ P},
    (3 * (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)) ^
      (support p).card

theorem fixedFamilyPrimeSupportActualCoefficientMass_le_rpow
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} (hR : 2 ≤ R) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    fixedFamilyPrimeSupportActualCoefficientMass R t u support ≤
      fixedFamilyPrimeSupportRpowCoefficientMass R support := by
  classical
  unfold fixedFamilyPrimeSupportActualCoefficientMass
    fixedFamilyPrimeSupportRpowCoefficientMass
  apply Finset.prod_le_prod
  · intro p _hp
    positivity
  · intro p _hp
    calc
      (∏ q ∈ support p,
          ‖pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q)‖) ≤
          ∏ _q ∈ support p,
            (3 * (p : ℝ) ^
              (-(Real.log (R : ℝ))⁻¹)) := by
        apply Finset.prod_le_prod
        · intro q _hq
          exact norm_nonneg _
        · intro q _hq
          exact
            norm_pairedFourierPrimeCoefficient_le_three_mul_rpow
              hR p (t q) (u q)
      _ =
          (3 * (p : ℝ) ^
            (-(Real.log (R : ℝ))⁻¹)) ^
              (support p).card := by
        simp

/-- Exact phase norm of one squarefree paired divisor family, with the
common cutoff Fourier density removed. -/
noncomputable def pairedDivisorRankinWeight
    {κ : Type*} [Fintype κ]
    (R : ℕ) (z : κ → ℕ × ℕ) : ℝ :=
  ∏ q,
    ((z q).1 : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) *
      ((z q).2 : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)

/-- Sum of the exact divisor-phase norms in one coordinatewise support
fiber. -/
noncomputable def coordinatewiseTruncatedSupportRankinMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℝ :=
  ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
    pairedDivisorRankinWeight R z

theorem SmoothSieveCutoff.norm_transformedPairedDivisorFamily_eq_rankin
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (z : κ → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (t u : κ → ℝ) :
    ‖χ.transformedPairedDivisorFamily R z (t, u)‖ =
      pairedDivisorRankinWeight R z *
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) := by
  classical
  have hleft :
      ∀ q : κ,
        ‖(ArithmeticFunction.moebius (z q).1 : ℂ)‖ = 1 := by
    intro q
    rw [Complex.norm_intCast]
    exact_mod_cast
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (hz q).1
  have hright :
      ∀ q : κ,
        ‖(ArithmeticFunction.moebius (z q).2 : ℂ)‖ = 1 := by
    intro q
    rw [Complex.norm_intCast]
    exact_mod_cast
      ArithmeticFunction.abs_moebius_eq_one_of_squarefree
        (hz q).2
  have hleftPhase :
      ∀ q : κ,
        ‖divisorMultiplicativePhase R (z q).1 (t q)‖ =
          ((z q).1 : ℝ) ^
            (-(Real.log (R : ℝ))⁻¹) := by
    intro q
    exact SmoothSieveCutoff.norm_divisorMultiplicativePhase_eq_rpow
      hR (Nat.pos_of_ne_zero (hz q).1.ne_zero) (t q)
  have hrightPhase :
      ∀ q : κ,
        ‖divisorMultiplicativePhase R (z q).2 (u q)‖ =
          ((z q).2 : ℝ) ^
            (-(Real.log (R : ℝ))⁻¹) := by
    intro q
    exact SmoothSieveCutoff.norm_divisorMultiplicativePhase_eq_rpow
      hR (Nat.pos_of_ne_zero (hz q).2.ne_zero) (u q)
  unfold transformedPairedDivisorFamily
    transformedDivisorFamilySide
    pairedDivisorRankinWeight
    SmoothSieveCutoff.fourierProductMomentDensity
    SmoothSieveCutoff.fourierMomentDensity
  simp only [norm_mul, norm_prod, hleft, hright,
    hleftPhase, hrightPhase, pow_zero, one_mul]
  simp only [Finset.prod_mul_distrib]
  ring

/-- The exact coordinatewise coefficient is bounded by its phase-weighted
Rankin fiber mass, rather than by the raw fiber cardinality. -/
theorem norm_coordinatewiseTruncatedSupportCoefficient_le_rankinMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖coordinatewiseTruncatedSupportCoefficient
        χ R P t u support‖ ≤
      coordinatewiseTruncatedSupportRankinMass R P support *
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) := by
  classical
  rw [coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber]
  calc
    ‖∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        χ.transformedPairedDivisorFamily R z (t, u)‖ ≤
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        ‖χ.transformedPairedDivisorFamily R z (t, u)‖ :=
      norm_sum_le _ _
    _ =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        pairedDivisorRankinWeight R z *
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u) := by
      apply Finset.sum_congr rfl
      intro z hzFiber
      have hzSquarefree :
          SquarefreePairedDivisorChoice z :=
        (SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp
          ((mem_coordinatewiseTruncatedSupportFiber.mp hzFiber).1)).2
      exact χ.norm_transformedPairedDivisorFamily_eq_rankin
        hR z hzSquarefree t u
    _ = _ := by
      unfold coordinatewiseTruncatedSupportRankinMass
      rw [Finset.sum_mul]

/-- Sharp frequency-independent Rankin bound for one support discrepancy. -/
theorem norm_coordinatewiseTruncationSupportDiscrepancy_le_rankinMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 2 ≤ R)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖coordinatewiseTruncationSupportDiscrepancy
        χ R P t u support‖ ≤
      (coordinatewiseTruncatedSupportRankinMass R P support +
        fixedFamilyPrimeSupportRpowCoefficientMass R support) *
      (χ.fourierProductMomentDensity (fun _ => 0) t *
        χ.fourierProductMomentDensity (fun _ => 0) u) := by
  unfold coordinatewiseTruncationSupportDiscrepancy
  have htruncated :=
    norm_coordinatewiseTruncatedSupportCoefficient_le_rankinMass
      χ (by omega : 1 < R) P t u support
  have hcoefficient :
      ‖fixedFamilyPrimeSupportCoefficient R t u support‖ ≤
        fixedFamilyPrimeSupportRpowCoefficientMass R support := by
    rw [norm_fixedFamilyPrimeSupportCoefficient_eq_actualMass]
    exact
      fixedFamilyPrimeSupportActualCoefficientMass_le_rpow
        hR t u support
  have hdensity :
      0 ≤
        χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u :=
    mul_nonneg
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) t)
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) u)
  calc
    ‖coordinatewiseTruncatedSupportCoefficient χ R P t u support -
        pairedCutoffFourierEnvelope χ t u *
          fixedFamilyPrimeSupportCoefficient R t u support‖ ≤
      ‖coordinatewiseTruncatedSupportCoefficient χ R P t u support‖ +
        ‖pairedCutoffFourierEnvelope χ t u *
          fixedFamilyPrimeSupportCoefficient R t u support‖ :=
      norm_sub_le _ _
    _ =
      ‖coordinatewiseTruncatedSupportCoefficient χ R P t u support‖ +
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) *
          ‖fixedFamilyPrimeSupportCoefficient R t u support‖ := by
      rw [norm_mul, norm_pairedCutoffFourierEnvelope]
    _ ≤
      coordinatewiseTruncatedSupportRankinMass R P support *
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u) +
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) *
          fixedFamilyPrimeSupportRpowCoefficientMass R support := by
      exact add_le_add htruncated
        (mul_le_mul_of_nonneg_left hcoefficient hdensity)
    _ = _ := by ring

/-- Arithmetic Rankin mass of the complete fixed-family discrepancy.  The
actual phase decay is retained in both its truncated and unrestricted
pieces. -/
noncomputable def fixedFamilyCoordinatewiseTruncationRankinMass
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) : ℝ :=
  ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
    (coordinatewiseTruncatedSupportRankinMass R P support +
      fixedFamilyPrimeSupportRpowCoefficientMass R support) *
      ‖fixedFamilyPrimeSupportDensity forms support‖

theorem fixedFamilyCoordinatewiseTruncationRankinMass_nonneg
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) :
    0 ≤ fixedFamilyCoordinatewiseTruncationRankinMass R forms P := by
  unfold fixedFamilyCoordinatewiseTruncationRankinMass
  apply Finset.sum_nonneg
  intro support _hsupport
  apply mul_nonneg
  · apply add_nonneg
    · unfold coordinatewiseTruncatedSupportRankinMass
        pairedDivisorRankinWeight
      exact Finset.sum_nonneg fun z _hz => by positivity
    · unfold fixedFamilyPrimeSupportRpowCoefficientMass
      positivity
  · exact norm_nonneg _

/-- Pointwise domination of the entire fixed-family discrepancy by the
frequency-independent arithmetic Rankin mass times the paired Schwartz
density. -/
theorem norm_sum_coordinatewiseTruncationSupportDiscrepancy_le_rankinMass
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ) :
    ‖∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        coordinatewiseTruncationSupportDiscrepancy
            χ R P t u support *
          fixedFamilyPrimeSupportDensity forms support‖ ≤
      fixedFamilyCoordinatewiseTruncationRankinMass R forms P *
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) := by
  classical
  calc
    ‖∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        coordinatewiseTruncationSupportDiscrepancy
            χ R P t u support *
          fixedFamilyPrimeSupportDensity forms support‖ ≤
      ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        ‖coordinatewiseTruncationSupportDiscrepancy
            χ R P t u support *
          fixedFamilyPrimeSupportDensity forms support‖ :=
      norm_sum_le _ _
    _ ≤
      ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        ((coordinatewiseTruncatedSupportRankinMass R P support +
            fixedFamilyPrimeSupportRpowCoefficientMass R support) *
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u)) *
          ‖fixedFamilyPrimeSupportDensity forms support‖ := by
      apply Finset.sum_le_sum
      intro support _hsupport
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_coordinatewiseTruncationSupportDiscrepancy_le_rankinMass
          χ hR P t u support)
        (norm_nonneg _)
    _ =
      fixedFamilyCoordinatewiseTruncationRankinMass R forms P *
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) := by
      unfold fixedFamilyCoordinatewiseTruncationRankinMass
      simp_rw [mul_assoc]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro support _hsupport
      ring

/-! ## Canonical carry Rankin mass -/

/-- The sharp arithmetic Rankin mass after summing the canonical carry
cells. -/
noncomputable def cfzCanonicalCarryTruncationRankinMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b R : ℕ) (forms : κ → CFZFormIndex k) : ℝ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    |cfzCanonicalCarryCellDensity
        (N := N) forms carry| *
      fixedFamilyCoordinatewiseTruncationRankinMass
        R
        (cfzCarryAdjustedFamilyAtVector N W b forms carry)
        (primesLEAsPrimes R)

theorem cfzCanonicalCarryTruncationRankinMass_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b R : ℕ) (forms : κ → CFZFormIndex k) :
    0 ≤ cfzCanonicalCarryTruncationRankinMass
      (N := N) W b R forms := by
  unfold cfzCanonicalCarryTruncationRankinMass
  exact Finset.sum_nonneg fun carry _hcarry =>
    mul_nonneg (abs_nonneg _)
      (fixedFamilyCoordinatewiseTruncationRankinMass_nonneg
        R
        (cfzCarryAdjustedFamilyAtVector N W b forms carry)
        (primesLEAsPrimes R))

/-- Pointwise canonical carry-discrepancy bound with the actual Rankin
weights retained. -/
theorem norm_cfzCanonicalCarryTruncationDiscrepancy_le_rankinMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) :
    ‖cfzCanonicalCarryTruncationDiscrepancy
        (N := N) χ W b R forms t u‖ ≤
      cfzCanonicalCarryTruncationRankinMass
          (N := N) W b R forms *
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) := by
  classical
  unfold cfzCanonicalCarryTruncationDiscrepancy
    cfzCanonicalCarryTruncationRankinMass
  calc
    ‖∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        (cfzCanonicalCarryCellDensity
            (N := N) forms carry : ℂ) *
          ∑ support ∈
              fixedFamilyPrimeSupportAssignmentChoices
                κ (primesLEAsPrimes R),
            coordinatewiseTruncationSupportDiscrepancy
                χ R (primesLEAsPrimes R) t u support *
              cfzCanonicalCarryPrimeSupportDensity
                N W b forms carry support‖ ≤
      ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        ‖(cfzCanonicalCarryCellDensity
              (N := N) forms carry : ℂ) *
          ∑ support ∈
              fixedFamilyPrimeSupportAssignmentChoices
                κ (primesLEAsPrimes R),
            coordinatewiseTruncationSupportDiscrepancy
                χ R (primesLEAsPrimes R) t u support *
              cfzCanonicalCarryPrimeSupportDensity
                N W b forms carry support‖ :=
      norm_sum_le _ _
    _ ≤
      ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        |cfzCanonicalCarryCellDensity
            (N := N) forms carry| *
          (fixedFamilyCoordinatewiseTruncationRankinMass
              R
              (cfzCarryAdjustedFamilyAtVector
                N W b forms carry)
              (primesLEAsPrimes R) *
            (χ.fourierProductMomentDensity (fun _ => 0) t *
              χ.fourierProductMomentDensity (fun _ => 0) u)) := by
      apply Finset.sum_le_sum
      intro carry _hcarry
      rw [norm_mul, Complex.norm_real]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [cfzCanonicalCarryPrimeSupportDensity] using
        norm_sum_coordinatewiseTruncationSupportDiscrepancy_le_rankinMass
          χ hR
          (cfzCarryAdjustedFamilyAtVector N W b forms carry)
          (primesLEAsPrimes R) t u
    _ =
      (∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
        |cfzCanonicalCarryCellDensity
            (N := N) forms carry| *
          fixedFamilyCoordinatewiseTruncationRankinMass
            R
            (cfzCarryAdjustedFamilyAtVector N W b forms carry)
            (primesLEAsPrimes R)) *
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro carry _hcarry
      ring

/-- The canonical carry discrepancy is a continuous function of its
Fourier variables. -/
theorem continuous_cfzCanonicalCarryTruncationDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k) :
    Continuous
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R forms tu.1 tu.2) := by
  classical
  unfold cfzCanonicalCarryTruncationDiscrepancy
    coordinatewiseTruncationSupportDiscrepancy
    coordinatewiseTruncatedSupportCoefficient
    pairedCutoffFourierEnvelope
    fixedFamilyPrimeSupportCoefficient
    fixedFamilyPrimeLocalCoefficient
    pairedFourierPrimeCoefficient
    SmoothSieveCutoff.transformedPairedDivisorFamily
    SmoothSieveCutoff.transformedDivisorFamilySide
    SmoothSieveCutoff.divisorMultiplicativePhase
    SmoothSieveCutoff.cutoffMultiplicativePhase
  have hχ : Continuous χ.cutoffFourierTransform :=
    χ.cutoffFourierTransform_continuous
  fun_prop

/-- The pointwise Rankin domination also proves integrability. -/
theorem integrable_cfzCanonicalCarryTruncationDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → CFZFormIndex k) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R forms tu.1 tu.2)
      (volume.prod volume) := by
  let mass :=
    cfzCanonicalCarryTruncationRankinMass
      (N := N) W b R forms
  have hmajorant :
      Integrable
        (fun tu : (κ → ℝ) × (κ → ℝ) =>
          mass *
            (χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
              χ.fourierProductMomentDensity (fun _ => 0) tu.2))
        (volume.prod volume) := by
    exact
      ((χ.integrable_fourierProductMomentDensity
          (fun _ => 0)).mul_prod
        (χ.integrable_fourierProductMomentDensity
          (fun _ => 0))).const_mul mass
  apply hmajorant.mono'
  · exact
      (continuous_cfzCanonicalCarryTruncationDiscrepancy
        χ W b R forms).aestronglyMeasurable
  · exact ae_of_all _ fun tu =>
      norm_cfzCanonicalCarryTruncationDiscrepancy_le_rankinMass
        χ W b hR forms tu.1 tu.2

/-! ## Growing-box complementary integral -/

/-- The complementary integral of the selected canonical carry discrepancy
is bounded by the sharp Rankin mass times the universal paired Schwartz
tail. -/
theorem
    norm_integral_selectedCFZCanonicalCarryTruncationDiscrepancy_compl_le_rankinMass
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (e : LinearFormsExponent k) (T : ℝ) :
    ‖∫ tu in
          (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R
          (fun q : SelectedCFZFormIndex e => q.1)
          tu.1 tu.2
        ∂(volume.prod volume)‖ ≤
      cfzCanonicalCarryTruncationRankinMass
          (N := N) W b R
          (fun q : SelectedCFZFormIndex e => q.1) *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  have hdom :
      ∀ᵐ tu ∂(volume.prod volume).restrict
          (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
        ‖cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2‖ ≤
          cfzCanonicalCarryTruncationRankinMass
              (N := N) W b R
              (fun q : SelectedCFZFormIndex e => q.1) *
            χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
    exact ae_of_all _ fun tu =>
      norm_cfzCanonicalCarryTruncationDiscrepancy_le_rankinMass
        χ W b hR
        (fun q : SelectedCFZFormIndex e => q.1)
        tu.1 tu.2
  have hbound :=
    norm_integral_le_of_norm_le
      ((χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
        (cfzCanonicalCarryTruncationRankinMass
          (N := N) W b R
          (fun q : SelectedCFZFormIndex e => q.1)) |>.integrableOn)
      hdom
  simpa [SmoothSieveCutoff.selectedCFZPairedFourierAbsoluteTail,
    integral_const_mul] using hbound

/-- High-moment form at the conventional radius `sqrt (log R)`. -/
theorem
    norm_integral_selectedCFZCanonicalCarryTruncationDiscrepancy_sqrt_log_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (e : LinearFormsExponent k) (n : ℕ) :
    ‖∫ tu in
          (SmoothSieveCutoff.selectedCFZPairedFourierBox e
            (Real.sqrt (Real.log R)))ᶜ,
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R
          (fun q : SelectedCFZFormIndex e => q.1)
          tu.1 tu.2
        ∂(volume.prod volume)‖ ≤
      cfzCanonicalCarryTruncationRankinMass
          (N := N) W b R
          (fun q : SelectedCFZFormIndex e => q.1) *
        (χ.selectedCFZPairedFourierAbsoluteMoment e (2 * n) /
          (Real.log R) ^ n) := by
  exact
    (norm_integral_selectedCFZCanonicalCarryTruncationDiscrepancy_compl_le_rankinMass
      χ W b hR e (Real.sqrt (Real.log R))).trans
      (mul_le_mul_of_nonneg_left
        (χ.selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
          e n hR)
        (cfzCanonicalCarryTruncationRankinMass_nonneg
          W b R (fun q : SelectedCFZFormIndex e => q.1)))

/-! ## Selberg-scaled complementary discrepancy -/

namespace SmoothSieveCutoff

/-- Norm of the fully Selberg-scaled canonical truncation discrepancy on
the complementary Fourier region. -/
noncomputable def
    selectedCFZCanonicalCarryScaledTruncationTailNorm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) : ℝ :=
  ‖(normalizedSelbergScale χ.normalizer R W : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      (((Real.log R ^ 2 : ℝ) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        ∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
          cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2
          ∂(volume.prod volume))‖

theorem selectedCFZCanonicalCarryScaledTruncationTailNorm_nonneg
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) :
    0 ≤ χ.selectedCFZCanonicalCarryScaledTruncationTailNorm
      (N := N) W b R e T :=
  norm_nonneg _

/-- The exact Selberg prefactors multiplying the sharp canonical Rankin
mass. -/
noncomputable def
    selectedCFZCanonicalCarryScaledTruncationRankinMass
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (e : LinearFormsExponent k) : ℝ :=
  |normalizedSelbergScale χ.normalizer R W| ^
      Fintype.card (SelectedCFZFormIndex e) *
    |Real.log R ^ 2| ^
      Fintype.card (SelectedCFZFormIndex e) *
    cfzCanonicalCarryTruncationRankinMass
      (N := N) W b R
      (fun q : SelectedCFZFormIndex e => q.1)

theorem selectedCFZCanonicalCarryScaledTruncationRankinMass_nonneg
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
      (N := N) W b R e := by
  unfold selectedCFZCanonicalCarryScaledTruncationRankinMass
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))
    (cfzCanonicalCarryTruncationRankinMass_nonneg
      W b R (fun q : SelectedCFZFormIndex e => q.1))

theorem
    selectedCFZCanonicalCarryScaledTruncationTailNorm_le_rankinMass
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (e : LinearFormsExponent k) (T : ℝ) :
    χ.selectedCFZCanonicalCarryScaledTruncationTailNorm
        (N := N) W b R e T ≤
      χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
          (N := N) W b R e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  unfold selectedCFZCanonicalCarryScaledTruncationTailNorm
    selectedCFZCanonicalCarryScaledTruncationRankinMass
  rw [norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs]
  let A :=
    |normalizedSelbergScale χ.normalizer R W| ^
        Fintype.card (SelectedCFZFormIndex e) *
      |Real.log R ^ 2| ^
        Fintype.card (SelectedCFZFormIndex e)
  have hA : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _)
  have hintegral :=
    norm_integral_selectedCFZCanonicalCarryTruncationDiscrepancy_compl_le_rankinMass
      (N := N) χ W b hR e T
  calc
    |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        (|Real.log R ^ 2| ^
            Fintype.card (SelectedCFZFormIndex e) *
          ‖∫ tu in
              (selectedCFZPairedFourierBox e T)ᶜ,
            cfzCanonicalCarryTruncationDiscrepancy
              χ W b R (fun q : SelectedCFZFormIndex e => q.1)
              tu.1 tu.2
            ∂(volume.prod volume)‖) =
        A *
          ‖∫ tu in
              (selectedCFZPairedFourierBox e T)ᶜ,
            cfzCanonicalCarryTruncationDiscrepancy
              χ W b R (fun q : SelectedCFZFormIndex e => q.1)
              tu.1 tu.2
            ∂(volume.prod volume)‖ := by
      ring
    _ ≤ A *
        (cfzCanonicalCarryTruncationRankinMass
            W b R (fun q : SelectedCFZFormIndex e => q.1) *
          χ.selectedCFZPairedFourierAbsoluteTail e T) :=
      mul_le_mul_of_nonneg_left hintegral hA
    _ =
        (|normalizedSelbergScale χ.normalizer R W| ^
              Fintype.card (SelectedCFZFormIndex e) *
            |Real.log R ^ 2| ^
              Fintype.card (SelectedCFZFormIndex e) *
            cfzCanonicalCarryTruncationRankinMass
              W b R (fun q : SelectedCFZFormIndex e => q.1)) *
          χ.selectedCFZPairedFourierAbsoluteTail e T := by
      ring

theorem
    selectedCFZCanonicalCarryScaledTruncationTailNorm_sqrt_log_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (e : LinearFormsExponent k) (n : ℕ) :
    χ.selectedCFZCanonicalCarryScaledTruncationTailNorm
        (N := N) W b R e
        (Real.sqrt (Real.log R)) ≤
      χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
          (N := N) W b R e *
        (χ.selectedCFZPairedFourierAbsoluteMoment e (2 * n) /
          (Real.log R) ^ n) := by
  exact
    (χ.selectedCFZCanonicalCarryScaledTruncationTailNorm_le_rankinMass
      (N := N) W b hR e (Real.sqrt (Real.log R))).trans
      (mul_le_mul_of_nonneg_left
        (χ.selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
          e n hR)
        (χ.selectedCFZCanonicalCarryScaledTruncationRankinMass_nonneg
          (N := N) W b R e))

/-- Any polylogarithmic bound for the sharp scaled Rankin mass is absorbed
by one additional paired Fourier moment.  This gives the desired
Selberg-normalized growing-box complementary decay. -/
theorem
    tendsto_selectedCFZCanonicalCarryScaledTruncationTailNorm_sqrt_log_of_polylog
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) (e : LinearFormsExponent k)
    (E : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hMass :
      ∀ᶠ R : ℕ in atTop,
        χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
            (N := N) W b R e ≤
          C * (1 + Real.log R) ^ E) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZCanonicalCarryScaledTruncationTailNorm
          (N := N) W b R e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  let M :=
    χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1))
  let K : ℝ := C * M * 2 ^ E
  have hM : 0 ≤ M := by
    unfold M
    exact χ.selectedCFZPairedFourierAbsoluteMoment_nonneg
      e (2 * (E + 1))
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hlogTop :
      Tendsto (fun R : ℕ => Real.log R) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvLog :
      Tendsto (fun R : ℕ => (Real.log R)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlogTop
  have hupper :
      Tendsto (fun R : ℕ => K / Real.log R) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinvLog :
        Tendsto
          (fun R : ℕ => K * (Real.log R)⁻¹)
          atTop (𝓝 (K * 0)))
  have hRtwo : ∀ᶠ R : ℕ in atTop, 2 ≤ R :=
    eventually_ge_atTop 2
  have hlogOne : ∀ᶠ R : ℕ in atTop, 1 ≤ Real.log R :=
    hlogTop.eventually (eventually_ge_atTop 1)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R =>
      χ.selectedCFZCanonicalCarryScaledTruncationTailNorm_nonneg
        (N := N) W b R e _
  · filter_upwards [hMass, hRtwo, hlogOne] with R hMassR hR hlogR
    have hlogPos : 0 < Real.log R :=
      lt_of_lt_of_le zero_lt_one hlogR
    have hquotient :
        0 ≤ M / (Real.log R) ^ (E + 1) :=
      div_nonneg hM (pow_nonneg hlogPos.le (E + 1))
    calc
      χ.selectedCFZCanonicalCarryScaledTruncationTailNorm
          (N := N) W b R e
          (Real.sqrt (Real.log R)) ≤
        χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
            (N := N) W b R e *
          (M / (Real.log R) ^ (E + 1)) := by
        simpa [M] using
          χ.selectedCFZCanonicalCarryScaledTruncationTailNorm_sqrt_log_le
            (N := N) W b hR e (E + 1)
      _ ≤
        (C * (1 + Real.log R) ^ E) *
          (M / (Real.log R) ^ (E + 1)) :=
        mul_le_mul_of_nonneg_right hMassR hquotient
      _ =
        (C * M) *
          ((1 + Real.log R) ^ E /
            (Real.log R) ^ (E + 1)) := by
        ring
      _ ≤
        (C * M) * ((2 : ℝ) ^ E / Real.log R) :=
        mul_le_mul_of_nonneg_left
          (one_add_pow_div_pow_succ_le_inv E hlogR) hCM
      _ = K / Real.log R := by
        unfold K
        ring
  · exact hupper

/-- Selberg-scaled norm of the canonical truncation discrepancy on the
interior Fourier box. -/
noncomputable def
    selectedCFZCanonicalCarryScaledTruncationBoxNorm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) : ℝ :=
  ‖(normalizedSelbergScale χ.normalizer R W : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      (((Real.log R ^ 2 : ℝ) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        ∫ tu in selectedCFZPairedFourierBox e T,
          cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2
          ∂(volume.prod volume))‖

/-- Once full-space Fourier inversion proves that the discrepancy integral
is zero, its interior-box norm equals the complementary-tail norm. -/
theorem selectedCFZCanonicalCarryScaledTruncationBoxNorm_eq_tailNorm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (e : LinearFormsExponent k) (T : ℝ)
    (hR : 2 ≤ R)
    (hzero :
      (∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R
          (fun q : SelectedCFZFormIndex e => q.1)
          tu.1 tu.2
        ∂(volume.prod volume)) = 0) :
    χ.selectedCFZCanonicalCarryScaledTruncationBoxNorm
        (N := N) W b R e T =
      χ.selectedCFZCanonicalCarryScaledTruncationTailNorm
        (N := N) W b R e T := by
  have hintegrable :=
    integrable_cfzCanonicalCarryTruncationDiscrepancy
      (N := N) χ W b hR
      (fun q : SelectedCFZFormIndex e => q.1)
  have hcompl :=
    setIntegral_compl
      (measurableSet_selectedCFZPairedFourierBox e T)
      hintegrable
  rw [hzero, zero_sub] at hcompl
  have hinside :
      (∫ tu in selectedCFZPairedFourierBox e T,
          cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2
          ∂(volume.prod volume)) =
        -(∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2
          ∂(volume.prod volume)) := by
    rw [hcompl]
    simp
  unfold selectedCFZCanonicalCarryScaledTruncationBoxNorm
    selectedCFZCanonicalCarryScaledTruncationTailNorm
  rw [hinside, mul_neg, mul_neg, norm_neg]

/-- Integrated closure theorem.  It records the mathematically correct
remaining input: full-space cancellation from Fourier inversion, together
with a polylogarithmic sharp Rankin mass.  Under those inputs the normalized
growing Fourier-box discrepancy vanishes. -/
theorem
    tendsto_selectedCFZCanonicalCarryScaledTruncationBoxNorm_sqrt_log_of_integral_zero
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) (e : LinearFormsExponent k)
    (E : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hMass :
      ∀ᶠ R : ℕ in atTop,
        χ.selectedCFZCanonicalCarryScaledTruncationRankinMass
            (N := N) W b R e ≤
          C * (1 + Real.log R) ^ E)
    (hzero :
      ∀ R : ℕ,
        (∫ tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ),
          cfzCanonicalCarryTruncationDiscrepancy
            (N := N) χ W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2
          ∂(volume.prod volume)) = 0) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZCanonicalCarryScaledTruncationBoxNorm
          (N := N) W b R e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  have htail :=
    χ.tendsto_selectedCFZCanonicalCarryScaledTruncationTailNorm_sqrt_log_of_polylog
      (N := N) W b e E C hC hMass
  apply htail.congr'
  filter_upwards [eventually_ge_atTop 2] with R hR
  exact
    (χ.selectedCFZCanonicalCarryScaledTruncationBoxNorm_eq_tailNorm
      (N := N) W b R e (Real.sqrt (Real.log R))
      hR (hzero R)).symm

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
