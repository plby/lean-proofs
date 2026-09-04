import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorIntegralCancellation
import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorRankinMassPolylog
import Wikipedia.GreenTao.Sieve.CFZCarryEulerFactorization
import Wikipedia.GreenTao.Sieve.CFZCarryFourierTailBound

/-!
# Complete Euler series for the canonical carry model

The canonical divisor expansion naturally produces a finite Euler product
over the primes at most the Selberg radius.  This file defines the honest
complete prime-support series, identifies it with the existing paired
Fourier Euler product, and compares its Fourier integral with the finite
prime-support expression.

There are two logically separate convergence statements.

* At each fixed Fourier frequency the support series is absolutely
  convergent.  In the selected CFZ primorial regime this follows from the
  exact integer coefficient geometry proved below.
* After multiplication by the paired Schwartz envelope, the series is
  absolutely summable in `L¹`.  This is what permits termwise Fourier
  inversion.  It is stronger than pointwise absolute convergence and is
  proved explicitly below rather than inferred from a pointwise `tsum`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## Integer coefficient geometry of canonical carry vectors -/

/-- A selected canonical carry family has no zero coefficient vector after
primorial scaling.  The carry and the reduced-residue representative occur
only in the affine constants. -/
theorem selectedCFZCarryAdjustedFamilyAtVector_nonzero
    {k N w b : ℕ}
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ) :
    NonzeroCoefficientVectors
      (cfzCarryAdjustedFamilyAtVector
        N (primorial w) b
        (fun q : SelectedCFZFormIndex e => q.1) carry) := by
  intro q hzero
  apply cfzCoefficient_ne_zero hk q.1
  funext v
  have hv := congrFun hzero v
  simp only [cfzCarryAdjustedFamilyAtVector,
    cfzCarryAdjustedAffineForm_coefficient] at hv
  have hW : ((primorial w : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (primorial_pos w).ne'
  exact (mul_eq_zero.mp hv).resolve_left hW

/-- Distinct selected canonical carry forms retain pairwise
non-proportional coefficient vectors after primorial scaling. -/
theorem selectedCFZCarryAdjustedFamilyAtVector_pairwiseIndependent
    {k N w b : ℕ}
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ) :
    PairwiseIndependentCoefficients
      (cfzCarryAdjustedFamilyAtVector
        N (primorial w) b
        (fun q : SelectedCFZFormIndex e => q.1) carry) := by
  intro q r hqr hproportional
  have hqr' : q.1 ≠ r.1 := by
    intro h
    exact hqr (Subtype.ext h)
  have horiginal :=
    cfzAffineForms_pairwiseIndependent hk hqr'
  apply horiginal
  intro v x
  have hscaled := hproportional v x
  simp only [cfzCarryAdjustedFamilyAtVector,
    cfzCarryAdjustedAffineForm_coefficient] at hscaled
  have hW : ((primorial w : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (primorial_pos w).ne'
  have hW2 :
      ((primorial w : ℤ) * (primorial w : ℤ)) ≠ 0 :=
    mul_ne_zero hW hW
  apply mul_left_cancel₀ hW2
  calc
    (primorial w : ℤ) * (primorial w : ℤ) *
          (cfzCoefficient q.1 v * cfzCoefficient r.1 x) =
        ((primorial w : ℤ) * cfzCoefficient q.1 v) *
          ((primorial w : ℤ) * cfzCoefficient r.1 x) := by
      ring
    _ =
        ((primorial w : ℤ) * cfzCoefficient q.1 x) *
          ((primorial w : ℤ) * cfzCoefficient r.1 v) :=
      hscaled
    _ =
        (primorial w : ℤ) * (primorial w : ℤ) *
          (cfzCoefficient q.1 x * cfzCoefficient r.1 v) := by
      ring

/-! ## The honest complete support series and Euler integrand -/

/-- The full squarefree prime-support series for one canonical carry
vector.  Unlike the finite powerset in
`cfzCanonicalCarryUnrestrictedFourierAverage`, the support index ranges
over every finite set of natural primes. -/
noncomputable def cfzCanonicalCarryCompletePrimeSupportSeries
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ) : ℂ :=
  ∑' S : Finset Nat.Primes,
    unrestrictedPrimeSupportTerm
      (cfzCanonicalCarryPairedFourierPrimeLocalFactor
        N W b R forms carry t u) S

/-- Carry-weighted complete prime-support average. -/
noncomputable def cfzCanonicalCarryCompleteFourierAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    (cfzCanonicalCarryCellDensity
        (N := N) forms carry : ℂ) *
      cfzCanonicalCarryCompletePrimeSupportSeries
        N W b R forms carry t u

/-- The complete canonical carry Euler integrand.  It is written as a
support `tsum` inside each finite carry cell; later the `L¹` theorem
justifies integrating this pointwise series. -/
noncomputable def SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  pairedCutoffFourierEnvelope χ tu.1 tu.2 *
    cfzCanonicalCarryCompleteFourierAverage
      (N := N) W b R forms tu.1 tu.2

/-- Difference between the finite prime-support Euler integrand occurring
in the canonical divisor expansion and the honest complete support
integrand. -/
noncomputable def SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  pairedCutoffFourierEnvelope χ tu.1 tu.2 *
      cfzCanonicalCarryUnrestrictedFourierAverage
        (N := N) W b R forms tu.1 tu.2 -
    χ.cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) W b R forms tu

/-- Exact complete Euler identification for one selected canonical carry
vector in the primorial regime.  All coefficient-geometry hypotheses have
been discharged. -/
theorem tsum_selectedCFZCanonicalCarry_unrestrictedPrimeSupport_eq
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ) :
    cfzCanonicalCarryCompletePrimeSupportSeries
        N (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) carry t u =
      (cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R
            (cfzCarryAdjustedFamilyAtVector
              N (primorial w) b
              (fun q : SelectedCFZFormIndex e => q.1) carry)
            t u p := by
  unfold cfzCanonicalCarryCompletePrimeSupportSeries
  exact
    tsum_cfzCanonicalCarry_unrestrictedPrimeSupport_eq
      N (primorial w) b
      (fun q : SelectedCFZFormIndex e => q.1) carry
      (selectedCFZCarryAdjustedFamilyAtVector_nonzero hk e carry)
      (selectedCFZCarryAdjustedFamilyAtVector_pairwiseIndependent
        hk e carry)
      hR t u

/-- Complete carry-weighted Euler identification, with a separate exact
Euler product for every canonical carry vector. -/
theorem cfzCanonicalCarryCompleteFourierAverage_eq_euler
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ) :
    cfzCanonicalCarryCompleteFourierAverage
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) t u =
      ∑ carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
        (cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1) carry : ℂ) *
          ((cutoffZetaSingularFactor R t u *
              cutoffZetaSystemFactor R t u) *
            ∏' p : Nat.Primes,
              primePairedFourierArithmeticToZetaLocalRatio
                R
                (cfzCarryAdjustedFamilyAtVector
                  N (primorial w) b
                  (fun q : SelectedCFZFormIndex e => q.1) carry)
                t u p) := by
  classical
  unfold cfzCanonicalCarryCompleteFourierAverage
  apply Finset.sum_congr rfl
  intro carry _hcarry
  rw [tsum_selectedCFZCanonicalCarry_unrestrictedPrimeSupport_eq
    hk e carry hR t u]

/-! ## Expanding one active prime support into nonempty form supports -/

/-- Form-support assignments in which every prime of `P` is genuinely
active.  This is the support-assignment counterpart of one term indexed by
`P : Finset Nat.Primes` in `unrestrictedPrimeSupportTerm`. -/
def fixedFamilyNonemptyPrimeSupportAssignmentChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (P : Finset Nat.Primes) :
    Finset (FixedFamilyPrimeSupportAssignment κ P) :=
  Fintype.piFinset fun _p : {p // p ∈ P} =>
    (Finset.univ : Finset κ).powerset.erase ∅

theorem mem_fixedFamilyNonemptyPrimeSupportAssignmentChoices
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : Finset Nat.Primes}
    {support : FixedFamilyPrimeSupportAssignment κ P} :
    support ∈ fixedFamilyNonemptyPrimeSupportAssignmentChoices κ P ↔
      ∀ p, (support p).Nonempty := by
  classical
  simp [fixedFamilyNonemptyPrimeSupportAssignmentChoices,
    Finset.nonempty_iff_ne_empty]

/-- Removing the empty form support from the local inclusion--exclusion
formula gives exactly `localFactor - 1`. -/
theorem pairedFourierPrimeLocalFactor_sub_one_eq_sum_nonemptySupport
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) :
    pairedFourierPrimeLocalFactor R forms t u p - 1 =
      ∑ s ∈ (Finset.univ : Finset κ).powerset.erase ∅,
        fixedFamilyPrimeLocalSupportTerm R forms t u p s := by
  rw [pairedFourierPrimeLocalFactor_eq_fixedFamilySupportSum]
  have hempty :
      (∅ : Finset κ) ∈
        (Finset.univ : Finset κ).powerset := by
    simp
  rw [← Finset.sum_erase_add _ _ hempty]
  simp [fixedFamilyPrimeLocalSupportTerm,
    fixedFamilyPrimeLocalCoefficient]

/-- Exact refinement of one unrestricted active-prime term into nonempty
form-support assignments. -/
theorem unrestrictedPrimeSupportTerm_eq_sum_nonemptyAssignments
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ) :
    unrestrictedPrimeSupportTerm
        (pairedFourierPrimeLocalFactor R forms t u) P =
      ∑ support ∈
          fixedFamilyNonemptyPrimeSupportAssignmentChoices κ P,
        fixedFamilyPrimeSupportEulerTerm
          R forms P t u support := by
  classical
  unfold unrestrictedPrimeSupportTerm
  calc
    (∏ p ∈ P,
        (pairedFourierPrimeLocalFactor R forms t u p - 1)) =
        ∏ p : {p // p ∈ P},
          (pairedFourierPrimeLocalFactor R forms t u p.1 - 1) := by
      exact
        (Finset.prod_coe_sort P
          (fun p : Nat.Primes =>
            pairedFourierPrimeLocalFactor R forms t u p - 1)).symm
    _ =
        ∏ p : {p // p ∈ P},
          ∑ s ∈ (Finset.univ : Finset κ).powerset.erase ∅,
            fixedFamilyPrimeLocalSupportTerm
              R forms t u p.1 s := by
      apply Finset.prod_congr rfl
      intro p _hp
      rw [pairedFourierPrimeLocalFactor_sub_one_eq_sum_nonemptySupport]
    _ = _ := by
      unfold fixedFamilyNonemptyPrimeSupportAssignmentChoices
        fixedFamilyPrimeSupportEulerTerm
      rw [Finset.prod_univ_sum]

/-- Every enveloped term of the complete support series is integrable.
The proof uses the exact finite nonempty-support refinement and the
three-state Fourier expansion, rather than a measurability assertion about
an infinite Euler product. -/
theorem SmoothSieveCutoff.integrable_pairedEnvelope_mul_unrestrictedPrimeSupportTerm
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff)
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (pairedFourierPrimeLocalFactor
              R forms tu.1 tu.2) P)
      (volume.prod volume) := by
  classical
  have hsum :
      Integrable
        (fun tu : (κ → ℝ) × (κ → ℝ) =>
          ∑ support ∈
              fixedFamilyNonemptyPrimeSupportAssignmentChoices κ P,
            pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              fixedFamilyPrimeSupportEulerTerm
                R forms P tu.1 tu.2 support)
        (volume.prod volume) := by
    apply integrable_finsetSum
    intro support _hsupport
    have h :=
      (integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
        χ R support).mul_const
          (fixedFamilyPrimeSupportDensity forms support)
    apply h.congr
    exact ae_of_all _ fun tu => by
      dsimp only
      rw [fixedFamilyPrimeSupportEulerTerm_eq_coefficient_mul_density
        R forms P tu.1 tu.2 support]
      ring
  apply hsum.congr
  exact ae_of_all _ fun tu => by
    dsimp only
    rw [unrestrictedPrimeSupportTerm_eq_sum_nonemptyAssignments,
      Finset.mul_sum]

/-! ## A large active prime is killed by full-space Fourier inversion -/

/-- If an active prime is larger than the coordinatewise divisor cutoff,
every three-state refinement places it in at least one divisor and hence
lies outside the smooth divisor box. -/
theorem fixedFamilyPairedPrimeStateDivisorFamily_not_mem_of_prime_gt
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (p : {p // p ∈ P})
    (hpSupport : (support p).Nonempty)
    (hpR : R < (p : ℕ)) :
    fixedFamilyPairedPrimeStateDivisorFamily support A ∉
      smoothDivisorFamilyChoices κ R := by
  intro hz
  obtain ⟨q, hq⟩ := hpSupport
  have hqPair :
      fixedFamilyPairedPrimeStateDivisorFamily support A q ∈
        smoothDivisorPairChoices R :=
    Fintype.mem_piFinset.mp hz q
  have hqSides := Finset.mem_product.mp hqPair
  have hleftLe :
      (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ≤ R :=
    (Finset.mem_Icc.mp hqSides.1).2
  have hrightLe :
      (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 ≤ R :=
    (Finset.mem_Icc.mp hqSides.2).2
  have hpos :=
    fixedFamilyPairedPrimeStateDivisorFamily_pos support A q
  by_cases hstate : A p ⟨q, hq⟩ = 1
  · have hneZero : A p ⟨q, hq⟩ ≠ 0 := by
      intro hzero
      rw [hzero] at hstate
      norm_num at hstate
    have hpDvd :
        (p : ℕ) ∣
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 :=
      (prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff
        support A q p).2 ⟨hq, hneZero⟩
    have hpLe :
        (p : ℕ) ≤
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 :=
      Nat.le_of_dvd hpos.2 hpDvd
    omega
  · have hpDvd :
        (p : ℕ) ∣
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 :=
      (prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff
        support A q p).2 ⟨hq, hstate⟩
    have hpLe :
        (p : ℕ) ≤
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 :=
      Nat.le_of_dvd hpos.1 hpDvd
    omega

/-- Full-space integral of one complete-series support term vanishes as
soon as its active prime set contains a prime above `R`. -/
theorem SmoothSieveCutoff.integral_pairedEnvelope_mul_unrestrictedPrimeSupportTerm_eq_zero_of_prime_gt
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes)
    (p : {p // p ∈ P}) (hpR : R < (p : ℕ)) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (pairedFourierPrimeLocalFactor
              R forms tu.1 tu.2) P
        ∂(volume.prod volume)) = 0 := by
  classical
  rw [show
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (pairedFourierPrimeLocalFactor
              R forms tu.1 tu.2) P) =
        fun tu =>
          ∑ support ∈
              fixedFamilyNonemptyPrimeSupportAssignmentChoices κ P,
            pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              fixedFamilyPrimeSupportEulerTerm
                R forms P tu.1 tu.2 support by
      funext tu
      rw [unrestrictedPrimeSupportTerm_eq_sum_nonemptyAssignments,
        Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro support hsupport
    have hpSupport : (support p).Nonempty :=
      (mem_fixedFamilyNonemptyPrimeSupportAssignmentChoices.mp
        hsupport) p
    calc
      (∫ tu : (κ → ℝ) × (κ → ℝ),
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            fixedFamilyPrimeSupportEulerTerm
              R forms P tu.1 tu.2 support
          ∂(volume.prod volume)) =
          ∫ tu : (κ → ℝ) × (κ → ℝ),
            (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              fixedFamilyPrimeSupportCoefficient
                R tu.1 tu.2 support) *
              fixedFamilyPrimeSupportDensity forms support
            ∂(volume.prod volume) := by
        apply integral_congr_ae
        exact ae_of_all _ fun tu => by
          dsimp only
          rw [fixedFamilyPrimeSupportEulerTerm_eq_coefficient_mul_density
            R forms P tu.1 tu.2 support]
          ring
      _ =
          (∑ A : FixedFamilyPairedPrimeStateAssignment support,
              (smoothDivisorFamilyCoefficient χ.toFun R
                (fixedFamilyPairedPrimeStateDivisorFamily
                  support A) : ℂ)) *
            fixedFamilyPrimeSupportDensity forms support := by
        rw [integral_mul_const,
          integral_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient_eq_sum_states]
      _ = 0 := by
        apply mul_eq_zero_of_left
        apply Finset.sum_eq_zero
        intro A _hA
        exact_mod_cast
          χ.smoothDivisorFamilyCoefficient_eq_zero_of_not_mem
            hR
            (fixedFamilyPairedPrimeStateDivisorFamily support A)
            (fixedFamilyPairedPrimeStateDivisorFamily_pos support A)
            (fixedFamilyPairedPrimeStateDivisorFamily_not_mem_of_prime_gt
              support A p hpSupport hpR)
  · intro support _hsupport
    have h :=
      (integrable_pairedCutoffFourierEnvelope_mul_fixedFamilyPrimeSupportCoefficient
        χ R support).mul_const
          (fixedFamilyPrimeSupportDensity forms support)
    apply h.congr
    exact ae_of_all _ fun tu => by
      dsimp only
      rw [fixedFamilyPrimeSupportEulerTerm_eq_coefficient_mul_density
        R forms P tu.1 tu.2 support]
      ring

/-! ## A summable uniform majorant and `L¹` convergence -/

/-- Frequency-independent majorant for the selected canonical carry local
error.  The positive Fourier shift supplies the summable
`p^(-1-1/log R)` term; rank-two geometry supplies the reciprocal-square
remainder. -/
noncomputable def selectedCFZCanonicalCompletePrimeErrorMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (p : Nat.Primes) : ℝ :=
  (3 * Fintype.card (SelectedCFZFormIndex e) : ℝ) *
      (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹ - 1) +
    (4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e) /
      (p : ℝ) ^ 2

theorem selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (p : Nat.Primes) :
    0 ≤ selectedCFZCanonicalCompletePrimeErrorMajorant e R p := by
  unfold selectedCFZCanonicalCompletePrimeErrorMajorant
  positivity

/-- The uniform local majorant is summable at every fixed radius
`R ≥ 2`. -/
theorem summable_selectedCFZCanonicalCompletePrimeErrorMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Summable
      (selectedCFZCanonicalCompletePrimeErrorMajorant e R) := by
  let exponent : ℝ :=
    -(Real.log (R : ℝ))⁻¹ - 1
  have hlog : 0 < Real.log (R : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hexponent : exponent < -1 := by
    dsimp only [exponent]
    have hinv : 0 < (Real.log (R : ℝ))⁻¹ :=
      inv_pos.mpr hlog
    linarith
  have hfirst :
      Summable (fun p : Nat.Primes =>
        (3 * Fintype.card (SelectedCFZFormIndex e) : ℝ) *
          (p : ℝ) ^ exponent) :=
    (Nat.Primes.summable_rpow.mpr hexponent).mul_left
      (3 * Fintype.card (SelectedCFZFormIndex e) : ℝ)
  have hsquare :
      Summable (fun p : Nat.Primes =>
        (4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e) /
          (p : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      summable_prime_inv_sq.mul_left
        ((4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e))
  change Summable (fun p : Nat.Primes =>
    (3 * Fintype.card (SelectedCFZFormIndex e) : ℝ) *
        (p : ℝ) ^ exponent +
      (4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e) /
        (p : ℝ) ^ 2)
  exact hfirst.add hsquare

/-- Uniform selected-carry local error bound in the primorial,
reduced-residue regime.  At primes dividing the primorial the error is
exactly zero; all other primes have the direct selected-CFZ good-prime
geometry. -/
theorem norm_selectedCFZCanonicalCarryPrimeLocalFactor_sub_one_le_majorant
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ)
    (p : Nat.Primes) :
    ‖cfzCanonicalCarryPairedFourierPrimeLocalFactor
          N (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          carry t u p - 1‖ ≤
      selectedCFZCanonicalCompletePrimeErrorMajorant e R p := by
  by_cases hpW : (p : ℕ) ∣ primorial w
  · have hlocal :
        cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            carry t u p = 1 := by
      let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
      unfold cfzCanonicalCarryPairedFourierPrimeLocalFactor
        pairedFourierPrimeLocalFactor
        cfzCarryAdjustedFamilyAtVector
        pairedFourierLocalFactor
      exact
        complexWeightedLocalFactor_cfzCarryAdjusted_eq_one_of_dvd
          N (primorial w) b p.prop hpW hwb
          (fun q : SelectedCFZFormIndex e => q.1) carry
          (fun q =>
            pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q))
    rw [hlocal, sub_self, norm_zero]
    exact
      selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R p
  · have hlarge :
      exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) <
          (p : ℕ) :=
      SmoothSieveCutoff.selectedCFZ_exceptionalPrime_covered_by_primorial
        hbound p.prop hpW
    have hnonzero :
        AffineNonzeroGoodPrime (p : ℕ)
          (cfzCarryAdjustedFamilyAtVector
            N (primorial w) b
            (fun q : SelectedCFZFormIndex e => q.1) carry) := by
      exact
        affineNonzeroGoodPrime_cfzCarryAdjusted
          N (primorial w) b
          (fun q : SelectedCFZFormIndex e => q.1) carry
          (selectedCFZAffineNonzeroGoodPrime
            hk p.prop hlarge e)
          hpW
    have hrank :
        AffineRankTwoGoodPrime (p : ℕ)
          (cfzCarryAdjustedFamilyAtVector
            N (primorial w) b
            (fun q : SelectedCFZFormIndex e => q.1) carry) := by
      exact
        affineRankTwoGoodPrime_cfzCarryAdjusted
          N (primorial w) b
          (fun q : SelectedCFZFormIndex e => q.1) carry
          (selectedCFZAffineRankTwoGoodPrime
            hk p.prop hlarge e)
          hpW
    simpa only [
      cfzCanonicalCarryPairedFourierPrimeLocalFactor,
      selectedCFZCanonicalCompletePrimeErrorMajorant] using
      norm_pairedFourierPrimeLocalFactor_sub_one_le_rpow_add_sq_of_goodPrime
        hR t u p hnonzero hrank

/-- Product majorant for one finite active-prime support. -/
noncomputable def selectedCFZCanonicalCompleteSupportMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (S : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ S,
    selectedCFZCanonicalCompletePrimeErrorMajorant e R p

theorem selectedCFZCanonicalCompleteSupportMajorant_nonneg
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (S : Finset Nat.Primes) :
    0 ≤ selectedCFZCanonicalCompleteSupportMajorant e R S := by
  unfold selectedCFZCanonicalCompleteSupportMajorant
  exact Finset.prod_nonneg fun p _hp =>
    selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R p

/-- The support majorants are summable over all finite prime sets. -/
theorem summable_selectedCFZCanonicalCompleteSupportMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Summable
      (selectedCFZCanonicalCompleteSupportMajorant e R) := by
  change Summable (fun S : Finset Nat.Primes =>
    ∏ p ∈ S,
      selectedCFZCanonicalCompletePrimeErrorMajorant e R p)
  exact
    summable_finsetProd_of_summable_nonneg
      (selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R)
      (summable_selectedCFZCanonicalCompletePrimeErrorMajorant e hR)

/-- Pointwise domination of one unrestricted support term by the
frequency-independent support majorant. -/
theorem norm_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm_le
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ)
    (S : Finset Nat.Primes) :
    ‖unrestrictedPrimeSupportTerm
        (cfzCanonicalCarryPairedFourierPrimeLocalFactor
          N (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          carry t u) S‖ ≤
      selectedCFZCanonicalCompleteSupportMajorant e R S := by
  classical
  unfold unrestrictedPrimeSupportTerm
    selectedCFZCanonicalCompleteSupportMajorant
  rw [norm_prod]
  apply Finset.prod_le_prod
  · intro p _hp
    exact norm_nonneg _
  · intro p _hp
    exact
      norm_selectedCFZCanonicalCarryPrimeLocalFactor_sub_one_le_majorant
        (N := N) hk hbound hwb e carry hR t u p

/-- The paired Schwartz envelope times one complete support term is
dominated by a scalar support majorant times the universal absolute
Fourier density. -/
theorem SmoothSieveCutoff.norm_selectedCFZCanonicalCarryCompleteSupportIntegrand_le
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (S : Finset Nat.Primes)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            carry tu.1 tu.2) S‖ ≤
      selectedCFZCanonicalCompleteSupportMajorant e R S *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  rw [norm_mul, norm_pairedCutoffFourierEnvelope]
  calc
    (χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
          χ.fourierProductMomentDensity (fun _ => 0) tu.2) *
        ‖unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            carry tu.1 tu.2) S‖ =
        ‖unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            carry tu.1 tu.2) S‖ *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
      rw [mul_comm]
      rfl
    _ ≤
        selectedCFZCanonicalCompleteSupportMajorant e R S *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu :=
      mul_le_mul_of_nonneg_right
        (norm_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm_le
          (N := N) hk hbound hwb e carry hR tu.1 tu.2 S)
        (χ.selectedCFZPairedFourierAbsoluteDensity_nonneg e tu)

/-- `L¹` summability of the complete support series for one selected
canonical carry vector.  This is the precise Fubini/Tonelli input needed
for the complete Euler integrand. -/
theorem SmoothSieveCutoff.summable_integral_norm_selectedCFZCanonicalCarryCompleteSupportIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R) :
    Summable (fun S : Finset Nat.Primes =>
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry tu.1 tu.2) S‖
        ∂(volume.prod volume)) := by
  let A : ℝ :=
    ∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      χ.selectedCFZPairedFourierAbsoluteDensity e tu
      ∂(volume.prod volume)
  have hmajorant :
      Summable (fun S : Finset Nat.Primes =>
        selectedCFZCanonicalCompleteSupportMajorant e R S * A) :=
    (summable_selectedCFZCanonicalCompleteSupportMajorant
      e hR).mul_right A
  apply hmajorant.of_nonneg_of_le
  · intro S
    exact integral_nonneg fun _tu => norm_nonneg _
  · intro S
    have hterm :
        Integrable
          (fun tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ) =>
            pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              unrestrictedPrimeSupportTerm
                (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2) S)
          (volume.prod volume) := by
      change Integrable
        (fun tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ) =>
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            unrestrictedPrimeSupportTerm
              (pairedFourierPrimeLocalFactor R
                (cfzCarryAdjustedFamilyAtVector
                  N (primorial w) b
                  (fun q : SelectedCFZFormIndex e => q.1) carry)
                tu.1 tu.2) S)
        (volume.prod volume)
      exact
        χ.integrable_pairedEnvelope_mul_unrestrictedPrimeSupportTerm
          R
          (cfzCarryAdjustedFamilyAtVector
            N (primorial w) b
            (fun q : SelectedCFZFormIndex e => q.1) carry)
          S
    have hboundIntegrable :
        Integrable
          (fun tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ) =>
            selectedCFZCanonicalCompleteSupportMajorant e R S *
              χ.selectedCFZPairedFourierAbsoluteDensity e tu)
          (volume.prod volume) :=
      (χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
        (selectedCFZCanonicalCompleteSupportMajorant e R S)
    have hle :=
      integral_mono hterm.norm hboundIntegrable fun tu =>
        χ.norm_selectedCFZCanonicalCarryCompleteSupportIntegrand_le
          (N := N) hk hbound hwb e carry hR S tu
    simpa only [A, integral_const_mul] using hle

/-! ## The completion tail as one absolutely convergent series -/

/-- At every fixed frequency, the complete support series for a selected
canonical carry is absolutely convergent.  This packages the coefficient
geometry established at the start of the file into the generic unrestricted
support summability theorem. -/
theorem summable_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ) :
    Summable (fun S : Finset Nat.Primes =>
      unrestrictedPrimeSupportTerm
        (cfzCanonicalCarryPairedFourierPrimeLocalFactor
          N (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          carry t u) S) := by
  exact
    summable_unrestrictedPrimeSupportTerm
      (summable_norm_cfzCanonicalCarryPairedFourierPrimeLocalFactor_sub_one
        N (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1)
        carry t u
        (selectedCFZCarryAdjustedFamilyAtVector_nonzero hk e carry)
        (selectedCFZCarryAdjustedFamilyAtVector_pairwiseIndependent
          hk e carry)
        hR)

/-- The countable index set for the missing completion tail: a canonical
carry cell together with a finite prime support which is not contained in
the finite Euler set `p ≤ R`. -/
def SelectedCFZCanonicalCarryEulerCompletionTailIndex
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) : Type :=
  {carry : SelectedCFZFormIndex e → ℤ //
      carry ∈ cfzCanonicalCarryVectorChoices
        (SelectedCFZFormIndex e) k} ×
    ↥
      ((↑((primesLEAsPrimes R).powerset) :
        Set (Finset Nat.Primes))ᶜ)

/-- One signed term of the full completion tail.  The minus sign records
`finite Euler series - complete Euler series`. -/
noncomputable def SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (R : ℕ)
    (idx : SelectedCFZCanonicalCarryEulerCompletionTailIndex e R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℂ :=
  -((cfzCanonicalCarryCellDensity
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
        idx.1.1 : ℂ) *
      (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            idx.1.1 tu.1 tu.2) idx.2.1))

/-- The signed completion tail is absolutely summable at each Fourier
frequency. -/
theorem SmoothSieveCutoff.summable_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    Summable (fun idx :
        SelectedCFZCanonicalCarryEulerCompletionTailIndex e R =>
      χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
        (N := N) (w := w) (b := b) e R idx tu) := by
  classical
  apply Summable.of_norm
  change Summable (fun idx :
      {carry : SelectedCFZFormIndex e → ℤ //
          carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k} ×
        ↥
          ((↑((primesLEAsPrimes R).powerset) :
            Set (Finset Nat.Primes))ᶜ) =>
    ‖χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
      (N := N) (w := w) (b := b) e R idx tu‖)
  rw [summable_prod_of_nonneg fun _idx => norm_nonneg _]
  constructor
  · intro carry
    have hsupport :
        Summable (fun S : Finset Nat.Primes =>
          ‖unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry.1 tu.1 tu.2) S‖) :=
      summable_norm_iff.mpr
        (summable_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm
        (N := N) (w := w) (b := b)
        hk e carry.1 hR tu.1 tu.2)
    have hsub :
        Summable (fun S :
            ↥
              ((↑((primesLEAsPrimes R).powerset) :
                Set (Finset Nat.Primes))ᶜ) =>
          ‖unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry.1 tu.1 tu.2) S.1‖) :=
      hsupport.comp_injective Subtype.val_injective
    have hscaled :=
      hsub.mul_left
        ‖(cfzCanonicalCarryCellDensity
              (N := N)
              (fun q : SelectedCFZFormIndex e => q.1)
              carry.1 : ℂ) *
            pairedCutoffFourierEnvelope χ tu.1 tu.2‖
    convert hscaled using 1
    · rfl
    · funext S
      simp only [
        SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand,
        norm_neg, norm_mul, mul_assoc]
  · exact Summable.of_finite

/-- Each signed tail term is integrable. -/
theorem SmoothSieveCutoff.integrable_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (R : ℕ)
    (idx : SelectedCFZCanonicalCarryEulerCompletionTailIndex e R) :
    Integrable
      (χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
        (N := N) (w := w) (b := b) e R idx)
      (volume.prod volume) := by
  have hbase :
      Integrable
        (fun tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ) =>
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            unrestrictedPrimeSupportTerm
              (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                N (primorial w) b R
                (fun q : SelectedCFZFormIndex e => q.1)
                idx.1.1 tu.1 tu.2) idx.2.1)
        (volume.prod volume) := by
    change Integrable
      (fun tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (pairedFourierPrimeLocalFactor R
              (cfzCarryAdjustedFamilyAtVector
                N (primorial w) b
                (fun q : SelectedCFZFormIndex e => q.1)
                idx.1.1)
              tu.1 tu.2) idx.2.1)
      (volume.prod volume)
    exact
      χ.integrable_pairedEnvelope_mul_unrestrictedPrimeSupportTerm
        R
        (cfzCarryAdjustedFamilyAtVector
          N (primorial w) b
          (fun q : SelectedCFZFormIndex e => q.1)
          idx.1.1)
        idx.2.1
  exact
    (hbase.const_mul
      (cfzCanonicalCarryCellDensity
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
        idx.1.1 : ℂ)).neg

/-- The `L¹` norms of all signed tail terms are summable. -/
theorem SmoothSieveCutoff.summable_integral_norm_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Summable (fun idx :
        SelectedCFZCanonicalCarryEulerCompletionTailIndex e R =>
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        ‖χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
          (N := N) (w := w) (b := b) e R idx tu‖
        ∂(volume.prod volume)) := by
  classical
  let TailIndex : Type :=
    {carry : SelectedCFZFormIndex e → ℤ //
        carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k} ×
      ↥
        ((↑((primesLEAsPrimes R).powerset) :
          Set (Finset Nat.Primes))ᶜ)
  let toTailIndex :
      TailIndex → SelectedCFZCanonicalCarryEulerCompletionTailIndex e R :=
    fun idx => idx
  let F : TailIndex → ℝ := fun idx =>
    ∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      ‖χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
        (N := N) (w := w) (b := b) e R (toTailIndex idx) tu‖
      ∂(volume.prod volume)
  have hF : Summable F := by
    apply (summable_prod_of_nonneg (f := F) fun _idx =>
      integral_nonneg fun _tu => norm_nonneg _).2
    constructor
    · intro carry
      dsimp only [F, toTailIndex]
      have hall :=
        χ.summable_integral_norm_selectedCFZCanonicalCarryCompleteSupportIntegrand
          (N := N) hk hbound hwb e carry.1 hR
      have hbase :
          Summable (fun S :
              ↥
                ((↑((primesLEAsPrimes R).powerset) :
                  Set (Finset Nat.Primes))ᶜ) =>
            ∫ tu :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ),
              ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                unrestrictedPrimeSupportTerm
                  (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry.1 tu.1 tu.2) S.1‖
              ∂(volume.prod volume)) :=
        hall.comp_injective Subtype.val_injective
      have hscaled :=
        hbase.mul_left
          ‖(cfzCanonicalCarryCellDensity
            (N := N)
            (fun q : SelectedCFZFormIndex e => q.1)
            carry.1 : ℂ)‖
      convert hscaled using 1
      · rfl
      · funext S
        simp only [
          SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand,
          norm_neg, norm_mul, integral_const_mul]
    · exact Summable.of_finite
  simpa only [F, TailIndex, toTailIndex,
    SelectedCFZCanonicalCarryEulerCompletionTailIndex] using hF

/-- For one canonical carry, subtracting the complete support series from
the finite Euler series is exactly the signed series over supports missing
from the finite powerset. -/
theorem SmoothSieveCutoff.pairedEnvelope_mul_selectedCFZCanonicalCarry_finite_sub_complete_eq_tail
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ) :
    pairedCutoffFourierEnvelope χ t u *
          (∑ S ∈ (primesLEAsPrimes R).powerset,
            unrestrictedPrimeSupportTerm
              (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                N (primorial w) b R
                (fun q : SelectedCFZFormIndex e => q.1)
                carry t u) S) -
        pairedCutoffFourierEnvelope χ t u *
          cfzCanonicalCarryCompletePrimeSupportSeries
            N (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            carry t u =
      ∑' S :
          ↥
            ((↑((primesLEAsPrimes R).powerset) :
              Set (Finset Nat.Primes))ᶜ),
        -(pairedCutoffFourierEnvelope χ t u *
          unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry t u) S.1) := by
  have hsupport :=
    summable_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm
      (N := N) (w := w) (b := b)
      hk e carry hR t u
  have hsplit :=
    hsupport.sum_add_tsum_compl
      (s := (primesLEAsPrimes R).powerset)
  unfold cfzCanonicalCarryCompletePrimeSupportSeries
  rw [← hsplit]
  simp only [tsum_neg, tsum_mul_left]
  ring

/-- The complete canonical Euler discrepancy is pointwise the single
signed tail series indexed above. -/
theorem SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy_eq_tsum_tail
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu =
      ∑' idx :
          SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
        χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
          (N := N) (w := w) (b := b) e R idx tu := by
  classical
  have htail :=
    χ.summable_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
      (N := N) (w := w) (b := b) hk e hR tu
  unfold SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy
    SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    cfzCanonicalCarryUnrestrictedFourierAverage
    cfzCanonicalCarryCompleteFourierAverage
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc
    ∑ carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
        (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              ((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
                ∑ S ∈ (primesLEAsPrimes R).powerset,
                  unrestrictedPrimeSupportTerm
                    (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                      N (primorial w) b R
                      (fun q : SelectedCFZFormIndex e => q.1)
                      carry tu.1 tu.2) S) -
            pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              ((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
                cfzCanonicalCarryCompletePrimeSupportSeries
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2)) =
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          ∑' S :
              ↥((↑((primesLEAsPrimes R).powerset) :
                Set (Finset Nat.Primes))ᶜ),
            -((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                unrestrictedPrimeSupportTerm
                  (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) S.1)) := by
      apply Finset.sum_congr rfl
      intro carry hcarry
      have hcompletion :=
        χ.pairedEnvelope_mul_selectedCFZCanonicalCarry_finite_sub_complete_eq_tail
          (N := N) (w := w) (b := b)
          hk e carry hR tu.1 tu.2
      rw [show
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                ((cfzCanonicalCarryCellDensity
                    (N := N)
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry : ℂ) *
                  ∑ S ∈ (primesLEAsPrimes R).powerset,
                    unrestrictedPrimeSupportTerm
                      (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                        N (primorial w) b R
                        (fun q : SelectedCFZFormIndex e => q.1)
                        carry tu.1 tu.2) S) -
              pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                ((cfzCanonicalCarryCellDensity
                    (N := N)
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry : ℂ) *
                  cfzCanonicalCarryCompletePrimeSupportSeries
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) =
            (cfzCanonicalCarryCellDensity
                (N := N)
                (fun q : SelectedCFZFormIndex e => q.1)
                carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                    (∑ S ∈ (primesLEAsPrimes R).powerset,
                      unrestrictedPrimeSupportTerm
                        (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                          N (primorial w) b R
                          (fun q : SelectedCFZFormIndex e => q.1)
                          carry tu.1 tu.2) S) -
                pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                  cfzCanonicalCarryCompletePrimeSupportSeries
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) by ring,
        hcompletion]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro S
      ring
    _ = _ := by
      unfold
        SelectedCFZCanonicalCarryEulerCompletionTailIndex at htail ⊢
      rw [htail.tsum_prod]
      unfold
        SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
      let F : (SelectedCFZFormIndex e → ℤ) → ℂ :=
        fun carry =>
          ∑' S :
              ↥((↑((primesLEAsPrimes R).powerset) :
                Set (Finset Nat.Primes))ᶜ),
            -((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                unrestrictedPrimeSupportTerm
                  (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) S.1))
      change
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
              (SelectedCFZFormIndex e) k,
            F carry =
          ∑' carry :
              ↥(cfzCanonicalCarryVectorChoices
                (SelectedCFZFormIndex e) k),
            F carry.1
      exact
        (Finset.tsum_subtype
          (cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k) F).symm

/-- Every term of the completion tail has zero full-space integral.  A
support outside the finite powerset contains a prime `p > R`, and that
prime forces one divisor coordinate beyond the smooth cutoff. -/
theorem SmoothSieveCutoff.integral_selectedCFZCanonicalCarryEulerCompletionTailIntegrand_eq_zero
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (idx : SelectedCFZCanonicalCarryEulerCompletionTailIndex e R) :
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
        (N := N) (w := w) (b := b) e R idx tu
      ∂(volume.prod volume)) = 0 := by
  classical
  have hnotMem :
      idx.2.1 ∉ (primesLEAsPrimes R).powerset := by
    simpa only [Set.mem_compl_iff, Finset.mem_coe] using idx.2.2
  have hnotSubset :
      ¬idx.2.1 ⊆ primesLEAsPrimes R := by
    intro hsubset
    exact hnotMem (Finset.mem_powerset.mpr hsubset)
  obtain ⟨p, hpSupport, hpNotSmall⟩ :=
    Finset.not_subset.mp hnotSubset
  have hpR : R < (p : ℕ) := by
    apply Nat.lt_of_not_ge
    intro hpLe
    exact hpNotSmall ((mem_primesLEAsPrimes_iff R p).2 hpLe)
  have hbase :
      (∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              idx.1.1 tu.1 tu.2) idx.2.1
        ∂(volume.prod volume)) = 0 := by
    change
      (∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (pairedFourierPrimeLocalFactor R
              (cfzCarryAdjustedFamilyAtVector
                N (primorial w) b
                (fun q : SelectedCFZFormIndex e => q.1)
                idx.1.1)
              tu.1 tu.2) idx.2.1
        ∂(volume.prod volume)) = 0
    exact
      χ.integral_pairedEnvelope_mul_unrestrictedPrimeSupportTerm_eq_zero_of_prime_gt
        (by omega)
        (cfzCarryAdjustedFamilyAtVector
          N (primorial w) b
          (fun q : SelectedCFZFormIndex e => q.1)
          idx.1.1)
        idx.2.1 ⟨p, hpSupport⟩ hpR
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
  rw [integral_neg, integral_const_mul, hbase]
  simp

/-- **Finite-to-complete full-space cancellation.**  The finite canonical
Euler support integral equals its honest complete Euler support integral.
Equivalently, the completion discrepancy has zero full-space integral. -/
theorem SmoothSieveCutoff.integral_cfzCanonicalCarryEulerCompletionDiscrepancy_eq_zero
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu
      ∂(volume.prod volume)) = 0 := by
  classical
  let :
      Countable
        (SelectedCFZCanonicalCarryEulerCompletionTailIndex e R) := by
    unfold SelectedCFZCanonicalCarryEulerCompletionTailIndex
    infer_instance
  have hterm :
      ∀ idx :
          SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
        Integrable
          (χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
            (N := N) (w := w) (b := b) e R idx)
          (volume.prod volume) :=
    fun idx =>
      χ.integrable_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
        (N := N) (w := w) (b := b) e R idx
  have hnorm :=
    χ.summable_integral_norm_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
      (N := N) hk hbound hwb e hR
  calc
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu
      ∂(volume.prod volume)) =
        ∫ tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ),
          ∑' idx :
              SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
            χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
              (N := N) (w := w) (b := b) e R idx tu
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact ae_of_all _ fun tu =>
        χ.cfzCanonicalCarryEulerCompletionDiscrepancy_eq_tsum_tail
          (N := N) (w := w) (b := b) hk e hR tu
    _ =
        ∑' idx :
            SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
              (N := N) (w := w) (b := b) e R idx tu
            ∂(volume.prod volume) :=
      (integral_tsum_of_summable_integral_norm hterm hnorm).symm
    _ = 0 := by
      have hz
          (idx :
            SelectedCFZCanonicalCarryEulerCompletionTailIndex e R) :
          (∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
              (N := N) (w := w) (b := b) e R idx tu
            ∂(volume.prod volume)) = 0 :=
        χ.integral_selectedCFZCanonicalCarryEulerCompletionTailIntegrand_eq_zero
          (N := N) (w := w) (b := b) e hR idx
      simp only [hz, tsum_zero]

/-! ## Exact remaining interface for diagonal growing-box decay -/

/-- Total mass of the frequency-independent complete-support majorant. -/
noncomputable def selectedCFZCanonicalCompleteSupportMass
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) : ℝ :=
  ∑' S : Finset Nat.Primes,
    selectedCFZCanonicalCompleteSupportMajorant e R S

theorem selectedCFZCanonicalCompleteSupportMass_nonneg
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) :
    0 ≤ selectedCFZCanonicalCompleteSupportMass e R := by
  unfold selectedCFZCanonicalCompleteSupportMass
  exact tsum_nonneg fun S =>
    selectedCFZCanonicalCompleteSupportMajorant_nonneg e R S

/-- The complete-support majorant is itself the honest Euler product of
the nonnegative local majorants. -/
theorem selectedCFZCanonicalCompleteSupportMass_eq_tprod
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalCompleteSupportMass e R =
      ∏' p : Nat.Primes,
        (1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p) := by
  unfold selectedCFZCanonicalCompleteSupportMass
    selectedCFZCanonicalCompleteSupportMajorant
  exact
    (tprod_one_add
      (summable_selectedCFZCanonicalCompleteSupportMajorant
        e hR)).symm

/-- The exact arithmetic mass which occurs in the missing completion
tail, before multiplication by the paired Schwartz density. -/
noncomputable def selectedCFZCanonicalEulerCompletionTailMajorantMass
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) : ℝ :=
  ∑' S :
      ↥((↑((primesLEAsPrimes R).powerset) :
        Set (Finset Nat.Primes))ᶜ),
    selectedCFZCanonicalCompleteSupportMajorant e R S.1

theorem summable_selectedCFZCanonicalEulerCompletionTailMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Summable (fun S :
        ↥((↑((primesLEAsPrimes R).powerset) :
          Set (Finset Nat.Primes))ᶜ) =>
      selectedCFZCanonicalCompleteSupportMajorant e R S.1) :=
  (summable_selectedCFZCanonicalCompleteSupportMajorant e hR).subtype _

theorem selectedCFZCanonicalEulerCompletionTailMajorantMass_nonneg
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) :
    0 ≤ selectedCFZCanonicalEulerCompletionTailMajorantMass e R := by
  unfold selectedCFZCanonicalEulerCompletionTailMajorantMass
  exact tsum_nonneg fun S =>
    selectedCFZCanonicalCompleteSupportMajorant_nonneg e R S.1

theorem selectedCFZCanonicalEulerCompletionTailMajorantMass_le_complete
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalEulerCompletionTailMajorantMass e R ≤
      selectedCFZCanonicalCompleteSupportMass e R := by
  have hsum :=
    summable_selectedCFZCanonicalCompleteSupportMajorant e hR
  have hsplit :=
    hsum.sum_add_tsum_compl
      (s := (primesLEAsPrimes R).powerset)
  unfold selectedCFZCanonicalEulerCompletionTailMajorantMass
    selectedCFZCanonicalCompleteSupportMass
  rw [← hsplit]
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun S _hS =>
      selectedCFZCanonicalCompleteSupportMajorant_nonneg e R S)

/-- The precise unproved analytic input needed to upgrade full-space
cancellation to the Selberg-scaled diagonal growing-box limit.  It asks
only for polylogarithmic growth of the genuinely missing infinite support
tail.  The local formula above shows that its new ingredient is a uniform
shifted-prime-zeta estimate for
`p^(-1-1/log R)`; the existing finite Rankin Euler bounds do not supply
that estimate. -/
def HasSelectedCFZCanonicalEulerCompletionTailPolylogBound
    {k : ℕ} (e : LinearFormsExponent k) : Prop :=
  ∃ E : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ R : ℕ in atTop,
      selectedCFZCanonicalEulerCompletionTailMajorantMass e R ≤
        C * (1 + Real.log R) ^ E

end Wikipedia.SzemeredisTheorem
