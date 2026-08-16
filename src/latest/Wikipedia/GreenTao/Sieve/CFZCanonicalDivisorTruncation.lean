import Wikipedia.GreenTao.Sieve.CFZCanonicalDivisorExpansion

/-!
# Canonical divisor truncation bounds

This file closes the purely infinite-series part of the canonical
fixed-carry expansion and isolates the genuinely coordinatewise part.

For a fixed prime-local factor with summable local errors, the sums over
subsets of the primes at most `X` converge to the full unrestricted
prime-support series.  This applies in particular to every fixed
carry-adjusted affine family satisfying the usual coefficient hypotheses.

The remaining divisor-cutoff discrepancy is bounded fiberwise by an
explicit finite quantity: the number of coordinatewise-admissible
squarefree divisor families in the support fiber, plus the unrestricted
primewise coefficient majorant.  Thus no infinite-series truncation remains
hidden in that discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-! ## Exhaustion of natural primes -/

theorem mem_primesLEAsPrimes_iff
    (R : ℕ) (p : Nat.Primes) :
    p ∈ primesLEAsPrimes R ↔ (p : ℕ) ≤ R := by
  classical
  constructor
  · exact le_of_mem_primesLEAsPrimes
  · intro hp
    have hpMem : (p : ℕ) ∈ Nat.primesLE R :=
      Nat.mem_primesLE.mpr ⟨hp, p.prop⟩
    unfold primesLEAsPrimes
    apply Finset.mem_map.mpr
    let q : (Nat.primesLE R : Finset ℕ) := ⟨p, hpMem⟩
    refine ⟨q, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

theorem monotone_primesLEAsPrimes :
    Monotone primesLEAsPrimes := by
  intro R X hRX p hp
  rw [mem_primesLEAsPrimes_iff] at hp ⊢
  exact hp.trans hRX

/-- The finite sets of natural primes at most `X` exhaust `Nat.Primes`. -/
theorem tendsto_primesLEAsPrimes_atTop :
    Tendsto primesLEAsPrimes atTop atTop := by
  apply monotone_primesLEAsPrimes.tendsto_atTop_finset
  intro p
  exact ⟨p, (mem_primesLEAsPrimes_iff (p : ℕ) p).2 le_rfl⟩

/-! ## Finite powersets converge to the unrestricted support series -/

/-- Absolute summability upgrades the finite powerset identity to an
honest limit over the natural-prime cutoff. -/
theorem tendsto_sum_unrestrictedPrimeSupportTerm_primesLE
    {localFactor : Nat.Primes → ℂ}
    (hlocal :
      Summable (fun p : Nat.Primes => ‖localFactor p - 1‖)) :
    Tendsto
      (fun X : ℕ =>
        ∑ S ∈ (primesLEAsPrimes X).powerset,
          unrestrictedPrimeSupportTerm localFactor S)
      atTop
      (𝓝 (∑' S : Finset Nat.Primes,
        unrestrictedPrimeSupportTerm localFactor S)) := by
  exact
    (summable_unrestrictedPrimeSupportTerm hlocal).hasSum.comp
      (tendsto_finset_powerset_atTop_atTop.comp
        tendsto_primesLEAsPrimes_atTop)

/-- Norm form of the preceding bridge. -/
theorem tendsto_norm_sum_unrestrictedPrimeSupportTerm_primesLE_sub_tsum
    {localFactor : Nat.Primes → ℂ}
    (hlocal :
      Summable (fun p : Nat.Primes => ‖localFactor p - 1‖)) :
    Tendsto
      (fun X : ℕ =>
        ‖(∑ S ∈ (primesLEAsPrimes X).powerset,
            unrestrictedPrimeSupportTerm localFactor S) -
          ∑' S : Finset Nat.Primes,
            unrestrictedPrimeSupportTerm localFactor S‖)
      atTop (𝓝 0) := by
  have hsub :
      Tendsto
        (fun X : ℕ =>
          (∑ S ∈ (primesLEAsPrimes X).powerset,
              unrestrictedPrimeSupportTerm localFactor S) -
            ∑' S : Finset Nat.Primes,
              unrestrictedPrimeSupportTerm localFactor S)
        atTop (𝓝 0) := by
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∑' S : Finset Nat.Primes,
              unrestrictedPrimeSupportTerm localFactor S)
          atTop
          (𝓝 (∑' S : Finset Nat.Primes,
            unrestrictedPrimeSupportTerm localFactor S)) :=
      tendsto_const_nhds
    simpa only [sub_self] using
      (tendsto_sum_unrestrictedPrimeSupportTerm_primesLE hlocal).sub
        hconst
  simpa using hsub.norm

/-! ## Fixed canonical carry families -/

theorem
    summable_norm_cfzCanonicalCarryPairedFourierPrimeLocalFactor_sub_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ)
    (hnonzero :
      NonzeroCoefficientVectors
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hindependent :
      PairwiseIndependentCoefficients
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hR : 2 ≤ R) :
    Summable (fun p : Nat.Primes =>
      ‖cfzCanonicalCarryPairedFourierPrimeLocalFactor
          N W b R forms carry t u p - 1‖) := by
  simpa only [cfzCanonicalCarryPairedFourierPrimeLocalFactor] using
    summable_norm_pairedFourierPrimeLocalFactor_sub_one
      hnonzero hindependent hR t u

/-- For fixed Selberg radius and fixed carry-adjusted family, the finite
prime-support powersets converge to the full absolutely convergent support
series.  The exhaustion parameter `X` is intentionally separate from the
fixed Fourier radius `R`. -/
theorem
    tendsto_cfzCanonicalCarry_unrestrictedPrimeSupport_powerset
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ)
    (hnonzero :
      NonzeroCoefficientVectors
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hindependent :
      PairwiseIndependentCoefficients
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hR : 2 ≤ R) :
    Tendsto
      (fun X : ℕ =>
        ∑ S ∈ (primesLEAsPrimes X).powerset,
          unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N W b R forms carry t u) S)
      atTop
      (𝓝 (∑' S : Finset Nat.Primes,
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N W b R forms carry t u) S)) := by
  exact
    tendsto_sum_unrestrictedPrimeSupportTerm_primesLE
      (summable_norm_cfzCanonicalCarryPairedFourierPrimeLocalFactor_sub_one
        N W b R forms carry t u hnonzero hindependent hR)

/-- The full fixed-carry support series is the already identified paired
Fourier Euler product. -/
theorem tsum_cfzCanonicalCarry_unrestrictedPrimeSupport_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (hnonzero :
      NonzeroCoefficientVectors
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hindependent :
      PairwiseIndependentCoefficients
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    {R : ℕ} (hR : 2 ≤ R) (t u : κ → ℝ) :
    (∑' S : Finset Nat.Primes,
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N W b R forms carry t u) S) =
      (cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R
            (cfzCarryAdjustedFamilyAtVector N W b forms carry)
            t u p := by
  change
    (∑' S : Finset Nat.Primes,
        unrestrictedPrimeSupportTerm
          (pairedFourierPrimeLocalFactor R
            (cfzCarryAdjustedFamilyAtVector N W b forms carry)
            t u) S) = _
  simpa only [unrestrictedPairedFourierPrimeSupportTerm] using
    tsum_unrestrictedPairedFourierPrimeSupportTerm_eq
      hnonzero hindependent hR t u

/-- Combined finite-to-full Euler bridge for one fixed canonical carry
family. -/
theorem
    tendsto_cfzCanonicalCarry_unrestrictedPrimeSupport_powerset_to_euler
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ)
    (hnonzero :
      NonzeroCoefficientVectors
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hindependent :
      PairwiseIndependentCoefficients
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hR : 2 ≤ R) :
    Tendsto
      (fun X : ℕ =>
        ∑ S ∈ (primesLEAsPrimes X).powerset,
          unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N W b R forms carry t u) S)
      atTop
      (𝓝
        ((cutoffZetaSingularFactor R t u *
            cutoffZetaSystemFactor R t u) *
          ∏' p : Nat.Primes,
            primePairedFourierArithmeticToZetaLocalRatio
              R
              (cfzCarryAdjustedFamilyAtVector
                N W b forms carry)
              t u p)) := by
  rw [← tsum_cfzCanonicalCarry_unrestrictedPrimeSupport_eq
    N W b forms carry hnonzero hindependent hR t u]
  exact
    tendsto_cfzCanonicalCarry_unrestrictedPrimeSupport_powerset
      N W b R forms carry t u hnonzero hindependent hR

/-! ## Coordinatewise support-fiber bounds -/

/-- The squarefree divisor families in one exact coordinatewise support
fiber. -/
noncomputable def coordinatewiseTruncatedSupportFiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    Finset (κ → ℕ × ℕ) :=
  (SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R).filter
    (fun z =>
      fixedFamilyPrimeSupportAssignmentOf P z = support)

theorem mem_coordinatewiseTruncatedSupportFiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {P : Finset Nat.Primes}
    {support : FixedFamilyPrimeSupportAssignment κ P}
    {z : κ → ℕ × ℕ} :
    z ∈ coordinatewiseTruncatedSupportFiber R P support ↔
      z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R ∧
        fixedFamilyPrimeSupportAssignmentOf P z = support := by
  classical
  simp [coordinatewiseTruncatedSupportFiber]

/-- A support fiber is no larger than the complete coordinatewise divisor
box. -/
theorem card_coordinatewiseTruncatedSupportFiber_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) (P : Finset Nat.Primes)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    (coordinatewiseTruncatedSupportFiber R P support).card ≤
      R ^ (2 * Fintype.card κ) := by
  classical
  calc
    (coordinatewiseTruncatedSupportFiber R P support).card ≤
        (SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices
          κ R).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (smoothDivisorFamilyChoices κ R).card := by
      unfold SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = R ^ (2 * Fintype.card κ) :=
      card_smoothDivisorFamilyChoices κ R

theorem coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    coordinatewiseTruncatedSupportCoefficient
        χ R P t u support =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        χ.transformedPairedDivisorFamily R z (t, u) := by
  classical
  rfl

/-- The norm of the common Fourier envelope is exactly the zero-th paired
Fourier moment density. -/
theorem norm_pairedCutoffFourierEnvelope
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (t u : κ → ℝ) :
    ‖pairedCutoffFourierEnvelope χ t u‖ =
      χ.fourierProductMomentDensity (fun _ => 0) t *
        χ.fourierProductMomentDensity (fun _ => 0) u := by
  classical
  simp [pairedCutoffFourierEnvelope,
    SmoothSieveCutoff.fourierProductMomentDensity,
    SmoothSieveCutoff.fourierMomentDensity]

/-- The coordinatewise coefficient in one support fiber is controlled by
the fiber cardinality times the common Fourier envelope. -/
theorem norm_coordinatewiseTruncatedSupportCoefficient_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖coordinatewiseTruncatedSupportCoefficient
        χ R P t u support‖ ≤
      ((coordinatewiseTruncatedSupportFiber R P support).card : ℝ) *
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
    _ ≤
        ∑ _z ∈ coordinatewiseTruncatedSupportFiber R P support,
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u) := by
      apply Finset.sum_le_sum
      intro z hz
      have hzSquarefree :
          SquarefreePairedDivisorChoice z :=
        (SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp
          ((mem_coordinatewiseTruncatedSupportFiber.mp hz).1)).2
      calc
        ‖χ.transformedPairedDivisorFamily R z (t, u)‖ ≤
            SmoothSieveCutoff.pairedDivisorMoebiusMass z *
              (χ.fourierProductMomentDensity (fun _ => 0) t *
                χ.fourierProductMomentDensity (fun _ => 0) u) :=
          χ.norm_transformedPairedDivisorFamily_le R z (t, u)
        _ =
            χ.fourierProductMomentDensity (fun _ => 0) t *
              χ.fourierProductMomentDensity (fun _ => 0) u := by
          rw [
            SmoothSieveCutoff.pairedDivisorMoebiusMass_eq_one_of_squarefree
              hzSquarefree,
            one_mul]
    _ = _ := by
      simp

/-- Product majorant for the unrestricted coefficient in one prime-support
fiber. -/
noncomputable def fixedFamilyPrimeSupportThreeMajorant
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) : ℝ :=
  ∏ p : {p // p ∈ P}, (3 : ℝ) ^ (support p).card

/-- The unrestricted primewise coefficient has the expected `3`-per-active
form bound. -/
theorem norm_fixedFamilyPrimeSupportCoefficient_le_threeMajorant
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} (hR : 2 ≤ R) (t u : κ → ℝ)
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖fixedFamilyPrimeSupportCoefficient R t u support‖ ≤
      fixedFamilyPrimeSupportThreeMajorant support := by
  classical
  unfold fixedFamilyPrimeSupportCoefficient
    fixedFamilyPrimeLocalCoefficient
    fixedFamilyPrimeSupportThreeMajorant
  rw [norm_prod]
  apply Finset.prod_le_prod
  · intro p _hp
    positivity
  · intro p _hp
    rw [norm_mul]
    have hsign :
        ‖(-1 : ℂ) ^ (support p).card‖ = 1 := by
      simp
    rw [hsign, one_mul, norm_prod]
    calc
      (∏ q ∈ support p,
          ‖pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q)‖) ≤
          ∏ _q ∈ support p, (3 : ℝ) := by
        apply Finset.prod_le_prod
        · intro q _hq
          exact norm_nonneg _
        · intro q _hq
          exact norm_pairedFourierPrimeCoefficient_le_three
            hR p.1.prop (t q) (u q)
      _ = (3 : ℝ) ^ (support p).card := by
        simp

/-- Explicit fiberwise bound for the exact coordinatewise-truncation
discrepancy.  This is the finite quantity that remains after the
unrestricted-series bridge. -/
theorem norm_coordinatewiseTruncationSupportDiscrepancy_le
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 2 ≤ R)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖coordinatewiseTruncationSupportDiscrepancy
        χ R P t u support‖ ≤
      (((coordinatewiseTruncatedSupportFiber
            R P support).card : ℝ) +
        fixedFamilyPrimeSupportThreeMajorant support) *
      (χ.fourierProductMomentDensity (fun _ => 0) t *
        χ.fourierProductMomentDensity (fun _ => 0) u) := by
  unfold coordinatewiseTruncationSupportDiscrepancy
  have htruncated :=
    norm_coordinatewiseTruncatedSupportCoefficient_le
      χ R P t u support
  have hcoefficient :=
    norm_fixedFamilyPrimeSupportCoefficient_le_threeMajorant
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
      ((coordinatewiseTruncatedSupportFiber R P support).card : ℝ) *
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u) +
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) *
          fixedFamilyPrimeSupportThreeMajorant support := by
      exact add_le_add htruncated
        (mul_le_mul_of_nonneg_left hcoefficient hdensity)
    _ = _ := by ring

/-- Coarser form using only the ambient coordinatewise box cardinality. -/
theorem norm_coordinatewiseTruncationSupportDiscrepancy_le_box
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 2 ≤ R)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖coordinatewiseTruncationSupportDiscrepancy
        χ R P t u support‖ ≤
      (((R ^ (2 * Fintype.card κ) : ℕ) : ℝ) +
        fixedFamilyPrimeSupportThreeMajorant support) *
      (χ.fourierProductMomentDensity (fun _ => 0) t *
        χ.fourierProductMomentDensity (fun _ => 0) u) := by
  have hfiber :
      ((coordinatewiseTruncatedSupportFiber
          R P support).card : ℝ) ≤
        ((R ^ (2 * Fintype.card κ) : ℕ) : ℝ) := by
    exact_mod_cast
      card_coordinatewiseTruncatedSupportFiber_le R P support
  have hdensity :
      0 ≤
        χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u :=
    mul_nonneg
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) t)
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) u)
  exact
    (norm_coordinatewiseTruncationSupportDiscrepancy_le
      χ hR P t u support).trans
      (mul_le_mul_of_nonneg_right
        (add_le_add hfiber le_rfl)
        hdensity)

/-- The complete fixed-family discrepancy sum is bounded by the sum of the
fiberwise majorants, with the exact common-zero densities retained. -/
theorem norm_sum_coordinatewiseTruncationSupportDiscrepancy_mul_density_le
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
      ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        ((((coordinatewiseTruncatedSupportFiber
              R P support).card : ℝ) +
            fixedFamilyPrimeSupportThreeMajorant support) *
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u)) *
          ‖fixedFamilyPrimeSupportDensity forms support‖ := by
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
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro support _hsupport
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_coordinatewiseTruncationSupportDiscrepancy_le
          χ hR P t u support)
        (norm_nonneg _)

/-! ## The named carry-weighted truncation majorant -/

/-- The explicit nonnegative quantity left after bounding every canonical
carry cell and support fiber. -/
noncomputable def cfzCanonicalCarryTruncationMajorant
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) : ℝ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    |cfzCanonicalCarryCellDensity
        (N := N) forms carry| *
      ∑ support ∈
          fixedFamilyPrimeSupportAssignmentChoices
            κ (primesLEAsPrimes R),
        ((((coordinatewiseTruncatedSupportFiber
              R (primesLEAsPrimes R) support).card : ℝ) +
            fixedFamilyPrimeSupportThreeMajorant support) *
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u)) *
          ‖cfzCanonicalCarryPrimeSupportDensity
              N W b forms carry support‖

theorem cfzCanonicalCarryTruncationMajorant_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) :
    0 ≤ cfzCanonicalCarryTruncationMajorant
      (N := N) χ W b R forms t u := by
  unfold cfzCanonicalCarryTruncationMajorant
  apply Finset.sum_nonneg
  intro carry _hcarry
  exact mul_nonneg (abs_nonneg _) <|
    Finset.sum_nonneg fun support _hsupport =>
      mul_nonneg
        (mul_nonneg
          (add_nonneg
            (Nat.cast_nonneg _)
            (by
              unfold fixedFamilyPrimeSupportThreeMajorant
              positivity))
          (mul_nonneg
            (χ.fourierProductMomentDensity_nonneg (fun _ => 0) t)
            (χ.fourierProductMomentDensity_nonneg (fun _ => 0) u)))
        (norm_nonneg _)

/-- The actual carry-weighted coordinatewise discrepancy is dominated by
the named finite majorant. -/
theorem norm_cfzCanonicalCarryTruncationDiscrepancy_le_majorant
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) :
    ‖cfzCanonicalCarryTruncationDiscrepancy
        (N := N) χ W b R forms t u‖ ≤
      cfzCanonicalCarryTruncationMajorant
        (N := N) χ W b R forms t u := by
  classical
  unfold cfzCanonicalCarryTruncationDiscrepancy
    cfzCanonicalCarryTruncationMajorant
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
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro carry _hcarry
      rw [norm_mul, Complex.norm_real]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [cfzCanonicalCarryPrimeSupportDensity] using
        norm_sum_coordinatewiseTruncationSupportDiscrepancy_mul_density_le
          χ hR
          (cfzCarryAdjustedFamilyAtVector N W b forms carry)
          (primesLEAsPrimes R) t u

/-- Exact reduction of pointwise carry-discrepancy vanishing to the named
finite majorant.  This is the remaining coordinatewise-truncation
obligation; the unrestricted Euler-series tail has already been proved to
vanish above. -/
theorem
    tendsto_cfzCanonicalCarryTruncationDiscrepancy_of_majorant
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ)
    (hmajorant :
      Tendsto
        (fun R : ℕ =>
          cfzCanonicalCarryTruncationMajorant
            (N := N) χ W b R forms t u)
        atTop (𝓝 0)) :
    Tendsto
      (fun R : ℕ =>
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R forms t u)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with R hR
    exact
      norm_cfzCanonicalCarryTruncationDiscrepancy_le_majorant
        χ W b hR forms t u
  · exact hmajorant

end Wikipedia.SzemeredisTheorem
