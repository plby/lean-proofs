import Wikipedia.GreenTao.Sieve.ComplexEulerProductComparison
import Wikipedia.GreenTao.Sieve.CFZCarryEulerTail

/-!
# Unrestricted finite-prime-support Euler series

An Euler product is not the pointwise factorization of the divisor sum in
which every divisor is separately truncated by `d ≤ R`.  This file records
the honest unrestricted object that has such a factorization.

For a prime-indexed family `L p`, put

`E S = ∏ p ∈ S, (L p - 1)`

for a finite set of active primes `S`.  If the local errors are absolutely
summable, then the series over all finite prime supports is absolutely
summable and

`∑' S, E S = ∏' p, L p`.

Thus the unrestricted squarefree prime-support expansion has a rigorous
Euler product, with no divisor cutoff and no conditional rearrangement.
The final section specializes the construction to the exact paired Fourier
local factors.  Comparing this unrestricted series with the original
coordinatewise truncation remains a separate approximation theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Generic absolutely convergent support expansion -/

/-- The contribution of one finite set of active primes to an unrestricted
Euler expansion. -/
noncomputable def unrestrictedPrimeSupportTerm
    (localFactor : Nat.Primes → ℂ)
    (S : Finset Nat.Primes) : ℂ :=
  ∏ p ∈ S, (localFactor p - 1)

@[simp]
theorem unrestrictedPrimeSupportTerm_empty
    (localFactor : Nat.Primes → ℂ) :
    unrestrictedPrimeSupportTerm localFactor ∅ = 1 := by
  simp [unrestrictedPrimeSupportTerm]

/-- On a fixed finite prime set, summing over all active sub-supports gives
the corresponding finite Euler product. -/
theorem sum_unrestrictedPrimeSupportTerm_powerset
    (localFactor : Nat.Primes → ℂ)
    (P : Finset Nat.Primes) :
    ∑ S ∈ P.powerset,
        unrestrictedPrimeSupportTerm localFactor S =
      ∏ p ∈ P, localFactor p := by
  rw [show
      (∑ S ∈ P.powerset,
          unrestrictedPrimeSupportTerm localFactor S) =
        ∏ p ∈ P, (1 + (localFactor p - 1)) by
      simpa [unrestrictedPrimeSupportTerm] using
        (Finset.prod_one_add
          (s := P) (f := fun p => localFactor p - 1)).symm]
  apply Finset.prod_congr rfl
  intro p _hp
  ring

/-- Absolute summability of the local errors implies absolute summability
of the series indexed by all finite prime supports. -/
theorem summable_unrestrictedPrimeSupportTerm
    {localFactor : Nat.Primes → ℂ}
    (hlocal :
      Summable (fun p : Nat.Primes => ‖localFactor p - 1‖)) :
    Summable (unrestrictedPrimeSupportTerm localFactor) := by
  change Summable
    (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, (localFactor p - 1))
  exact
    summable_finsetProd_of_summable_norm
      (f := fun p : Nat.Primes => localFactor p - 1)
      hlocal

/-- The absolutely convergent unrestricted support series is exactly the
unordered Euler product. -/
theorem tsum_unrestrictedPrimeSupportTerm_eq_tprod
    {localFactor : Nat.Primes → ℂ}
    (hlocal :
      Summable (fun p : Nat.Primes => ‖localFactor p - 1‖)) :
    ∑' S : Finset Nat.Primes,
        unrestrictedPrimeSupportTerm localFactor S =
      ∏' p : Nat.Primes, localFactor p := by
  have hsupports :=
    summable_finsetProd_of_summable_norm
      (f := fun p : Nat.Primes => localFactor p - 1)
      hlocal
  change
    (∑' S : Finset Nat.Primes,
      ∏ p ∈ S, (localFactor p - 1)) =
      ∏' p : Nat.Primes, localFactor p
  rw [← tprod_one_add hsupports]
  apply tprod_congr
  intro p
  ring

/-- Canonical `HasSum` form, convenient for subsequent Fubini arguments. -/
theorem unrestrictedPrimeSupportTerm_hasSum
    {localFactor : Nat.Primes → ℂ}
    (hlocal :
      Summable (fun p : Nat.Primes => ‖localFactor p - 1‖)) :
    HasSum
      (unrestrictedPrimeSupportTerm localFactor)
      (∏' p : Nat.Primes, localFactor p) := by
  rw [← tsum_unrestrictedPrimeSupportTerm_eq_tprod hlocal]
  exact (summable_unrestrictedPrimeSupportTerm hlocal).hasSum

/-! ## Absolute convergence of paired-Fourier local errors -/

/-- The norm of a prime Fourier phase is an exact real power.  In
particular it is independent of the Fourier frequency. -/
theorem SmoothSieveCutoff.norm_divisorMultiplicativePhase_prime_eq_rpow
    {R : ℕ} (_hR : 1 < R)
    (p : Nat.Primes) (t : ℝ) :
    ‖divisorMultiplicativePhase R (p : ℕ) t‖ =
      (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) := by
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  rw [divisorMultiplicativePhase,
    norm_cutoffMultiplicativePhase,
    Real.rpow_def_of_pos hp0]
  congr 1
  rw [div_eq_mul_inv]
  ring

/-- The paired prime coefficient retains the power saving coming from the
positive real part of the Fourier shift. -/
theorem norm_pairedFourierPrimeCoefficient_le_three_mul_rpow
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : ℝ) :
    ‖pairedFourierPrimeCoefficient
        R (p : ℕ) t u‖ ≤
      3 * (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹) := by
  let x : ℝ :=
    (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  have hx0 : 0 ≤ x := by
    exact (Real.rpow_pos_of_pos hp0 _).le
  have ht :
      ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t‖ = x := by
    exact
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_prime_eq_rpow
        (by omega) p t
  have hu :
      ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) u‖ = x := by
    exact
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_prime_eq_rpow
        (by omega) p u
  have hx1 : x ≤ 1 := by
    rw [← ht]
    exact
      SmoothSieveCutoff.norm_divisorMultiplicativePhase_le_one
        hR p.prop t
  let z : ℂ :=
    SmoothSieveCutoff.divisorMultiplicativePhase
      R (p : ℕ) t
  let w : ℂ :=
    SmoothSieveCutoff.divisorMultiplicativePhase
      R (p : ℕ) u
  unfold pairedFourierPrimeCoefficient
  calc
    ‖SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) t +
        SmoothSieveCutoff.divisorMultiplicativePhase
          R (p : ℕ) u -
        SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) t *
          SmoothSieveCutoff.divisorMultiplicativePhase
            R (p : ℕ) u‖ ≤
        (‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) t‖ +
            ‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) u‖) +
          ‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) t‖ *
            ‖SmoothSieveCutoff.divisorMultiplicativePhase
              R (p : ℕ) u‖ := by
      change ‖z + w - z * w‖ ≤
        (‖z‖ + ‖w‖) + ‖z‖ * ‖w‖
      calc
        ‖z + w - z * w‖ ≤
            ‖z + w‖ + ‖z * w‖ :=
          norm_sub_le _ _
        _ = ‖z + w‖ + ‖z‖ * ‖w‖ := by
          rw [norm_mul]
        _ ≤ (‖z‖ + ‖w‖) + ‖z‖ * ‖w‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ = (x + x) + x * x := by rw [ht, hu]
    _ ≤ 3 * x := by nlinarith

/-- The first-order part of a paired Fourier factor is bounded by the
summable prime power `p^(-1-1/log R)`. -/
theorem norm_pairedFourierFirstOrderLocalModel_sub_one_le
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : κ → ℝ) :
    ‖pairedFourierFirstOrderLocalModel
          R (p : ℕ) t u - 1‖ ≤
      (3 * Fintype.card κ : ℝ) *
        (p : ℝ) ^
          (-(Real.log (R : ℝ))⁻¹ - 1) := by
  let x : ℝ :=
    (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  have hsum :
      ‖∑ q : κ,
          pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q)‖ ≤
        (Fintype.card κ : ℝ) * (3 * x) := by
    calc
      ‖∑ q : κ,
          pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q)‖ ≤
          ∑ q : κ,
            ‖pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q)‖ :=
        norm_sum_le Finset.univ _
      _ ≤ ∑ _q : κ, 3 * x := by
        apply Finset.sum_le_sum
        intro q _hq
        exact
          norm_pairedFourierPrimeCoefficient_le_three_mul_rpow
            hR p (t q) (u q)
      _ = (Fintype.card κ : ℝ) * (3 * x) := by simp
  have hpower :
      x / (p : ℝ) =
        (p : ℝ) ^
          (-(Real.log (R : ℝ))⁻¹ - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one,
      ← Real.rpow_add hp0]
    simp only [sub_eq_add_neg]
  rw [pairedFourierFirstOrderLocalModel,
    complexFirstOrderLocalModel]
  have hrearrange :
      (1 -
          (∑ q : κ,
            pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q)) /
            ((p : ℕ) : ℂ)) -
          1 =
        -((∑ q : κ,
            pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q)) /
            ((p : ℕ) : ℂ)) := by
    ring
  rw [hrearrange, norm_neg, norm_div,
    Complex.norm_natCast]
  calc
    ‖∑ q : κ,
        pairedFourierPrimeCoefficient
          R (p : ℕ) (t q) (u q)‖ /
        (p : ℝ) ≤
      ((Fintype.card κ : ℝ) * (3 * x)) /
        (p : ℝ) := by
      exact div_le_div_of_nonneg_right hsum hp0.le
    _ =
      (3 * Fintype.card κ : ℝ) *
        (p : ℝ) ^
          (-(Real.log (R : ℝ))⁻¹ - 1) := by
      rw [← hpower]
      ring

/-- At every good prime, the complete paired Fourier local error is
dominated by a summable first-order power plus the familiar square error.
-/
theorem norm_pairedFourierPrimeLocalFactor_sub_one_le_rpow_add_sq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes)
    (hlarge : exceptionalPrimeBound forms < (p : ℕ)) :
    ‖pairedFourierPrimeLocalFactor
          R forms t u p - 1‖ ≤
      (3 * Fintype.card κ : ℝ) *
          (p : ℝ) ^
            (-(Real.log (R : ℝ))⁻¹ - 1) +
        (4 : ℝ) ^ Fintype.card κ /
          (p : ℝ) ^ 2 := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  let firstOrder : ℂ :=
    pairedFourierFirstOrderLocalModel
      R (p : ℕ) t u
  have hremainder :
      ‖pairedFourierPrimeLocalFactor
            R forms t u p - firstOrder‖ ≤
        (4 : ℝ) ^ Fintype.card κ /
          (p : ℝ) ^ 2 := by
    simpa only [pairedFourierPrimeLocalFactor, firstOrder] using
      norm_pairedFourierLocalFactor_sub_firstOrder_le
        hnonzero hindependent hR p.prop hlarge t u
  have hfirst :
      ‖firstOrder - 1‖ ≤
        (3 * Fintype.card κ : ℝ) *
          (p : ℝ) ^
            (-(Real.log (R : ℝ))⁻¹ - 1) := by
    simpa only [firstOrder] using
      norm_pairedFourierFirstOrderLocalModel_sub_one_le
        hR p t u
  calc
    ‖pairedFourierPrimeLocalFactor
          R forms t u p - 1‖ ≤
        ‖pairedFourierPrimeLocalFactor
            R forms t u p - firstOrder‖ +
          ‖firstOrder - 1‖ := by
      have hrewrite :
          pairedFourierPrimeLocalFactor
              R forms t u p - 1 =
            (pairedFourierPrimeLocalFactor
                R forms t u p - firstOrder) +
              (firstOrder - 1) := by
        ring
      rw [hrewrite]
      exact norm_add_le _ _
    _ ≤
        (4 : ℝ) ^ Fintype.card κ /
            (p : ℝ) ^ 2 +
          (3 * Fintype.card κ : ℝ) *
            (p : ℝ) ^
              (-(Real.log (R : ℝ))⁻¹ - 1) :=
      add_le_add hremainder hfirst
    _ = _ := by ring

/-- The exact paired-Fourier local errors are absolutely summable.  The
essential point is that the positive shift `1/log R` turns the apparent
`p⁻¹` first-order term into `p^(-1-1/log R)`. -/
theorem summable_norm_pairedFourierPrimeLocalFactor_sub_one
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    Summable (fun p : Nat.Primes =>
      ‖pairedFourierPrimeLocalFactor
          R forms t u p - 1‖) := by
  let exponent : ℝ :=
    -(Real.log (R : ℝ))⁻¹ - 1
  have hlog : 0 < Real.log (R : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hexponent : exponent < -1 := by
    dsimp only [exponent]
    have hinv : 0 < (Real.log (R : ℝ))⁻¹ :=
      inv_pos.mpr hlog
    linarith
  let majorant : Nat.Primes → ℝ :=
    fun p =>
      (3 * Fintype.card κ : ℝ) *
          (p : ℝ) ^ exponent +
        (4 : ℝ) ^ Fintype.card κ /
          (p : ℝ) ^ 2
  have hmajorant : Summable majorant := by
    have hfirst :
        Summable (fun p : Nat.Primes =>
          (3 * Fintype.card κ : ℝ) *
            (p : ℝ) ^ exponent) :=
      (Nat.Primes.summable_rpow.mpr hexponent).mul_left
        (3 * Fintype.card κ : ℝ)
    have hsquare :
        Summable (fun p : Nat.Primes =>
          (4 : ℝ) ^ Fintype.card κ /
            (p : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv] using
        summable_prime_inv_sq.mul_left
          ((4 : ℝ) ^ Fintype.card κ)
    exact hfirst.add hsquare
  let maskedError : Nat.Primes → ℝ :=
    fun p =>
      if exceptionalPrimeBound forms < (p : ℕ) then
        ‖pairedFourierPrimeLocalFactor
            R forms t u p - 1‖
      else
        0
  have hmasked : Summable maskedError := by
    apply hmajorant.of_nonneg_of_le
    · intro p
      dsimp only [maskedError]
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    · intro p
      dsimp only [maskedError, majorant, exponent]
      split_ifs with hp
      · exact
          norm_pairedFourierPrimeLocalFactor_sub_one_le_rpow_add_sq
            hnonzero hindependent hR t u p hp
      · have hfirstNonneg :
            0 ≤
              (3 * Fintype.card κ : ℝ) *
                (p : ℝ) ^
                  (-(Real.log (R : ℝ))⁻¹ - 1) := by
          positivity
        have hsquareNonneg :
            0 ≤
              (4 : ℝ) ^ Fintype.card κ /
                (p : ℝ) ^ 2 := by
          positivity
        linarith
  apply hmasked.congr_cofinite
  filter_upwards
    [(finite_setOf_prime_le
      (exceptionalPrimeBound forms)).eventually_cofinite_notMem]
    with p hp
  have hlarge :
      exceptionalPrimeBound forms < (p : ℕ) := by
    apply Nat.lt_of_not_ge
    intro hle
    apply hp
    simpa only [Set.mem_setOf_eq] using hle
  simp [maskedError, hlarge]

/-! ## Direct-good-prime and carry-block versions -/

/-- Direct modular good-prime version of the summable local-error bound. -/
theorem
    norm_pairedFourierPrimeLocalFactor_sub_one_le_rpow_add_sq_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (p : Nat.Primes)
    (hnonzero : AffineNonzeroGoodPrime (p : ℕ) forms)
    (hrankTwo : AffineRankTwoGoodPrime (p : ℕ) forms) :
    ‖pairedFourierPrimeLocalFactor
          R forms t u p - 1‖ ≤
      (3 * Fintype.card κ : ℝ) *
          (p : ℝ) ^
            (-(Real.log (R : ℝ))⁻¹ - 1) +
        (4 : ℝ) ^ Fintype.card κ /
          (p : ℝ) ^ 2 := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  let firstOrder : ℂ :=
    pairedFourierFirstOrderLocalModel
      R (p : ℕ) t u
  have hremainder :
      ‖pairedFourierPrimeLocalFactor
            R forms t u p - firstOrder‖ ≤
        (4 : ℝ) ^ Fintype.card κ /
          (p : ℝ) ^ 2 := by
    simpa only [pairedFourierPrimeLocalFactor, firstOrder] using
      norm_pairedFourierLocalFactor_sub_firstOrder_le_of_goodPrime
        hnonzero hrankTwo hR t u
  have hfirst :
      ‖firstOrder - 1‖ ≤
        (3 * Fintype.card κ : ℝ) *
          (p : ℝ) ^
            (-(Real.log (R : ℝ))⁻¹ - 1) := by
    simpa only [firstOrder] using
      norm_pairedFourierFirstOrderLocalModel_sub_one_le
        hR p t u
  calc
    ‖pairedFourierPrimeLocalFactor
          R forms t u p - 1‖ ≤
        ‖pairedFourierPrimeLocalFactor
            R forms t u p - firstOrder‖ +
          ‖firstOrder - 1‖ := by
      have hrewrite :
          pairedFourierPrimeLocalFactor
              R forms t u p - 1 =
            (pairedFourierPrimeLocalFactor
                R forms t u p - firstOrder) +
              (firstOrder - 1) := by
        ring
      rw [hrewrite]
      exact norm_add_le _ _
    _ ≤
        (4 : ℝ) ^ Fintype.card κ /
            (p : ℝ) ^ 2 +
          (3 * Fintype.card κ : ℝ) *
            (p : ℝ) ^
              (-(Real.log (R : ℝ))⁻¹ - 1) :=
      add_le_add hremainder hfirst
    _ = _ := by ring

/-- Absolute convergence needs only direct one-form and rank-two geometry
outside one finite numerical cutoff.  This is the appropriate interface
for carry-adjusted families, whose constants and integer exceptional bound
may be very large while their modular geometry is uniform. -/
theorem
    summable_norm_pairedFourierPrimeLocalFactor_sub_one_of_eventually_good
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) (B : ℕ)
    (hgood :
      ∀ p : Nat.Primes, B < (p : ℕ) →
        AffineNonzeroGoodPrime (p : ℕ) forms ∧
          AffineRankTwoGoodPrime (p : ℕ) forms) :
    Summable (fun p : Nat.Primes =>
      ‖pairedFourierPrimeLocalFactor
          R forms t u p - 1‖) := by
  let exponent : ℝ :=
    -(Real.log (R : ℝ))⁻¹ - 1
  have hlog : 0 < Real.log (R : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < R by omega))
  have hexponent : exponent < -1 := by
    dsimp only [exponent]
    have hinv : 0 < (Real.log (R : ℝ))⁻¹ :=
      inv_pos.mpr hlog
    linarith
  let majorant : Nat.Primes → ℝ :=
    fun p =>
      (3 * Fintype.card κ : ℝ) *
          (p : ℝ) ^ exponent +
        (4 : ℝ) ^ Fintype.card κ /
          (p : ℝ) ^ 2
  have hmajorant : Summable majorant := by
    have hfirst :
        Summable (fun p : Nat.Primes =>
          (3 * Fintype.card κ : ℝ) *
            (p : ℝ) ^ exponent) :=
      (Nat.Primes.summable_rpow.mpr hexponent).mul_left
        (3 * Fintype.card κ : ℝ)
    have hsquare :
        Summable (fun p : Nat.Primes =>
          (4 : ℝ) ^ Fintype.card κ /
            (p : ℝ) ^ 2) := by
      simpa [div_eq_mul_inv] using
        summable_prime_inv_sq.mul_left
          ((4 : ℝ) ^ Fintype.card κ)
    exact hfirst.add hsquare
  let maskedError : Nat.Primes → ℝ :=
    fun p =>
      if B < (p : ℕ) then
        ‖pairedFourierPrimeLocalFactor
            R forms t u p - 1‖
      else
        0
  have hmasked : Summable maskedError := by
    apply hmajorant.of_nonneg_of_le
    · intro p
      dsimp only [maskedError]
      split_ifs
      · exact norm_nonneg _
      · exact le_rfl
    · intro p
      dsimp only [maskedError, majorant, exponent]
      split_ifs with hp
      · obtain ⟨hnonzero, hrankTwo⟩ := hgood p hp
        exact
          norm_pairedFourierPrimeLocalFactor_sub_one_le_rpow_add_sq_of_goodPrime
            hR t u p hnonzero hrankTwo
      · have hfirstNonneg :
            0 ≤
              (3 * Fintype.card κ : ℝ) *
                (p : ℝ) ^
                  (-(Real.log (R : ℝ))⁻¹ - 1) := by
          positivity
        have hsquareNonneg :
            0 ≤
              (4 : ℝ) ^ Fintype.card κ /
                (p : ℝ) ^ 2 := by
          positivity
        linarith
  apply hmasked.congr_cofinite
  filter_upwards
    [(finite_setOf_prime_le B).eventually_cofinite_notMem]
    with p hp
  have hlarge : B < (p : ℕ) := by
    apply Nat.lt_of_not_ge
    intro hle
    apply hp
    simpa only [Set.mem_setOf_eq] using hle
  simp [maskedError, hlarge]

namespace SelectedCFZCarryFourierBlockData

/-- The exact arithmetic local factor on one packaged carry block. -/
noncomputable def pairedPrimeLocalFactor
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k)
    (p : Nat.Primes) : ℂ :=
  pairedFourierPrimeLocalFactor
    d.R d.carryAdjustedFamily d.t d.u p

/-- The unrestricted finite-prime-support term on one packaged carry
block. -/
noncomputable def unrestrictedEulerPrimeSupportTerm
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k)
    (S : Finset Nat.Primes) : ℂ :=
  unrestrictedPrimeSupportTerm d.pairedPrimeLocalFactor S

/-- At fixed carry-block data, the exact arithmetic local errors are
absolutely summable.  The cutoff used in the proof contains the original
`k`-only CFZ exceptional bound and the fixed primorial; it does not use the
much larger exceptional bound of the carry-adjusted integer constants. -/
theorem summable_norm_pairedPrimeLocalFactor_sub_one
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCarryFourierBlockData k)
    (hR : 2 ≤ d.R) :
    Summable (fun p : Nat.Primes =>
      ‖d.pairedPrimeLocalFactor p - 1‖) := by
  let B : ℕ :=
    max
      (exceptionalPrimeBound
        (fun q : CFZFormIndex k => cfzAffineForm q))
      (primorial d.w)
  apply
    summable_norm_pairedFourierPrimeLocalFactor_sub_one_of_eventually_good
      hR d.t d.u B
  intro p hp
  letI : NeZero d.N := d.N_neZero
  have hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) := by
    exact
      (Nat.le_max_left
        (exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q))
        (primorial d.w)).trans_lt hp
  have hpW : ¬(p : ℕ) ∣ primorial d.w := by
    intro hpDvd
    have hpLe :
        (p : ℕ) ≤ primorial d.w :=
      Nat.le_of_dvd (primorial_pos d.w) hpDvd
    have hWlt :
        primorial d.w < (p : ℕ) :=
      (Nat.le_max_right
        (exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q))
        (primorial d.w)).trans_lt hp
    omega
  simpa only [pairedPrimeLocalFactor,
    carryAdjustedFamily] using
    (selectedCFZCarryAdjustedFamilyAtBlock_goodPrime
      (N := d.N) (W := primorial d.w)
      hk p.prop hpW hlarge d.e
      (pairedDivisorLcm d.z) d.b
      (fun v => (d.block v : ℕ)))

/-- The unrestricted carry-block support series is absolutely summable. -/
theorem summable_unrestrictedEulerPrimeSupportTerm
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCarryFourierBlockData k)
    (hR : 2 ≤ d.R) :
    Summable d.unrestrictedEulerPrimeSupportTerm :=
  summable_unrestrictedPrimeSupportTerm
    (d.summable_norm_pairedPrimeLocalFactor_sub_one hk hR)

/-- Honest Euler factorization of the unrestricted carry-block support
series.  This theorem concerns the unrestricted series, not the original
coordinatewise divisor truncation. -/
theorem tsum_unrestrictedEulerPrimeSupportTerm_eq_tprod
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCarryFourierBlockData k)
    (hR : 2 ≤ d.R) :
    ∑' S : Finset Nat.Primes,
        d.unrestrictedEulerPrimeSupportTerm S =
      ∏' p : Nat.Primes, d.pairedPrimeLocalFactor p :=
  tsum_unrestrictedPrimeSupportTerm_eq_tprod
    (d.summable_norm_pairedPrimeLocalFactor_sub_one hk hR)

end SelectedCFZCarryFourierBlockData

/-! ## Exact paired-Fourier specialization -/

/-- The unrestricted finite-prime-support term for the exact paired Fourier
local factors of an affine family. -/
noncomputable def unrestrictedPairedFourierPrimeSupportTerm
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (S : Finset Nat.Primes) : ℂ :=
  unrestrictedPrimeSupportTerm
    (pairedFourierPrimeLocalFactor R forms t u) S

/-- Whenever the exact paired-Fourier local errors are absolutely
summable, their unrestricted squarefree support series is the arithmetic
Euler product identified by `ComplexEulerProductComparison`. -/
theorem tsum_unrestrictedPairedFourierPrimeSupportTerm_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : κ → ℝ) :
    ∑' S : Finset Nat.Primes,
        unrestrictedPairedFourierPrimeSupportTerm
          R forms t u S =
      (cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R forms t u p := by
  rw [show
      (∑' S : Finset Nat.Primes,
          unrestrictedPairedFourierPrimeSupportTerm
            R forms t u S) =
        ∏' p : Nat.Primes,
          pairedFourierPrimeLocalFactor R forms t u p by
      exact
        tsum_unrestrictedPrimeSupportTerm_eq_tprod
          (summable_norm_pairedFourierPrimeLocalFactor_sub_one
            hnonzero hindependent hR t u)]
  exact
    tprod_pairedFourierPrimeLocalFactor_eq
      hnonzero hindependent hR t u

end Wikipedia.SzemeredisTheorem
