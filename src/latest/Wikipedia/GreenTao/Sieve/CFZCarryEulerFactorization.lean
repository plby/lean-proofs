import Wikipedia.GreenTao.Sieve.CFZCarryEulerTail
import Wikipedia.GreenTao.Sieve.WTrickedEulerCorrection

/-!
# Exact small/large-prime factorization on CFZ carry blocks

The carry constants introduced by quotient-block decomposition do not
disturb the W-trick at primes dividing `W`: every carry-adjusted affine form
is still the constant reduced residue `b` modulo such a prime.  This file
upgrades that observation from real avoidance products to the complex
Fourier local factors.

For a packaged selected carry block we consequently identify the product of
the arithmetic/zeta ratios at `p ≤ w` with the already normalized
`smallPrimeZetaCorrection`.  The complementary product is exactly the
bounded-mask product from `CFZCarryEulerTail`.  Once `w` contains the
fixed `k`-exceptional range, the direct `O_k(p⁻²)` estimate proves
multipliability on the complement and yields an exact small/large split of
the complete arithmetic correction.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Unit complex factors at primes dividing the primorial -/

/-- Every complex-weighted avoidance product of carry-adjusted CFZ forms is
pointwise one at a prime dividing `W`. -/
theorem
    complexWeightedLocalAvoidanceProduct_cfzCarryAdjusted_eq_one_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k p : ℕ} [NeZero p]
    (N W b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → CFZFormIndex k) (c : κ → ℤ)
    (a : κ → ℂ) (x : CFZVariable k → ZMod p) :
    complexWeightedLocalAvoidanceProduct p
        (fun q =>
          cfzCarryAdjustedAffineForm
            N W b (forms q) (c q))
        a x = 1 := by
  simp [complexWeightedLocalAvoidanceProduct,
    cfzCarryAdjustedAffineForm_zeroFinsetZMod_eq_empty
      N W b hp hpW hWb]

/-- The averaged complex local factor of a carry-adjusted CFZ family is one
at a prime dividing `W`. -/
theorem complexWeightedLocalFactor_cfzCarryAdjusted_eq_one_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k p : ℕ} [NeZero p]
    (N W b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (forms : κ → CFZFormIndex k) (c : κ → ℤ)
    (a : κ → ℂ) :
    complexWeightedLocalFactor p
        (fun q =>
          cfzCarryAdjustedAffineForm
            N W b (forms q) (c q))
        a = 1 := by
  unfold complexWeightedLocalFactor
  rw [show
      complexWeightedLocalAvoidanceProduct p
          (fun q =>
            cfzCarryAdjustedAffineForm
              N W b (forms q) (c q))
          a =
        fun _x => 1 by
      funext x
      exact
        complexWeightedLocalAvoidanceProduct_cfzCarryAdjusted_eq_one_of_dvd
          N W b hp hpW hWb forms c a x]
  exact Fintype.expect_one

/-- In particular, the paired-Fourier factor of the carry-adjusted family
on a quotient block is one at every prime dividing `W`. -/
theorem pairedFourierLocalFactor_cfzCarryAdjustedFamilyAtBlock_eq_one_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N p : ℕ} [NeZero N] [NeZero p]
    (D W b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (R : ℕ) (forms : κ → CFZFormIndex k)
    (block : CFZVariable k → ℕ) (t u : κ → ℝ) :
    pairedFourierLocalFactor R p
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) D W b forms block)
        t u = 1 := by
  exact
    complexWeightedLocalFactor_cfzCarryAdjusted_eq_one_of_dvd
      N W b hp hpW hWb forms
      (fun q =>
        cfzCarry (N := N) (forms q)
          (fun v => D * block v))
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))

/-! ## Exact small-prime correction for a packaged carry block -/

/-- The actual carry-block local factor is one at every prime `p ≤ w`. -/
theorem selectedCFZCarryPairedFourierLocalFactor_eq_one_of_small
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k)
    (hwb : (primorial d.w).Coprime d.b)
    {p : Nat.Primes} (hp : p ∈ smallPrimeFinset d.w) :
    pairedFourierPrimeLocalFactor d.R
        d.carryAdjustedFamily d.t d.u p = 1 := by
  let : NeZero d.N := d.N_neZero
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  rw [pairedFourierPrimeLocalFactor]
  unfold SelectedCFZCarryFourierBlockData.carryAdjustedFamily
  exact
    pairedFourierLocalFactor_cfzCarryAdjustedFamilyAtBlock_eq_one_of_dvd
      (N := d.N)
      (pairedDivisorLcm d.z) (primorial d.w) d.b
      p.prop
      (p.prop.dvd_primorial_iff.mpr
        (mem_smallPrimeFinset.mp hp))
      hwb d.R
      (fun q : SelectedCFZFormIndex d.e => q.1)
      (fun v => (d.block v : ℕ)) d.t d.u

/-- At a small prime the carry-block arithmetic/zeta ratio is exactly the
inverse universal zeta factor. -/
theorem
    selectedCFZCarryPrimeArithmeticToZetaLocalRatio_eq_inv_of_small
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k)
    (hwb : (primorial d.w).Coprime d.b)
    {p : Nat.Primes} (hp : p ∈ smallPrimeFinset d.w) :
    d.primeArithmeticToZetaLocalRatio p =
      (cutoffZetaEulerLocalFactor d.R d.t d.u p)⁻¹ := by
  let : NeZero d.N := d.N_neZero
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hlocal :
      pairedFourierLocalFactor d.R (p : ℕ)
          d.carryAdjustedFamily d.t d.u = 1 := by
    simpa [pairedFourierPrimeLocalFactor] using
      selectedCFZCarryPairedFourierLocalFactor_eq_one_of_small
        d hwb hp
  rw [SelectedCFZCarryFourierBlockData.primeArithmeticToZetaLocalRatio,
    pairedFourierArithmeticToZetaLocalRatio,
    hlocal,
    one_div,
    cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor]

/-- The finite product of all small-prime carry-block correction ratios is
the standard small-prime zeta correction. -/
theorem prod_selectedCFZCarrySmallPrimeArithmeticToZetaRatio_eq
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k)
    (hwb : (primorial d.w).Coprime d.b) :
    ∏ p ∈ smallPrimeFinset d.w,
        d.primeArithmeticToZetaLocalRatio p =
      smallPrimeZetaCorrection d.R d.w d.t d.u := by
  apply Finset.prod_congr rfl
  intro p hp
  exact
    selectedCFZCarryPrimeArithmeticToZetaLocalRatio_eq_inv_of_small
      d hwb hp

/-! ## The complementary product and the exact complete correction -/

/-- Masking primes at most `w` is the multiplicative indicator of the
set-theoretic complement of `smallPrimeFinset w`. -/
theorem boundedMaskedComplexPrimeLocalFactor_eq_smallPrime_compl_mulIndicator
    (w : ℕ) (localFactor : Nat.Primes → ℂ) :
    boundedMaskedComplexPrimeLocalFactor w localFactor =
      ((smallPrimeFinset w : Set Nat.Primes)ᶜ).mulIndicator
        localFactor := by
  funext p
  by_cases hp : (p : ℕ) ≤ w
  · have hmem : p ∈ smallPrimeFinset w :=
      mem_smallPrimeFinset.mpr hp
    simp [boundedMaskedComplexPrimeLocalFactor, hp, hmem]
  · have hnotmem : p ∉ smallPrimeFinset w := by
      simpa [mem_smallPrimeFinset] using hp
    simp [boundedMaskedComplexPrimeLocalFactor, hp, hnotmem]

/-- The bounded-mask definition of the large-prime carry correction is
literally the unordered product over the complement of the small-prime
finset. -/
theorem
    selectedCFZCarryLargePrimeEulerCorrection_eq_tprod_smallPrime_compl
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k) :
    d.largePrimeEulerCorrection =
      ∏' p :
          ↑((smallPrimeFinset d.w : Set Nat.Primes)ᶜ),
        d.primeArithmeticToZetaLocalRatio p := by
  rw [SelectedCFZCarryFourierBlockData.largePrimeEulerCorrection,
    tprod_subtype,
    ← boundedMaskedComplexPrimeLocalFactor_eq_smallPrime_compl_mulIndicator]

/-- Above the fixed exceptional cutoff, the carry-block arithmetic/zeta
ratios are multipliable on the complement of the small primes. -/
theorem
    multipliable_selectedCFZCarryPrimeArithmeticToZetaLocalRatio_smallPrime_compl
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCarryFourierBlockData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w) :
    Multipliable
      (fun p :
          ↑((smallPrimeFinset d.w : Set Nat.Primes)ᶜ) =>
        d.primeArithmeticToZetaLocalRatio p) := by
  have hmasked :
      HasComplexPrimeSquareError
        (selectedCFZCarryEulerTailErrorConstant k)
        (boundedMaskedComplexPrimeLocalFactor
          d.w d.primeArithmeticToZetaLocalRatio) := by
    apply
      hasComplexPrimeSquareError_boundedMasked
        d.w
        (selectedCFZCarryEulerTailErrorConstant_nonneg k)
    intro p hp
    have hpW :
        ¬(p : ℕ) ∣ primorial d.w := by
      rw [p.prop.dvd_primorial_iff]
      exact Nat.not_le.mpr hp
    exact
      norm_selectedCFZCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
        hk d hR p hpW (hw.trans_lt hp)
  apply
    (multipliable_subtype_iff_mulIndicator
      (f := d.primeArithmeticToZetaLocalRatio)
      (s :=
        (smallPrimeFinset d.w : Set Nat.Primes)ᶜ)).mpr
  rw [←
    boundedMaskedComplexPrimeLocalFactor_eq_smallPrime_compl_mulIndicator]
  exact hmasked.multipliable

/-- **Exact carry-block Euler correction.**  The standard finite
small-prime zeta correction times the convergent carry-block large-prime
correction is the complete unordered product of the arithmetic/zeta local
ratios. -/
theorem smallPrimeZetaCorrection_mul_selectedCFZCarryLargePrimeEulerCorrection
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCarryFourierBlockData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w)
    (hwb : (primorial d.w).Coprime d.b) :
    smallPrimeZetaCorrection d.R d.w d.t d.u *
        d.largePrimeEulerCorrection =
      ∏' p : Nat.Primes,
        d.primeArithmeticToZetaLocalRatio p := by
  rw [←
      prod_selectedCFZCarrySmallPrimeArithmeticToZetaRatio_eq
        d hwb,
    selectedCFZCarryLargePrimeEulerCorrection_eq_tprod_smallPrime_compl]
  rw [←
    Finset.tprod_subtype'
      (smallPrimeFinset d.w)
      d.primeArithmeticToZetaLocalRatio]
  exact
    Multipliable.tprod_mul_tprod_compl
      ((smallPrimeFinset d.w).multipliable
        d.primeArithmeticToZetaLocalRatio)
      (multipliable_selectedCFZCarryPrimeArithmeticToZetaLocalRatio_smallPrime_compl
        hk d hR hw)

end Wikipedia.SzemeredisTheorem
