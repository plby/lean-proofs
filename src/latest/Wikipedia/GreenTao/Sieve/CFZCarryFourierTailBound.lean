import Wikipedia.GreenTao.Sieve.CFZCarryFourierBridge
import Wikipedia.GreenTao.Sieve.DivisorCoefficientBounds

/-!
# Honest Fourier-tail bounds for the carry-block divisor expansion

The carry-block Fourier integrand is a finite sum indexed by paired divisor
families.  Taking absolute values before summing loses the cancellation that
will eventually come from the arithmetic Euler product.  This file records
the sharp domination available without making such a cancellation claim.

The loss is isolated in `selectedCFZCarryFourierCoefficientMass`.  Unlike the
raw cardinality `R ^ (2m)`, this quantity retains both the carry-block Euler
coefficient and every Möbius zero.  The remaining analytic factor is a
genuine Schwartz tail, independent of `R`, `W`, `b`, and the divisor family.

Consequently the fully Selberg-scaled complementary integral tends to zero
as soon as the correspondingly scaled coefficient mass is eventually
bounded.  After exceptional-prime coverage, the coefficient mass is further
reduced to a harmonic LCM mass.  The remaining finite combinatorial estimate
is the expected prime-support bound

`harmonicLcmMass R ≤ ∏ p ∈ primesLE R,
  (1 + (2 ^ (2 * m) - 1) / p)`.

Together with the standard zeta-at-`1 + 1 / log R` majorization this is
polylogarithmic, and an arbitrarily high Schwartz moment then beats it at
`T = sqrt (log R)`.  That prime-support estimate is made explicit as the
sole missing step; it is not replaced by the useless raw divisor-choice
count.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace SmoothSieveCutoff

/-! ## The exact coefficient mass retained by triangle domination -/

/-- The Möbius mass in one transformed paired-divisor family.  It is zero
as soon as any selected divisor is nonsquarefree. -/
noncomputable def pairedDivisorMoebiusMass
    {κ : Type*} [Fintype κ]
    (z : κ → ℕ × ℕ) : ℝ :=
  (∏ q, |(ArithmeticFunction.moebius (z q).1 : ℝ)|) *
    ∏ q, |(ArithmeticFunction.moebius (z q).2 : ℝ)|

theorem pairedDivisorMoebiusMass_nonneg
    {κ : Type*} [Fintype κ]
    (z : κ → ℕ × ℕ) :
    0 ≤ pairedDivisorMoebiusMass z := by
  unfold pairedDivisorMoebiusMass
  positivity

/-- The arithmetic `L¹` mass which is actually paid by pointwise triangle
domination.  It retains the carry Euler average and all Möbius zeros. -/
noncomputable def selectedCFZCarryFourierCoefficientMass
    {k N : ℕ} [NeZero N]
    (R W b : ℕ) (e : LinearFormsExponent k) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices
        (SelectedCFZFormIndex e) R,
    |selectedCFZCarryBlockEulerAverage
        (N := N) e W b z| *
      pairedDivisorMoebiusMass z

theorem selectedCFZCarryFourierCoefficientMass_nonneg
    {k N : ℕ} [NeZero N]
    (R W b : ℕ) (e : LinearFormsExponent k) :
    0 ≤ selectedCFZCarryFourierCoefficientMass
      (N := N) R W b e := by
  unfold selectedCFZCarryFourierCoefficientMass
  exact Finset.sum_nonneg fun z _ => mul_nonneg
    (abs_nonneg _) (pairedDivisorMoebiusMass_nonneg z)

/-! ## Elementary bounds for the retained arithmetic coefficients -/

/-- Every finite affine common-zero density is at most one. -/
theorem affineFamilyZeroDensity_le_one
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (s : Finset κ) :
    affineFamilyZeroDensity p forms s ≤ 1 := by
  rw [affineFamilyZeroDensity_eq_card]
  apply (div_le_one (by positivity)).2
  exact_mod_cast
    (affineFamilyCommonZeroFinset p forms s).card_le_univ

theorem selectedCFZCarryEulerProductAtBlock_nonneg
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (a : FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)) :
    0 ≤ selectedCFZCarryEulerProductAtBlock
      (N := N) W b e z a := by
  unfold selectedCFZCarryEulerProductAtBlock
  exact Finset.prod_nonneg fun p _ =>
    affineFamilyZeroDensity_nonneg
      (p : ℕ)
      (cfzCarryAdjustedFamilyAtBlock
        (N := N) (pairedDivisorLcm z) W b
        (fun q : SelectedCFZFormIndex e => q.1)
        (fun v => (a v : ℕ)))
      (pairedPrimeSupport z p)

theorem selectedCFZCarryEulerProductAtBlock_le_one
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (a : FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)) :
    selectedCFZCarryEulerProductAtBlock
      (N := N) W b e z a ≤ 1 := by
  unfold selectedCFZCarryEulerProductAtBlock
  apply Finset.prod_le_one
  · intro p _hp
    exact affineFamilyZeroDensity_nonneg
      (p : ℕ)
      (cfzCarryAdjustedFamilyAtBlock
        (N := N) (pairedDivisorLcm z) W b
        (fun q : SelectedCFZFormIndex e => q.1)
        (fun v => (a v : ℕ)))
      (pairedPrimeSupport z p)
  · intro p _hp
    exact affineFamilyZeroDensity_le_one
      (p : ℕ)
      (cfzCarryAdjustedFamilyAtBlock
        (N := N) (pairedDivisorLcm z) W b
        (fun q : SelectedCFZFormIndex e => q.1)
        (fun v => (a v : ℕ)))
      (pairedPrimeSupport z p)

theorem selectedCFZCarryBlockEulerAverage_nonneg
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ) :
    0 ≤ selectedCFZCarryBlockEulerAverage
      (N := N) e W b z := by
  rw [selectedCFZCarryBlockEulerAverage_eq_mean_productAtBlock]
  exact mean_nonneg fun a =>
    selectedCFZCarryEulerProductAtBlock_nonneg W b e z a

/-- In particular every carry-block arithmetic coefficient lies in the
closed unit interval, without any good-prime hypothesis. -/
theorem selectedCFZCarryBlockEulerAverage_le_one
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ) :
    selectedCFZCarryBlockEulerAverage
      (N := N) e W b z ≤ 1 := by
  rw [selectedCFZCarryBlockEulerAverage_eq_mean_productAtBlock]
  let α :=
    FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)
  rcases isEmpty_or_nonempty α with hα | hα
  · letI : IsEmpty α := hα
    simp [mean]
  · letI : Nonempty α := hα
    exact mean_le_of_le_const fun a =>
      selectedCFZCarryEulerProductAtBlock_le_one W b e z a

theorem abs_selectedCFZCarryBlockEulerAverage_le_one
    {k N : ℕ} [NeZero N]
    (W b : ℕ) (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ) :
    |selectedCFZCarryBlockEulerAverage
      (N := N) e W b z| ≤ 1 := by
  rw [abs_of_nonneg
    (selectedCFZCarryBlockEulerAverage_nonneg W b e z)]
  exact selectedCFZCarryBlockEulerAverage_le_one W b e z

/-! ## Harmonic LCM gain when `W` covers the exceptional primes -/

/-- At a covered good prime, every nonempty selected support costs at
least one factor `p⁻¹`; supports of size at least two in fact cost
`p⁻²`. -/
theorem selectedCFZCarryBlockPrimeLocalDensity_le_inv
    {k N W : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k) (b : ℕ)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (p : (pairedDivisorLcm z).primeFactors)
    (hpW : ¬(p : ℕ) ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ))
    (a : CFZVariable k → ℕ) :
    affineFamilyZeroDensity (p : ℕ)
        (cfzCarryAdjustedFamilyAtBlock
          (N := N) (pairedDivisorLcm z) W b
          (fun q : SelectedCFZFormIndex e => q.1) a)
        (pairedPrimeSupport z p) ≤
      (1 : ℝ) / (p : ℝ) := by
  have hpSupport :
      (pairedPrimeSupport z (p : ℕ)).Nonempty :=
    ((mem_primeFactors_pairedDivisorLcm_iff
      hz (p : ℕ)).mp p.2).2
  by_cases hone : (pairedPrimeSupport z p).card = 1
  · rw [selectedCFZCarryBlockPrimeLocalDensity_eq_inv_of_card_eq_one
      (N := N) (W := W) hk e b z p hpW hlarge a hone]
  · have htwo : 2 ≤ (pairedPrimeSupport z p).card := by
      have hpos := hpSupport.card_pos
      omega
    have hnontrivial :
        (pairedPrimeSupport z p).Nontrivial :=
      Finset.one_lt_card_iff_nontrivial.mp htwo
    calc
      affineFamilyZeroDensity (p : ℕ)
          (cfzCarryAdjustedFamilyAtBlock
            (N := N) (pairedDivisorLcm z) W b
            (fun q : SelectedCFZFormIndex e => q.1) a)
          (pairedPrimeSupport z p) ≤
          (1 : ℝ) / (p : ℝ) ^ 2 :=
        selectedCFZCarryBlockPrimeLocalDensity_le_inv_sq_of_nontrivial
          (N := N) (W := W)
          hk e b z p hpW hlarge a hnontrivial
      _ ≤ (1 : ℝ) / (p : ℝ) := by
        apply one_div_le_one_div_of_le
        · exact_mod_cast
            (Nat.prime_of_mem_primeFactors p.2).pos
        · have hpone : (1 : ℝ) ≤ (p : ℝ) := by
            exact_mod_cast
              (Nat.prime_of_mem_primeFactors p.2).one_le
          nlinarith

/-- For a squarefree natural, the product of reciprocal prime factors is
the reciprocal of the natural itself. -/
theorem prod_inv_primeFactors_eq_inv_of_squarefree
    {D : ℕ} (hD : Squarefree D) :
    (∏ p : D.primeFactors, (1 : ℝ) / (p : ℝ)) =
      (1 : ℝ) / (D : ℝ) := by
  calc
    (∏ p : D.primeFactors, (1 : ℝ) / (p : ℝ)) =
        ∏ p ∈ D.primeFactors, (1 : ℝ) / (p : ℝ) :=
      Finset.prod_coe_sort D.primeFactors
        (fun p : ℕ => (1 : ℝ) / (p : ℝ))
    _ = (1 : ℝ) / (D : ℝ) := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const_one, one_div]
      have hprod :
          (∏ p ∈ D.primeFactors, (p : ℝ)) = (D : ℝ) := by
        have hnat := Nat.prod_primeFactors_of_squarefree hD
        have hreal := congrArg (fun n : ℕ => (n : ℝ)) hnat
        push_cast at hreal
        exact hreal
      rw [hprod]

/-- Under the usual exceptional-prime coverage hypothesis, a squarefree
block Euler product is bounded by the reciprocal of its global paired
LCM.  If the LCM contains a prime dividing `W`, the product is exactly
zero; otherwise every prime contributes at most `p⁻¹`. -/
theorem selectedCFZCarryEulerProductAtBlock_le_inv_lcm
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (hlarge :
      ∀ p : (pairedDivisorLcm z).primeFactors,
        ¬(p : ℕ) ∣ W →
          exceptionalPrimeBound
              (fun q : CFZFormIndex k => cfzAffineForm q) <
            (p : ℕ))
    (a : FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)) :
    selectedCFZCarryEulerProductAtBlock
        (N := N) W b e z a ≤
      (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
  classical
  by_cases hsmall :
      ∃ p : (pairedDivisorLcm z).primeFactors,
        (p : ℕ) ∣ W
  · obtain ⟨p, hpW⟩ := hsmall
    rw [selectedCFZCarryEulerProductAtBlock_eq_zero_of_prime_dvd
      (N := N) b e z hz p hpW hWb a]
    positivity
  · push Not at hsmall
    unfold selectedCFZCarryEulerProductAtBlock
    calc
      (∏ p : (pairedDivisorLcm z).primeFactors,
          affineFamilyZeroDensity (p : ℕ)
            (cfzCarryAdjustedFamilyAtBlock
              (N := N) (pairedDivisorLcm z) W b
              (fun q : SelectedCFZFormIndex e => q.1)
              (fun v => (a v : ℕ)))
            (pairedPrimeSupport z p)) ≤
          ∏ p : (pairedDivisorLcm z).primeFactors,
            (1 : ℝ) / (p : ℝ) := by
        apply Finset.prod_le_prod
        · intro p _hp
          exact affineFamilyZeroDensity_nonneg
            (p : ℕ)
            (cfzCarryAdjustedFamilyAtBlock
              (N := N) (pairedDivisorLcm z) W b
              (fun q : SelectedCFZFormIndex e => q.1)
              (fun v => (a v : ℕ)))
            (pairedPrimeSupport z p)
        · intro p _hp
          exact selectedCFZCarryBlockPrimeLocalDensity_le_inv
            (N := N) (W := W)
            hk e b z hz p (hsmall p)
            (hlarge p (hsmall p))
            (fun v => (a v : ℕ))
      _ = (1 : ℝ) / (pairedDivisorLcm z : ℝ) :=
        prod_inv_primeFactors_eq_inv_of_squarefree
          (squarefree_pairedDivisorLcm hz)

/-- Averaging the preceding pointwise bound over quotient blocks preserves
the reciprocal-LCM gain. -/
theorem selectedCFZCarryBlockEulerAverage_le_inv_lcm
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (hlarge :
      ∀ p : (pairedDivisorLcm z).primeFactors,
        ¬(p : ℕ) ∣ W →
          exceptionalPrimeBound
              (fun q : CFZFormIndex k => cfzAffineForm q) <
            (p : ℕ)) :
    selectedCFZCarryBlockEulerAverage
        (N := N) e W b z ≤
      (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
  rw [selectedCFZCarryBlockEulerAverage_eq_mean_productAtBlock]
  let α :=
    FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)
  rcases isEmpty_or_nonempty α with hα | hα
  · letI : IsEmpty α := hα
    simp [mean]
  · letI : Nonempty α := hα
    exact mean_le_of_le_const fun a =>
      selectedCFZCarryEulerProductAtBlock_le_inv_lcm
        (N := N) hk hWb e z hz hlarge a

/-- Absolute-value form used in the Fourier coefficient mass. -/
theorem abs_selectedCFZCarryBlockEulerAverage_le_inv_lcm
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k)
    (z : SelectedCFZFormIndex e → ℕ × ℕ)
    (hz : SquarefreePairedDivisorChoice z)
    (hlarge :
      ∀ p : (pairedDivisorLcm z).primeFactors,
        ¬(p : ℕ) ∣ W →
          exceptionalPrimeBound
              (fun q : CFZFormIndex k => cfzAffineForm q) <
            (p : ℕ)) :
    |selectedCFZCarryBlockEulerAverage
        (N := N) e W b z| ≤
      (1 : ℝ) / (pairedDivisorLcm z : ℝ) := by
  rw [abs_of_nonneg
    (selectedCFZCarryBlockEulerAverage_nonneg W b e z)]
  exact selectedCFZCarryBlockEulerAverage_le_inv_lcm
    (N := N) hk hWb e z hz hlarge

/-- Nonzero transformed Möbius mass is exactly enough to recover
squarefreeness of every selected divisor. -/
theorem squarefreePairedDivisorChoice_of_moebiusMass_ne_zero
    {κ : Type*} [Fintype κ]
    (z : κ → ℕ × ℕ)
    (hz : pairedDivisorMoebiusMass z ≠ 0) :
    SquarefreePairedDivisorChoice z := by
  intro q
  have hprod := mul_ne_zero_iff.mp hz
  have hleftR :
      |(ArithmeticFunction.moebius (z q).1 : ℝ)| ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod.1) q (Finset.mem_univ q)
  have hrightR :
      |(ArithmeticFunction.moebius (z q).2 : ℝ)| ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hprod.2) q (Finset.mem_univ q)
  have hleftCast :
      (ArithmeticFunction.moebius (z q).1 : ℝ) ≠ 0 :=
    abs_ne_zero.mp hleftR
  have hrightCast :
      (ArithmeticFunction.moebius (z q).2 : ℝ) ≠ 0 :=
    abs_ne_zero.mp hrightR
  have hleft :
      ArithmeticFunction.moebius (z q).1 ≠ 0 := by
    exact_mod_cast hleftCast
  have hright :
      ArithmeticFunction.moebius (z q).2 ≠ 0 := by
    exact_mod_cast hrightCast
  exact
    ⟨ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hleft,
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hright⟩

/-- The harmonic LCM mass left after using the primewise `p⁻¹` gain.
Unlike the raw choice count, this is naturally controlled by a finite
prime-support Euler product.  The next arithmetic module should prove

`pairedDivisorHarmonicLcmMass R ≤
  ∏ p ∈ primesLE R, (1 + (2 ^ (2 * card κ) - 1) / p)`.

Each local factor simply records the empty support and the
`2 ^ (2 * card κ) - 1` nonempty choices of occurrences of `p`. -/
noncomputable def pairedDivisorHarmonicLcmMass
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) : ℝ :=
  ∑ z ∈ smoothDivisorFamilyChoices κ R,
    ((1 : ℝ) / (pairedDivisorLcm z : ℝ)) *
      pairedDivisorMoebiusMass z

theorem pairedDivisorHarmonicLcmMass_nonneg
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (R : ℕ) :
    0 ≤ pairedDivisorHarmonicLcmMass (κ := κ) R := by
  unfold pairedDivisorHarmonicLcmMass
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg (by positivity)
      (pairedDivisorMoebiusMass_nonneg z)

/-- The exact Fourier coefficient mass is bounded by the harmonic LCM
mass whenever every prime outside `W` lies above the exceptional cutoff.
This is the crucial improvement over `R ^ (2m)`. -/
theorem selectedCFZCarryFourierCoefficientMass_le_harmonicLcmMass
    {k N W b : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k) (R : ℕ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p) :
    selectedCFZCarryFourierCoefficientMass
        (N := N) R W b e ≤
      pairedDivisorHarmonicLcmMass
        (κ := SelectedCFZFormIndex e) R := by
  classical
  unfold selectedCFZCarryFourierCoefficientMass
    pairedDivisorHarmonicLcmMass
  apply Finset.sum_le_sum
  intro z hz
  by_cases hmass : pairedDivisorMoebiusMass z = 0
  · simp [hmass]
  · have hsquarefree :=
      squarefreePairedDivisorChoice_of_moebiusMass_ne_zero z hmass
    have hlarge :
        ∀ p : (pairedDivisorLcm z).primeFactors,
          ¬(p : ℕ) ∣ W →
            exceptionalPrimeBound
                (fun q : CFZFormIndex k => cfzAffineForm q) <
              (p : ℕ) := by
      intro p hpW
      exact hcover (p : ℕ)
        (Nat.prime_of_mem_primeFactors p.2) hpW
    exact mul_le_mul_of_nonneg_right
      (abs_selectedCFZCarryBlockEulerAverage_le_inv_lcm
        (N := N) hk hWb e z hsquarefree hlarge)
      (pairedDivisorMoebiusMass_nonneg z)

/-- A primorial through the exceptional cutoff supplies the preceding
coverage hypothesis automatically. -/
theorem selectedCFZ_exceptionalPrime_covered_by_primorial
    {k w p : ℕ}
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hp : p.Prime) (hpW : ¬p ∣ primorial w) :
    exceptionalPrimeBound
        (fun q : CFZFormIndex k => cfzAffineForm q) < p := by
  by_contra hnot
  have hpw : p ≤ w := by omega
  exact hpW ((hp.dvd_primorial_iff).2 hpw)

/-- Primorial specialization of the harmonic-LCM coefficient bound. -/
theorem selectedCFZCarryFourierCoefficientMass_le_harmonicLcmMass_primorial
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k) (R : ℕ) :
    selectedCFZCarryFourierCoefficientMass
        (N := N) R (primorial w) b e ≤
      pairedDivisorHarmonicLcmMass
        (κ := SelectedCFZFormIndex e) R := by
  exact selectedCFZCarryFourierCoefficientMass_le_harmonicLcmMass
    (N := N) hk hwb e R
    (fun p hp hpW =>
      selectedCFZ_exceptionalPrime_covered_by_primorial
        hbound hp hpW)

/-! ## The universal paired Schwartz density -/

/-- Product of the absolute cutoff transforms on both Fourier sides. -/
noncomputable def selectedCFZPairedFourierAbsoluteDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℝ :=
  χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
    χ.fourierProductMomentDensity (fun _ => 0) tu.2

theorem selectedCFZPairedFourierAbsoluteDensity_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    0 ≤ χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  unfold selectedCFZPairedFourierAbsoluteDensity
  exact mul_nonneg
    (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
    (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2)

theorem integrable_selectedCFZPairedFourierAbsoluteDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    Integrable
      (χ.selectedCFZPairedFourierAbsoluteDensity e)
      (volume.prod volume) := by
  unfold selectedCFZPairedFourierAbsoluteDensity
  exact
    (χ.integrable_fourierProductMomentDensity (fun _ => 0)).mul_prod
      (χ.integrable_fourierProductMomentDensity (fun _ => 0))

/-- Absolute Schwartz mass outside the exact paired box used by the carry
Fourier bridge. -/
noncomputable def selectedCFZPairedFourierAbsoluteTail
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (T : ℝ) : ℝ :=
  ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
    χ.selectedCFZPairedFourierAbsoluteDensity e tu
    ∂(volume.prod volume)

theorem selectedCFZPairedFourierAbsoluteTail_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (T : ℝ) :
    0 ≤ χ.selectedCFZPairedFourierAbsoluteTail e T := by
  unfold selectedCFZPairedFourierAbsoluteTail
  exact setIntegral_nonneg
    (measurableSet_selectedCFZPairedFourierBox e T).compl
    fun tu _ => χ.selectedCFZPairedFourierAbsoluteDensity_nonneg e tu

/-- The product of the two coordinatewise sup-norm boxes is exactly the
closed ball for the product sup norm. -/
theorem selectedCFZPairedFourierBox_eq_closedBall
    {k : ℕ} (e : LinearFormsExponent k) (T : ℝ) :
    selectedCFZPairedFourierBox e T =
      Metric.closedBall
        (0 :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ))
        T := by
  ext tu
  simp [selectedCFZPairedFourierBox, fourierProductBox,
    Metric.mem_closedBall, Prod.norm_def]

/-- The universal paired Schwartz tail vanishes as the box expands. -/
theorem tendsto_selectedCFZPairedFourierAbsoluteTail_atTop
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    Tendsto (χ.selectedCFZPairedFourierAbsoluteTail e)
      atTop (𝓝 0) := by
  have hcover :
      AECover (volume.prod volume) atTop
        (fun T : ℝ => selectedCFZPairedFourierBox e T) := by
    have hclosed :
        AECover (volume.prod volume) atTop
          (fun T : ℝ =>
            Metric.closedBall
              (0 :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ))
              T) :=
      aecover_closedBall tendsto_id
    convert hclosed using 1
    funext T
    exact selectedCFZPairedFourierBox_eq_closedBall e T
  have hinside :
      Tendsto
        (fun T : ℝ =>
          ∫ tu in selectedCFZPairedFourierBox e T,
            χ.selectedCFZPairedFourierAbsoluteDensity e tu
            ∂(volume.prod volume))
        atTop
        (𝓝 (∫ tu,
          χ.selectedCFZPairedFourierAbsoluteDensity e tu
          ∂(volume.prod volume))) :=
    hcover.integral_tendsto_of_countably_generated
      (χ.integrable_selectedCFZPairedFourierAbsoluteDensity e)
  have hconst :
      Tendsto
        (fun _ : ℝ =>
          ∫ tu,
            χ.selectedCFZPairedFourierAbsoluteDensity e tu
            ∂(volume.prod volume))
        atTop
        (𝓝 (∫ tu,
          χ.selectedCFZPairedFourierAbsoluteDensity e tu
          ∂(volume.prod volume))) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          (∫ tu,
            χ.selectedCFZPairedFourierAbsoluteDensity e tu
            ∂(volume.prod volume)) -
          ∫ tu in selectedCFZPairedFourierBox e T,
            χ.selectedCFZPairedFourierAbsoluteDensity e tu
            ∂(volume.prod volume))
        atTop (𝓝 0) := by
    convert hconst.sub hinside using 1
    all_goals simp
  refine hsub.congr' (Filter.Eventually.of_forall fun T => ?_)
  unfold selectedCFZPairedFourierAbsoluteTail
  symm
  exact setIntegral_compl
    (measurableSet_selectedCFZPairedFourierBox e T)
    (χ.integrable_selectedCFZPairedFourierAbsoluteDensity e)

/-- In particular the paired tail vanishes at the conventional radius
`sqrt (log R)`. -/
theorem tendsto_selectedCFZPairedFourierAbsoluteTail_sqrt_log
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) :=
  (χ.tendsto_selectedCFZPairedFourierAbsoluteTail_atTop e).comp
    tendsto_sqrt_log_nat_atTop

/-! ## Pointwise transform domination -/

/-- The divisor phase lies in the closed unit ball for every natural
divisor.  The prime-specialized version in the Euler-product API is enough
for local factors; here the finite divisor transform also needs composite
divisors. -/
theorem norm_divisorMultiplicativePhase_le_one_general
    (R d : ℕ) (t : ℝ) :
    ‖divisorMultiplicativePhase R d t‖ ≤ 1 := by
  by_cases hR : 2 ≤ R
  · rw [divisorMultiplicativePhase,
      norm_cutoffMultiplicativePhase]
    have hlogd : 0 ≤ Real.log (d : ℝ) := by
      rcases d.eq_zero_or_pos with rfl | hd
      · simp
      · exact Real.log_nonneg (by exact_mod_cast hd)
    have hlogR : 0 ≤ Real.log (R : ℝ) :=
      Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ R by omega))
    have hdiv :
        0 ≤ Real.log (d : ℝ) / Real.log (R : ℝ) :=
      div_nonneg hlogd hlogR
    calc
      Real.exp (-(Real.log (d : ℝ) / Real.log (R : ℝ))) ≤
          Real.exp 0 :=
        Real.exp_le_exp.mpr (neg_nonpos.mpr hdiv)
      _ = 1 := Real.exp_zero
  · have hsmall : R = 0 ∨ R = 1 := by omega
    rcases hsmall with rfl | rfl <;>
      simp [divisorMultiplicativePhase,
        norm_cutoffMultiplicativePhase]

/-- One transformed side is bounded by its exact Möbius mass times the
unweighted product of absolute cutoff transforms. -/
theorem norm_transformedDivisorFamilySide_le_moebiusMass
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) (t : κ → ℝ) :
    ‖χ.transformedDivisorFamilySide R d t‖ ≤
      (∏ q, |(ArithmeticFunction.moebius (d q) : ℝ)|) *
        χ.fourierProductMomentDensity (fun _ => 0) t := by
  unfold transformedDivisorFamilySide
  rw [norm_prod]
  calc
    (∏ q,
        ‖(ArithmeticFunction.moebius (d q) : ℂ) *
            χ.cutoffFourierTransform (t q) *
              divisorMultiplicativePhase R (d q) (t q)‖) ≤
        ∏ q,
          |(ArithmeticFunction.moebius (d q) : ℝ)| *
            ‖χ.cutoffFourierTransform (t q)‖ := by
      apply Finset.prod_le_prod
      · intro q _hq
        positivity
      · intro q _hq
        rw [norm_mul, norm_mul]
        calc
          ‖(ArithmeticFunction.moebius (d q) : ℂ)‖ *
                ‖χ.cutoffFourierTransform (t q)‖ *
              ‖divisorMultiplicativePhase R (d q) (t q)‖ ≤
              (|(ArithmeticFunction.moebius (d q) : ℝ)| *
                ‖χ.cutoffFourierTransform (t q)‖) * 1 := by
            gcongr
            · simp
            · exact norm_divisorMultiplicativePhase_le_one_general
                R (d q) (t q)
          _ = _ := mul_one _
    _ =
        (∏ q, |(ArithmeticFunction.moebius (d q) : ℝ)|) *
          χ.fourierProductMomentDensity (fun _ => 0) t := by
      rw [Finset.prod_mul_distrib]
      simp [fourierProductMomentDensity, fourierMomentDensity]

/-- The paired transform inherits the product of the two exact Möbius
masses. -/
theorem norm_transformedPairedDivisorFamily_le
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ)
    (tu : (κ → ℝ) × (κ → ℝ)) :
    ‖χ.transformedPairedDivisorFamily R z tu‖ ≤
      pairedDivisorMoebiusMass z *
        (χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
          χ.fourierProductMomentDensity (fun _ => 0) tu.2) := by
  unfold transformedPairedDivisorFamily pairedDivisorMoebiusMass
  rw [norm_mul]
  calc
    ‖χ.transformedDivisorFamilySide R (fun q => (z q).1) tu.1‖ *
          ‖χ.transformedDivisorFamilySide R (fun q => (z q).2) tu.2‖ ≤
        ((∏ q, |(ArithmeticFunction.moebius (z q).1 : ℝ)|) *
            χ.fourierProductMomentDensity (fun _ => 0) tu.1) *
          ((∏ q, |(ArithmeticFunction.moebius (z q).2 : ℝ)|) *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2) := by
      exact mul_le_mul
        (χ.norm_transformedDivisorFamilySide_le_moebiusMass
          R (fun q => (z q).1) tu.1)
        (χ.norm_transformedDivisorFamilySide_le_moebiusMass
          R (fun q => (z q).2) tu.2)
        (norm_nonneg _)
        (mul_nonneg
          (Finset.prod_nonneg fun q _ => abs_nonneg _)
          (χ.fourierProductMomentDensity_nonneg
            (fun _ => 0) tu.1))
    _ = _ := by ring

/-- Pointwise domination of the full carry integrand.  No raw divisor-choice
count appears: all arithmetic loss is retained in the exact coefficient
mass. -/
theorem norm_selectedCFZCarryFourierIntegrand_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖χ.selectedCFZCarryFourierIntegrand
        (N := N) R W b e tu‖ ≤
      selectedCFZCarryFourierCoefficientMass
          (N := N) R W b e *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  rw [χ.selectedCFZCarryFourierIntegrand_eq_sum
    (N := N) R W b e tu]
  calc
    ‖∑ z ∈ smoothDivisorFamilyChoices
          (SelectedCFZFormIndex e) R,
        (selectedCFZCarryBlockEulerAverage
            (N := N) e W b z : ℂ) *
          χ.transformedPairedDivisorFamily R z tu‖ ≤
        ∑ z ∈ smoothDivisorFamilyChoices
            (SelectedCFZFormIndex e) R,
          ‖(selectedCFZCarryBlockEulerAverage
              (N := N) e W b z : ℂ) *
            χ.transformedPairedDivisorFamily R z tu‖ :=
      norm_sum_le _ _
    _ ≤
        ∑ z ∈ smoothDivisorFamilyChoices
            (SelectedCFZFormIndex e) R,
          (|selectedCFZCarryBlockEulerAverage
              (N := N) e W b z| *
            pairedDivisorMoebiusMass z) *
              χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
      apply Finset.sum_le_sum
      intro z hz
      rw [norm_mul]
      have hzbound :=
        χ.norm_transformedPairedDivisorFamily_le
          R z tu
      unfold selectedCFZPairedFourierAbsoluteDensity
      simpa [Real.norm_eq_abs, mul_assoc] using
        (mul_le_mul_of_nonneg_left hzbound
          (norm_nonneg
            (selectedCFZCarryBlockEulerAverage
              (N := N) e W b z : ℂ)))
    _ =
        selectedCFZCarryFourierCoefficientMass
            (N := N) R W b e *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
      unfold selectedCFZCarryFourierCoefficientMass
      simp_rw [mul_assoc]
      rw [Finset.sum_mul]
      simp only [mul_assoc]

/-! ## Complementary-integral and scaled bounds -/

/-- The complementary Fourier integral is bounded by the exact arithmetic
coefficient mass times a universal paired Schwartz tail. -/
theorem norm_integral_selectedCFZCarryFourierIntegrand_compl_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) (T : ℝ) :
    ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
        χ.selectedCFZCarryFourierIntegrand
          (N := N) R W b e tu
        ∂(volume.prod volume)‖ ≤
      selectedCFZCarryFourierCoefficientMass
          (N := N) R W b e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  have hdom :
      ∀ᵐ tu ∂(volume.prod volume).restrict
          (selectedCFZPairedFourierBox e T)ᶜ,
        ‖χ.selectedCFZCarryFourierIntegrand
            (N := N) R W b e tu‖ ≤
          selectedCFZCarryFourierCoefficientMass
              (N := N) R W b e *
            χ.selectedCFZPairedFourierAbsoluteDensity e tu :=
    ae_of_all _ fun tu =>
      χ.norm_selectedCFZCarryFourierIntegrand_le R W b e tu
  have hbound :=
    norm_integral_le_of_norm_le
      ((χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
        (selectedCFZCarryFourierCoefficientMass
          (N := N) R W b e) |>.integrableOn)
      hdom
  simpa [selectedCFZPairedFourierAbsoluteTail,
    integral_const_mul] using hbound

/-- The same estimate with exactly the two Selberg prefactors from
`selectedCFZCarryBlockEulerMainTerm_eq_fourierBox_add_compl`. -/
theorem norm_scaled_integral_selectedCFZCarryFourierIntegrand_compl_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) (T : ℝ) :
    ‖(normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.selectedCFZCarryFourierIntegrand
            (N := N) R W b e tu
          ∂(volume.prod volume))‖ ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        |Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        selectedCFZCarryFourierCoefficientMass
            (N := N) R W b e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have htail :=
    χ.norm_integral_selectedCFZCarryFourierIntegrand_compl_le
      (N := N) R W b e T
  calc
    |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        (|Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        ‖∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.selectedCFZCarryFourierIntegrand
            (N := N) R W b e tu
          ∂(volume.prod volume)‖) ≤
      |normalizedSelbergScale χ.normalizer R W| ^
          Fintype.card (SelectedCFZFormIndex e) *
        (|Real.log R ^ 2| ^
          Fintype.card (SelectedCFZFormIndex e) *
        (selectedCFZCarryFourierCoefficientMass
            (N := N) R W b e *
          χ.selectedCFZPairedFourierAbsoluteTail e T)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htail
          (pow_nonneg (abs_nonneg _) _))
        (pow_nonneg (abs_nonneg _) _)
    _ = _ := by ring

/-! ## The exact remaining arithmetic hypothesis -/

/-- All non-Schwartz factors in the complementary-integral bound.  A
prime-support argument should prove that this is bounded in the intended
primorial/Selberg regime.  Keeping it named prevents an accidental fallback
to the raw `R ^ (2m)` choice count. -/
noncomputable def selectedCFZCarryScaledFourierCoefficientMass
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  |normalizedSelbergScale χ.normalizer R W| ^
      Fintype.card (SelectedCFZFormIndex e) *
    |Real.log R ^ 2| ^
      Fintype.card (SelectedCFZFormIndex e) *
    selectedCFZCarryFourierCoefficientMass
      (N := N) R W b e

theorem selectedCFZCarryScaledFourierCoefficientMass_nonneg
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZCarryScaledFourierCoefficientMass
      (N := N) R W b e := by
  unfold selectedCFZCarryScaledFourierCoefficientMass
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))
    (selectedCFZCarryFourierCoefficientMass_nonneg
      (N := N) R W b e)

/-- Selberg-scaled form of the harmonic LCM mass.  This no longer depends
on the cyclic carry parameters `N` and `b`. -/
noncomputable def selectedCFZScaledHarmonicLcmMass
    {k : ℕ}
    (χ : SmoothSieveCutoff) (R W : ℕ)
    (e : LinearFormsExponent k) : ℝ :=
  |normalizedSelbergScale χ.normalizer R W| ^
      Fintype.card (SelectedCFZFormIndex e) *
    |Real.log R ^ 2| ^
      Fintype.card (SelectedCFZFormIndex e) *
    pairedDivisorHarmonicLcmMass
      (κ := SelectedCFZFormIndex e) R

theorem selectedCFZScaledHarmonicLcmMass_nonneg
    {k : ℕ}
    (χ : SmoothSieveCutoff) (R W : ℕ)
    (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZScaledHarmonicLcmMass R W e := by
  unfold selectedCFZScaledHarmonicLcmMass
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))
    (pairedDivisorHarmonicLcmMass_nonneg R)

/-- Exceptional-prime coverage upgrades the exact scaled coefficient mass
to the scaled harmonic LCM mass. -/
theorem selectedCFZCarryScaledFourierCoefficientMass_le_scaledHarmonicLcmMass
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k) (R : ℕ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p) :
    χ.selectedCFZCarryScaledFourierCoefficientMass
        (N := N) R W b e ≤
      χ.selectedCFZScaledHarmonicLcmMass R W e := by
  unfold selectedCFZCarryScaledFourierCoefficientMass
    selectedCFZScaledHarmonicLcmMass
  exact mul_le_mul_of_nonneg_left
    (selectedCFZCarryFourierCoefficientMass_le_harmonicLcmMass
      (N := N) hk hWb e R hcover)
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))

/-- Norm of the fully scaled complementary contribution at radius `T`. -/
noncomputable def selectedCFZCarryScaledFourierTailNorm
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) (T : ℝ) : ℝ :=
  ‖(normalizedSelbergScale χ.normalizer R W : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      (((Real.log R ^ 2 : ℝ) : ℂ) ^
        Fintype.card (SelectedCFZFormIndex e) *
      ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
        χ.selectedCFZCarryFourierIntegrand
          (N := N) R W b e tu
        ∂(volume.prod volume))‖

theorem selectedCFZCarryScaledFourierTailNorm_nonneg
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) (T : ℝ) :
    0 ≤ χ.selectedCFZCarryScaledFourierTailNorm
      (N := N) R W b e T := by
  unfold selectedCFZCarryScaledFourierTailNorm
  exact norm_nonneg _

/-- Clean factorized form of the scaled tail estimate. -/
theorem selectedCFZCarryScaledFourierTailNorm_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) (T : ℝ) :
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R W b e T ≤
      χ.selectedCFZCarryScaledFourierCoefficientMass
          (N := N) R W b e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  unfold selectedCFZCarryScaledFourierTailNorm
    selectedCFZCarryScaledFourierCoefficientMass
  simpa only [mul_assoc] using
    χ.norm_scaled_integral_selectedCFZCarryFourierIntegrand_compl_le
      (N := N) R W b e T

/-- The useful arithmetic version of the pointwise tail bound: after
exceptional-prime coverage, only the harmonic LCM mass remains. -/
theorem selectedCFZCarryScaledFourierTailNorm_le_scaledHarmonicLcmMass
    {k N W b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k) (hWb : W.Coprime b)
    (e : LinearFormsExponent k) (R : ℕ)
    (hcover :
      ∀ p : ℕ, p.Prime → ¬p ∣ W →
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (T : ℝ) :
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R W b e T ≤
      χ.selectedCFZScaledHarmonicLcmMass R W e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  calc
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R W b e T ≤
      χ.selectedCFZCarryScaledFourierCoefficientMass
          (N := N) R W b e *
        χ.selectedCFZPairedFourierAbsoluteTail e T :=
      χ.selectedCFZCarryScaledFourierTailNorm_le
        (N := N) R W b e T
    _ ≤
      χ.selectedCFZScaledHarmonicLcmMass R W e *
        χ.selectedCFZPairedFourierAbsoluteTail e T :=
      mul_le_mul_of_nonneg_right
        (χ.selectedCFZCarryScaledFourierCoefficientMass_le_scaledHarmonicLcmMass
          (N := N) hk hWb e R hcover)
        (χ.selectedCFZPairedFourierAbsoluteTail_nonneg e T)

/-- Primorial version of the preceding pointwise estimate. -/
theorem
    selectedCFZCarryScaledFourierTailNorm_le_scaledHarmonicLcmMass_primorial
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k) (R : ℕ) (T : ℝ) :
    χ.selectedCFZCarryScaledFourierTailNorm
        (N := N) R (primorial w) b e T ≤
      χ.selectedCFZScaledHarmonicLcmMass R (primorial w) e *
        χ.selectedCFZPairedFourierAbsoluteTail e T := by
  exact χ.selectedCFZCarryScaledFourierTailNorm_le_scaledHarmonicLcmMass
    (N := N) hk hwb e R
    (fun p hp hpW =>
      selectedCFZ_exceptionalPrime_covered_by_primorial
        hbound hp hpW)
    T

/-- **Conditional vanishing theorem.**  Once the named arithmetic
coefficient mass is eventually bounded, the fully scaled complementary
integral vanishes at `T = sqrt (log R)`.  Thus the remaining gap is exactly
the eventual boundedness hypothesis below, rather than any analytic Fourier
tail estimate. -/
theorem tendsto_selectedCFZCarryScaledFourierTailNorm_sqrt_log_of_eventually_le
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (W b : ℕ)
    (e : LinearFormsExponent k) (C : ℝ)
    (hMass :
      ∀ᶠ R : ℕ in atTop,
        χ.selectedCFZCarryScaledFourierCoefficientMass
          (N := N) R W b e ≤ C) :
    Tendsto
      (fun R : ℕ =>
        χ.selectedCFZCarryScaledFourierTailNorm
          (N := N) R W b e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  have hupper :
      Tendsto
        (fun R : ℕ =>
          C * χ.selectedCFZPairedFourierAbsoluteTail e
            (Real.sqrt (Real.log R)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (χ.tendsto_selectedCFZPairedFourierAbsoluteTail_sqrt_log e))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R =>
      χ.selectedCFZCarryScaledFourierTailNorm_nonneg
        (N := N) R W b e _
  · filter_upwards [hMass] with R hR
    calc
      χ.selectedCFZCarryScaledFourierTailNorm
          (N := N) R W b e
          (Real.sqrt (Real.log R)) ≤
        χ.selectedCFZCarryScaledFourierCoefficientMass
            (N := N) R W b e *
          χ.selectedCFZPairedFourierAbsoluteTail e
            (Real.sqrt (Real.log R)) :=
        χ.selectedCFZCarryScaledFourierTailNorm_le
          (N := N) R W b e _
      _ ≤
        C * χ.selectedCFZPairedFourierAbsoluteTail e
            (Real.sqrt (Real.log R)) :=
        mul_le_mul_of_nonneg_right hR
          (χ.selectedCFZPairedFourierAbsoluteTail_nonneg e _)
  · exact hupper

/-- **Growing primorial/Selberg regime.**  The cyclic modulus, primorial
cutoff, and reduced residue may all vary with `R`.  The fully scaled tail
still vanishes at `sqrt (log R)` provided the scaled harmonic LCM mass is
eventually bounded.  This isolates the remaining finite-prime-support
estimate in a form independent of the carry decomposition. -/
theorem
    tendsto_selectedCFZCarryScaledFourierTailNorm_sqrt_log_primorial_of_harmonic
    {k : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (Nseq wseq bseq : ℕ → ℕ)
    (hN : ∀ R, Nseq R ≠ 0)
    (hbound :
      ∀ R,
        exceptionalPrimeBound
            (fun q : CFZFormIndex k => cfzAffineForm q) ≤
          wseq R)
    (hcoprime :
      ∀ R, (primorial (wseq R)).Coprime (bseq R))
    (e : LinearFormsExponent k) (C : ℝ)
    (hMass :
      ∀ᶠ R : ℕ in atTop,
        χ.selectedCFZScaledHarmonicLcmMass
          R (primorial (wseq R)) e ≤ C) :
    Tendsto
      (fun R : ℕ =>
        letI : NeZero (Nseq R) := ⟨hN R⟩
        χ.selectedCFZCarryScaledFourierTailNorm
          (N := Nseq R) R (primorial (wseq R)) (bseq R) e
          (Real.sqrt (Real.log R)))
      atTop (𝓝 0) := by
  have hupper :
      Tendsto
        (fun R : ℕ =>
          C * χ.selectedCFZPairedFourierAbsoluteTail e
            (Real.sqrt (Real.log R)))
        atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (χ.tendsto_selectedCFZPairedFourierAbsoluteTail_sqrt_log e))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R => by
      letI : NeZero (Nseq R) := ⟨hN R⟩
      exact χ.selectedCFZCarryScaledFourierTailNorm_nonneg
        (N := Nseq R) R (primorial (wseq R)) (bseq R) e _
  · filter_upwards [hMass] with R hR
    letI : NeZero (Nseq R) := ⟨hN R⟩
    calc
      χ.selectedCFZCarryScaledFourierTailNorm
          (N := Nseq R) R (primorial (wseq R)) (bseq R) e
          (Real.sqrt (Real.log R)) ≤
        χ.selectedCFZScaledHarmonicLcmMass
            R (primorial (wseq R)) e *
          χ.selectedCFZPairedFourierAbsoluteTail e
            (Real.sqrt (Real.log R)) :=
        χ.selectedCFZCarryScaledFourierTailNorm_le_scaledHarmonicLcmMass_primorial
          (N := Nseq R) hk (hbound R) (hcoprime R) e R _
      _ ≤
        C * χ.selectedCFZPairedFourierAbsoluteTail e
            (Real.sqrt (Real.log R)) :=
        mul_le_mul_of_nonneg_right hR
          (χ.selectedCFZPairedFourierAbsoluteTail_nonneg e _)
  · exact hupper

end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem
