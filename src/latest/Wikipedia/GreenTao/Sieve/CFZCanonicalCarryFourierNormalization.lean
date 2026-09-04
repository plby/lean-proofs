import Wikipedia.GreenTao.Sieve.CFZCanonicalEulerCompletionTail
import Wikipedia.GreenTao.Sieve.FixedPrimorialSieveSchedule

/-!
# Fourier normalization for canonical CFZ carry vectors

The canonical divisor expansion freezes one complete integer carry vector,
rather than a divisor-dependent quotient block.  This file gives that
carry-vector model the same local-ratio, Euler-tail, factorization, and
normalized Fourier API as the older carry-block model.

All estimates are uniform in the carry vector.  In particular, no
realizability or positive-density hypothesis is imposed: vectors which do
not occur in a canonical carry cell satisfy the same pointwise arithmetic
statements.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## Packaged canonical carry-vector data -/

/-- The data determining one selected canonical carry-vector Fourier
factor.  The integer carry vector is deliberately unrestricted. -/
structure SelectedCFZCanonicalCarryFourierData (k : ℕ) where
  N : ℕ
  N_neZero : NeZero N
  R : ℕ
  w : ℕ
  b : ℕ
  e : LinearFormsExponent k
  carry : SelectedCFZFormIndex e → ℤ
  t : SelectedCFZFormIndex e → ℝ
  u : SelectedCFZFormIndex e → ℝ

namespace SelectedCFZCanonicalCarryFourierData

/-- The affine family attached directly to the packaged carry vector. -/
def carryAdjustedFamily
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) :
    SelectedCFZFormIndex d.e → AffineForm (CFZVariable k) ℤ :=
  cfzCarryAdjustedFamilyAtVector
    d.N (primorial d.w) d.b
    (fun q : SelectedCFZFormIndex d.e => q.1) d.carry

/-- The arithmetic/zeta ratio at a natural prime. -/
noncomputable def primeArithmeticToZetaLocalRatio
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k)
    (p : Nat.Primes) : ℂ := by
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact
    pairedFourierArithmeticToZetaLocalRatio
      d.R (p : ℕ) d.carryAdjustedFamily d.t d.u

/-- The correction over primes larger than the primorial parameter, with
all primes at most `w` masked to one. -/
noncomputable def largePrimeEulerCorrection
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) : ℂ :=
  ∏' p : Nat.Primes,
    boundedMaskedComplexPrimeLocalFactor
      d.w d.primeArithmeticToZetaLocalRatio p

/-- The complete prime-support series for the packaged carry vector. -/
noncomputable def completePrimeSupportSeries
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) : ℂ :=
  cfzCanonicalCarryCompletePrimeSupportSeries
    d.N (primorial d.w) d.b d.R
    (fun q : SelectedCFZFormIndex d.e => q.1)
    d.carry d.t d.u

end SelectedCFZCanonicalCarryFourierData

/-! ## Direct good-prime geometry -/

/-- Above the exceptional cutoff of the original full CFZ family and
outside `W`, an arbitrary selected carry vector has direct modular
one-form and rank-two geometry.  The affine constants `N`, `b`, and
`carry` are completely unrestricted. -/
theorem selectedCFZCarryAdjustedFamilyAtVector_goodPrime
    {k N W b p : ℕ}
    (hk : 2 ≤ k) (hp : p.Prime) (hpW : ¬p ∣ W)
    (hlarge :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) < p)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ) :
    AffineNonzeroGoodPrime p
        (cfzCarryAdjustedFamilyAtVector
          N W b
          (fun q : SelectedCFZFormIndex e => q.1) carry) ∧
      AffineRankTwoGoodPrime p
        (cfzCarryAdjustedFamilyAtVector
          N W b
          (fun q : SelectedCFZFormIndex e => q.1) carry) := by
  change
    AffineNonzeroGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          cfzCarryAdjustedAffineForm N W b q.1 (carry q)) ∧
      AffineRankTwoGoodPrime p
        (fun q : SelectedCFZFormIndex e =>
          cfzCarryAdjustedAffineForm N W b q.1 (carry q))
  exact
    ⟨affineNonzeroGoodPrime_cfzCarryAdjusted
        N W b
        (fun q : SelectedCFZFormIndex e => q.1) carry
        (selectedCFZAffineNonzeroGoodPrime hk hp hlarge e)
        hpW,
      affineRankTwoGoodPrime_cfzCarryAdjusted
        N W b
        (fun q : SelectedCFZFormIndex e => q.1) carry
        (selectedCFZAffineRankTwoGoodPrime hk hp hlarge e)
        hpW⟩

/-! ## Uniform prime-square control and Euler tail -/

/-- Every packaged canonical carry vector has arithmetic/zeta ratio
`1 + O_k(p⁻²)` above the common `k`-only cutoff. -/
theorem
    norm_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCanonicalCarryFourierData k)
    (hR : 2 ≤ d.R) (p : Nat.Primes)
    (hpW : ¬(p : ℕ) ∣ primorial d.w)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ)) :
    ‖d.primeArithmeticToZetaLocalRatio p - 1‖ ≤
      selectedCFZCarryEulerTailErrorConstant k /
        (p : ℝ) ^ 2 := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  obtain ⟨hnonzero, hrankTwo⟩ :=
    selectedCFZCarryAdjustedFamilyAtVector_goodPrime
      (N := d.N) (W := primorial d.w) (b := d.b)
      hk p.prop hpW horiginal d.e d.carry
  have hfullCut :
      complexZetaModelNonzeroCutoff
          (Fintype.card (CFZFormIndex k)) ≤
        (p : ℕ) :=
    (Nat.le_max_right _ _).trans hlarge.le
  have hselectedCut :
      complexZetaModelNonzeroCutoff
          (Fintype.card (SelectedCFZFormIndex d.e)) ≤
        (p : ℕ) :=
    (complexZetaModelNonzeroCutoff_mono
      (card_selectedCFZFormIndex_le d.e)).trans hfullCut
  have hlocal :=
    norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le_of_goodPrime
      hnonzero hrankTwo hR hselectedCut d.t d.u
  have hconstant :
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card (SelectedCFZFormIndex d.e)) ≤
        selectedCFZCarryEulerTailErrorConstant k :=
    complexArithmeticZetaRatioErrorConstant_mono
      (card_selectedCFZFormIndex_le d.e)
  unfold
    SelectedCFZCanonicalCarryFourierData.primeArithmeticToZetaLocalRatio
    SelectedCFZCanonicalCarryFourierData.carryAdjustedFamily
  exact hlocal.trans
    (div_le_div_of_nonneg_right hconstant
      (sq_nonneg (p : ℝ)))

/-- The masked large-prime correction tends to one uniformly while every
datum other than the ambient `k` is allowed to vary. -/
theorem tendsto_selectedCFZCanonicalCarryLargePrimeEulerCorrection_one
    {α : Type*} {𝓕 : Filter α} {k : ℕ}
    (hk : 2 ≤ k)
    (d : α → SelectedCFZCanonicalCarryFourierData k)
    (hw : Tendsto (fun n => (d n).w) 𝓕 atTop)
    (hR : ∀ᶠ n in 𝓕, 2 ≤ (d n).R) :
    Tendsto
      (fun n => (d n).largePrimeEulerCorrection)
      𝓕 (𝓝 1) := by
  apply
    tendsto_tprod_boundedMaskedComplexPrimeLocalFactor_one
      (selectedCFZCarryEulerTailErrorConstant_nonneg k)
      (fun n => (d n).w)
      (fun n => (d n).primeArithmeticToZetaLocalRatio)
      hw
  filter_upwards
      [hR,
        hw
          (eventually_ge_atTop
            (wTrickedCFZComplexExceptionalBound k))]
    with n hnR hnlarge
  intro p hp
  have hpW : ¬(p : ℕ) ∣ primorial (d n).w := by
    rw [p.prop.dvd_primorial_iff]
    exact Nat.not_le.mpr hp
  exact
    norm_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
      hk (d n) hnR p hpW (hnlarge.trans_lt hp)

/-- Epsilon-threshold form of the preceding uniform tail theorem.  Once
`w` is large enough, every canonical vector and every pair of Fourier
frequencies has correction within `ε` of one. -/
theorem
    exists_uniform_cutoff_selectedCFZCanonicalCarryLargePrimeEulerCorrection_close_one
    {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w₀ : ℕ,
      ∀ d : SelectedCFZCanonicalCarryFourierData k,
        w₀ ≤ d.w →
        2 ≤ d.R →
        ‖d.largePrimeEulerCorrection - 1‖ < ε := by
  by_contra h
  push Not at h
  choose d hdw hdR hfar using h
  have hwtop :
      Tendsto (fun n => (d n).w) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro W
    exact ⟨W, fun n hn => hn.trans (hdw n)⟩
  have hlarge :
      Tendsto
        (fun n => (d n).largePrimeEulerCorrection)
        atTop (𝓝 1) :=
    tendsto_selectedCFZCanonicalCarryLargePrimeEulerCorrection_one
      hk d hwtop (Filter.Eventually.of_forall hdR)
  have hclose :
      ∀ᶠ n in atTop,
        ‖(d n).largePrimeEulerCorrection - 1‖ < ε := by
    have hdist :
        ∀ᶠ n in atTop,
          dist ((d n).largePrimeEulerCorrection) 1 < ε :=
      (Metric.tendsto_nhds.mp hlarge) ε hε
    simpa only [dist_eq_norm] using hdist
  obtain ⟨n, hn⟩ := hclose.exists
  exact (not_lt_of_ge (hfar n)) hn

/-! ## Exact small/large-prime factorization -/

/-- The paired Fourier factor of an arbitrary carry vector is one at a
prime dividing `W`, provided `b` is reduced modulo `W`. -/
theorem pairedFourierLocalFactor_cfzCarryAdjustedFamilyAtVector_eq_one_of_dvd
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k p : ℕ} [NeZero p]
    (N W b : ℕ)
    (hp : p.Prime) (hpW : p ∣ W) (hWb : W.Coprime b)
    (R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ) :
    pairedFourierLocalFactor R p
        (cfzCarryAdjustedFamilyAtVector
          N W b forms carry) t u = 1 := by
  exact
    complexWeightedLocalFactor_cfzCarryAdjusted_eq_one_of_dvd
      N W b hp hpW hWb forms carry
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))

/-- The packaged canonical local factor is one at every prime `p ≤ w`. -/
theorem selectedCFZCanonicalCarryPairedFourierLocalFactor_eq_one_of_small
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k)
    (hwb : (primorial d.w).Coprime d.b)
    {p : Nat.Primes} (hp : p ∈ smallPrimeFinset d.w) :
    pairedFourierPrimeLocalFactor d.R
        d.carryAdjustedFamily d.t d.u p = 1 := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  rw [pairedFourierPrimeLocalFactor]
  unfold SelectedCFZCanonicalCarryFourierData.carryAdjustedFamily
  exact
    pairedFourierLocalFactor_cfzCarryAdjustedFamilyAtVector_eq_one_of_dvd
      d.N (primorial d.w) d.b p.prop
      (p.prop.dvd_primorial_iff.mpr
        (mem_smallPrimeFinset.mp hp))
      hwb d.R
      (fun q : SelectedCFZFormIndex d.e => q.1)
      d.carry d.t d.u

/-- At a small prime the canonical arithmetic/zeta ratio is the inverse
universal zeta factor. -/
theorem
    selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_eq_inv_of_small
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k)
    (hwb : (primorial d.w).Coprime d.b)
    {p : Nat.Primes} (hp : p ∈ smallPrimeFinset d.w) :
    d.primeArithmeticToZetaLocalRatio p =
      (cutoffZetaEulerLocalFactor d.R d.t d.u p)⁻¹ := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have hlocal :
      pairedFourierLocalFactor d.R (p : ℕ)
          d.carryAdjustedFamily d.t d.u = 1 := by
    simpa [pairedFourierPrimeLocalFactor] using
      selectedCFZCanonicalCarryPairedFourierLocalFactor_eq_one_of_small
        d hwb hp
  rw [
    SelectedCFZCanonicalCarryFourierData.primeArithmeticToZetaLocalRatio,
    pairedFourierArithmeticToZetaLocalRatio,
    hlocal,
    one_div,
    cutoffZetaEulerLocalFactor_eq_fourierZetaSystemEulerLocalFactor]

/-- The finite product over `p ≤ w` is the standard small-prime
correction. -/
theorem prod_selectedCFZCanonicalCarrySmallPrimeArithmeticToZetaRatio_eq
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k)
    (hwb : (primorial d.w).Coprime d.b) :
    ∏ p ∈ smallPrimeFinset d.w,
        d.primeArithmeticToZetaLocalRatio p =
      smallPrimeZetaCorrection d.R d.w d.t d.u := by
  apply Finset.prod_congr rfl
  intro p hp
  exact
    selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_eq_inv_of_small
      d hwb hp

/-- The bounded mask is exactly the unordered product on the complement
of the small-prime finset. -/
theorem
    selectedCFZCanonicalCarryLargePrimeEulerCorrection_eq_tprod_smallPrime_compl
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) :
    d.largePrimeEulerCorrection =
      ∏' p :
          ↑((smallPrimeFinset d.w : Set Nat.Primes)ᶜ),
        d.primeArithmeticToZetaLocalRatio p := by
  rw [
    SelectedCFZCanonicalCarryFourierData.largePrimeEulerCorrection,
    tprod_subtype,
    ←
      boundedMaskedComplexPrimeLocalFactor_eq_smallPrime_compl_mulIndicator]

/-- The canonical ratios are multipliable on the large-prime
complement. -/
theorem
    multipliable_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_smallPrime_compl
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCanonicalCarryFourierData k)
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
      norm_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
        hk d hR p hpW (hw.trans_lt hp)
  apply
    (multipliable_subtype_iff_mulIndicator
      (f := d.primeArithmeticToZetaLocalRatio)
      (s :=
        (smallPrimeFinset d.w : Set Nat.Primes)ᶜ)).mpr
  rw [←
    boundedMaskedComplexPrimeLocalFactor_eq_smallPrime_compl_mulIndicator]
  exact hmasked.multipliable

/-- Exact small/large factorization of the complete arithmetic
correction for one canonical carry vector. -/
theorem
    smallPrimeZetaCorrection_mul_selectedCFZCanonicalCarryLargePrimeEulerCorrection
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCanonicalCarryFourierData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w)
    (hwb : (primorial d.w).Coprime d.b) :
    smallPrimeZetaCorrection d.R d.w d.t d.u *
        d.largePrimeEulerCorrection =
      ∏' p : Nat.Primes,
        d.primeArithmeticToZetaLocalRatio p := by
  rw [←
      prod_selectedCFZCanonicalCarrySmallPrimeArithmeticToZetaRatio_eq
        d hwb,
    selectedCFZCanonicalCarryLargePrimeEulerCorrection_eq_tprod_smallPrime_compl]
  rw [←
    Finset.tprod_subtype'
      (smallPrimeFinset d.w)
      d.primeArithmeticToZetaLocalRatio]
  exact
    Multipliable.tprod_mul_tprod_compl
      ((smallPrimeFinset d.w).multipliable
        d.primeArithmeticToZetaLocalRatio)
      (multipliable_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_smallPrime_compl
        hk d hR hw)

/-! ## Exact normalized completed-Euler identities -/

/-- Exact normalized completed-Euler identity for one arbitrary canonical
carry vector. -/
theorem normalizedSelberg_fourier_completeCanonicalCarryEuler_eq
    {k : ℕ} (hk : 2 ≤ k)
    (χ : SmoothSieveCutoff)
    (d : SelectedCFZCanonicalCarryFourierData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w)
    (hwb : (primorial d.w).Coprime d.b) :
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (χ.fourierProductTransform d.t *
            χ.fourierProductTransform d.u *
            cutoffZetaSingularFactor d.R d.t d.u)) *
        cutoffZetaSystemFactor d.R d.t d.u *
        (∏' p : Nat.Primes,
          d.primeArithmeticToZetaLocalRatio p) =
      ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
        normalizedCompletedFourierEulerCorrection
          d.R d.w d.t d.u d.largePrimeEulerCorrection := by
  have hratio :
      (∏' p : Nat.Primes,
          d.primeArithmeticToZetaLocalRatio p) =
        smallPrimeZetaCorrection d.R d.w d.t d.u *
          d.largePrimeEulerCorrection :=
    (smallPrimeZetaCorrection_mul_selectedCFZCanonicalCarryLargePrimeEulerCorrection
      hk d hR hw hwb).symm
  rw [hratio]
  have hnormalization :=
    normalizedSelberg_fourier_zeta_smallPrime_eq
      χ (show 1 < d.R by omega) d.w d.t d.u
  unfold normalizedCompletedFourierEulerCorrection
  calc
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (χ.fourierProductTransform d.t *
            χ.fourierProductTransform d.u *
            cutoffZetaSingularFactor d.R d.t d.u)) *
        cutoffZetaSystemFactor d.R d.t d.u *
        (smallPrimeZetaCorrection d.R d.w d.t d.u *
          d.largePrimeEulerCorrection) =
      ((normalizedSelbergScale χ.normalizer d.R
            (primorial d.w) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
          (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
            (χ.fourierProductTransform d.t *
              χ.fourierProductTransform d.u *
              cutoffZetaSingularFactor d.R d.t d.u)) *
          smallPrimeZetaCorrection d.R d.w d.t d.u) *
        cutoffZetaSystemFactor d.R d.t d.u *
        d.largePrimeEulerCorrection := by
      ring
    _ =
      (((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
          normalizedSmallPrimeZetaCorrection
            d.R d.w d.t d.u) *
        cutoffZetaSystemFactor d.R d.t d.u *
        d.largePrimeEulerCorrection := by
      rw [hnormalization]
    _ =
      ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
        (normalizedSmallPrimeZetaCorrection d.R d.w d.t d.u *
          cutoffZetaSystemFactor d.R d.t d.u *
          d.largePrimeEulerCorrection) := by
      ring

/-- The same identity rewritten all the way to the exact complete
prime-support series used by the canonical Euler completion. -/
theorem
    normalizedSelberg_fourier_canonicalCarryCompletePrimeSupportSeries_eq
    {k : ℕ} (hk : 2 ≤ k)
    (χ : SmoothSieveCutoff)
    (d : SelectedCFZCanonicalCarryFourierData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w)
    (hwb : (primorial d.w).Coprime d.b) :
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (pairedCutoffFourierEnvelope χ d.t d.u *
            d.completePrimeSupportSeries)) =
      ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
        normalizedCompletedFourierEulerCorrection
          d.R d.w d.t d.u d.largePrimeEulerCorrection := by
  let : NeZero d.N := d.N_neZero
  have hseries :=
    tsum_selectedCFZCanonicalCarry_unrestrictedPrimeSupport_eq
      (N := d.N) (w := d.w) (b := d.b)
      hk d.e d.carry hR d.t d.u
  have hnormalized :=
    normalizedSelberg_fourier_completeCanonicalCarryEuler_eq
      hk χ d hR hw hwb
  unfold
    SelectedCFZCanonicalCarryFourierData.completePrimeSupportSeries
  rw [hseries]
  calc
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (pairedCutoffFourierEnvelope χ d.t d.u *
            ((cutoffZetaSingularFactor d.R d.t d.u *
                cutoffZetaSystemFactor d.R d.t d.u) *
              ∏' p : Nat.Primes,
                primePairedFourierArithmeticToZetaLocalRatio
                  d.R d.carryAdjustedFamily d.t d.u p))) =
      (normalizedSelbergScale χ.normalizer d.R
            (primorial d.w) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
          (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
            (χ.fourierProductTransform d.t *
              χ.fourierProductTransform d.u *
              cutoffZetaSingularFactor d.R d.t d.u)) *
          cutoffZetaSystemFactor d.R d.t d.u *
          (∏' p : Nat.Primes,
            d.primeArithmeticToZetaLocalRatio p) := by
        unfold pairedCutoffFourierEnvelope
          SmoothSieveCutoff.fourierProductTransform
          primePairedFourierArithmeticToZetaLocalRatio
          SelectedCFZCanonicalCarryFourierData.primeArithmeticToZetaLocalRatio
        ring
    _ = _ := hnormalized

end Wikipedia.SzemeredisTheorem
