import Wikipedia.GreenTao.Sieve.ComplexEulerProductTail
import Wikipedia.GreenTao.Sieve.WTrickedGoodPrime
import Wikipedia.GreenTao.Sieve.CFZCarryBlockEulerBridge
import Wikipedia.GreenTao.Sieve.CFZCarryFourierBridge

/-!
# Uniform Euler tails on CFZ carry blocks

The carry-block reduction leaves a genuinely varying affine system.  The
paired divisor choice determines the block side length, the point of the
quotient block determines all carry constants, and all of these data may
vary with the asymptotic parameter.  This file keeps that dependence.

At a prime outside the primorial, carry corrections alter only affine
constants.  The direct modular one-form and rank-two predicates therefore
give the same `O_k(p⁻²)` arithmetic-to-zeta ratio estimate on every block,
uniformly in the divisor choice and in both Fourier variables.  The general
dominated Euler-product theorem then shows that the product over `p > w`
tends to one as `w → ∞`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## A dependent package for a varying carry block -/

/-- All data needed for one selected-CFZ carry-block Fourier local factor.

The selected family, smooth scale, cyclic modulus, paired divisor choice,
quotient-block point, residue class, and Fourier variables are fields of the
package.  Thus a family of these packages may vary in every one of those
parameters while `k` stays fixed. -/
structure SelectedCFZCarryFourierBlockData (k : ℕ) where
  N : ℕ
  N_neZero : NeZero N
  R : ℕ
  w : ℕ
  b : ℕ
  e : LinearFormsExponent k
  z : SelectedCFZFormIndex e → ℕ × ℕ
  block :
    FiniteBox (fun _ : CFZVariable k =>
      N / pairedDivisorLcm z)
  t : SelectedCFZFormIndex e → ℝ
  u : SelectedCFZFormIndex e → ℝ

namespace SelectedCFZCarryFourierBlockData

/-- The affine family frozen on the packaged quotient block. -/
noncomputable def carryAdjustedFamily
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k) :
    SelectedCFZFormIndex d.e → AffineForm (CFZVariable k) ℤ := by
  letI : NeZero d.N := d.N_neZero
  exact
    cfzCarryAdjustedFamilyAtBlock
      (N := d.N) (pairedDivisorLcm d.z)
      (primorial d.w) d.b
      (fun q : SelectedCFZFormIndex d.e => q.1)
      (fun v => (d.block v : ℕ))

/-- The carry-block arithmetic/zeta ratio at a natural prime. -/
noncomputable def primeArithmeticToZetaLocalRatio
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k)
    (p : Nat.Primes) : ℂ := by
  letI : NeZero d.N := d.N_neZero
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  exact
    pairedFourierArithmeticToZetaLocalRatio
      d.R (p : ℕ) d.carryAdjustedFamily d.t d.u

/-- The large-prime carry-block correction, with every prime at most `w`
masked to one. -/
noncomputable def largePrimeEulerCorrection
    {k : ℕ} (d : SelectedCFZCarryFourierBlockData k) : ℂ :=
  ∏' p : Nat.Primes,
    boundedMaskedComplexPrimeLocalFactor
      d.w d.primeArithmeticToZetaLocalRatio p

end SelectedCFZCarryFourierBlockData

/-! ## Direct modular local estimate -/

/-- A direct-good-prime arithmetic local factor differs from the common
first-order model by `O(4^m p⁻²)`.  Unlike the natural-constant W-trick
specialization, this statement permits arbitrary integer affine constants. -/
theorem norm_pairedFourierLocalFactor_sub_firstOrder_le_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hR : 2 ≤ R) (t u : κ → ℝ) :
    ‖pairedFourierLocalFactor R p forms t u -
        pairedFourierFirstOrderLocalModel R p t u‖ ≤
      (4 : ℝ) ^ Fintype.card κ / (p : ℝ) ^ 2 := by
  have hbase :=
    norm_complexWeightedLocalFactor_sub_firstOrder_le_of_goodPrime
      hnonzero hrankTwo
      (fun q =>
        pairedFourierPrimeCoefficient R p (t q) (u q))
  simpa [pairedFourierLocalFactor,
    pairedFourierFirstOrderLocalModel,
    complexFirstOrderLocalModel, div_eq_mul_inv] using
    hbase.trans
      (mul_le_mul_of_nonneg_right
        (complexWeightedHigherOrderCoefficientMass_pairedFourier_le
          hR hnonzero.1 t u)
        (by positivity))

/-- Direct modular version of the arithmetic/zeta ratio estimate.  It is
uniform in all affine constants and all Fourier variables. -/
theorem
    norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le_of_goodPrime
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hR : 2 ≤ R)
    (hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierArithmeticToZetaLocalRatio
          R p forms t u - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  let zeta :=
    fourierZetaSystemEulerLocalFactor R p t u
  have hzetaQuarter :
      (1 : ℝ) / 4 ≤ ‖zeta‖ := by
    exact
      one_fourth_le_norm_fourierZetaSystemEulerLocalFactor
        hR hnonzero.1 hcut t u
  have hzetaPos : 0 < ‖zeta‖ :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      hzetaQuarter
  have hcomparison :
      complexZetaModelComparisonCutoff
          (Fintype.card κ) ≤ p :=
    (Nat.le_max_left _ _).trans hcut
  have hseven : 7 ≤ p :=
    (Nat.le_max_left 7
      (6 * Fintype.card κ)).trans hcomparison
  have harithmetic :=
    norm_pairedFourierLocalFactor_sub_firstOrder_le_of_goodPrime
      hnonzero hrankTwo hR t u
  have hzeta :=
    norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
      hR hnonzero.1 hseven t u
  have hdiff :
      ‖pairedFourierLocalFactor R p forms t u - zeta‖ ≤
        complexArithmeticZetaDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    have htriangle :
        ‖pairedFourierLocalFactor R p forms t u - zeta‖ ≤
          ‖pairedFourierLocalFactor R p forms t u -
              pairedFourierFirstOrderLocalModel R p t u‖ +
            ‖zeta -
              pairedFourierFirstOrderLocalModel R p t u‖ := by
      have hrearrange :
          pairedFourierLocalFactor R p forms t u - zeta =
            (pairedFourierLocalFactor R p forms t u -
                pairedFourierFirstOrderLocalModel R p t u) -
              (zeta -
                pairedFourierFirstOrderLocalModel R p t u) := by
        ring
      rw [hrearrange]
      exact norm_sub_le _ _
    calc
      ‖pairedFourierLocalFactor R p forms t u - zeta‖ ≤
          ‖pairedFourierLocalFactor R p forms t u -
              pairedFourierFirstOrderLocalModel R p t u‖ +
            ‖zeta -
              pairedFourierFirstOrderLocalModel R p t u‖ :=
        htriangle
      _ ≤
          (4 : ℝ) ^ Fintype.card κ / (p : ℝ) ^ 2 +
            complexZetaModelDifferenceConstant
                (Fintype.card κ) /
              (p : ℝ) ^ 2 :=
        add_le_add harithmetic (by simpa [zeta] using hzeta)
      _ =
          complexArithmeticZetaDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2 := by
        rw [complexArithmeticZetaDifferenceConstant]
        ring
  have hzetaNe : zeta ≠ 0 :=
    norm_pos_iff.mp hzetaPos
  rw [pairedFourierArithmeticToZetaLocalRatio,
    div_sub_one hzetaNe, Complex.norm_div]
  calc
    ‖pairedFourierLocalFactor R p forms t u - zeta‖ /
          ‖zeta‖ ≤
        4 *
          ‖pairedFourierLocalFactor R p forms t u - zeta‖ := by
      rw [div_le_iff₀ hzetaPos]
      have hnonneg :
          0 ≤ ‖pairedFourierLocalFactor R p forms t u - zeta‖ :=
        norm_nonneg _
      nlinarith
    _ ≤
        4 *
          (complexArithmeticZetaDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ =
        complexArithmeticZetaRatioErrorConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexArithmeticZetaRatioErrorConstant]
      ring

/-! ## A `k`-only bound for every selected block -/

/-- One error constant for all selected carry blocks at ambient
progression length `k`. -/
noncomputable def selectedCFZCarryEulerTailErrorConstant
    (k : ℕ) : ℝ :=
  complexArithmeticZetaRatioErrorConstant
    (Fintype.card (CFZFormIndex k))

theorem selectedCFZCarryEulerTailErrorConstant_nonneg
    (k : ℕ) :
    0 ≤ selectedCFZCarryEulerTailErrorConstant k := by
  exact complexArithmeticZetaRatioErrorConstant_nonneg _

theorem complexArithmeticZetaRatioErrorNat_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexArithmeticZetaRatioErrorNat m ≤
      complexArithmeticZetaRatioErrorNat n := by
  unfold complexArithmeticZetaRatioErrorNat
  exact Nat.mul_le_mul_left 4
    (Nat.add_le_add
      (Nat.pow_le_pow_right (by omega) hmn)
      (complexZetaModelDifferenceNat_mono hmn))

theorem complexArithmeticZetaRatioErrorConstant_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexArithmeticZetaRatioErrorConstant m ≤
      complexArithmeticZetaRatioErrorConstant n := by
  rw [complexArithmeticZetaRatioErrorConstant_eq_natCast,
    complexArithmeticZetaRatioErrorConstant_eq_natCast]
  exact_mod_cast complexArithmeticZetaRatioErrorNat_mono hmn

/-- **Carry-adjusted local input.**  Above the `k`-only cutoff and outside
`W`, every selected CFZ carry block has arithmetic/zeta ratio
`1 + O_k(p⁻²)`.  The estimate is independent of the paired divisor choice,
the quotient block, the carry constants, and both Fourier variables. -/
theorem
    norm_selectedCFZCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCarryFourierBlockData k)
    (hR : 2 ≤ d.R) (p : Nat.Primes)
    (hpW : ¬(p : ℕ) ∣ primorial d.w)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ)) :
    ‖d.primeArithmeticToZetaLocalRatio p - 1‖ ≤
      selectedCFZCarryEulerTailErrorConstant k /
        (p : ℝ) ^ 2 := by
  letI : NeZero d.N := d.N_neZero
  letI : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  obtain ⟨hnonzero, hrankTwo⟩ :=
    selectedCFZCarryAdjustedFamilyAtBlock_goodPrime
      (N := d.N) (W := primorial d.w)
      hk p.prop hpW horiginal d.e
      (pairedDivisorLcm d.z) d.b
      (fun v => (d.block v : ℕ))
  have hfullCut :
      complexZetaModelNonzeroCutoff
          (Fintype.card (CFZFormIndex k)) ≤
        (p : ℕ) :=
    (Nat.le_max_right _ _).trans hlarge.le
  have hselectedCut :
      complexZetaModelNonzeroCutoff
          (Fintype.card
            (SelectedCFZFormIndex d.e)) ≤
        (p : ℕ) :=
    (complexZetaModelNonzeroCutoff_mono
      (card_selectedCFZFormIndex_le d.e)).trans hfullCut
  have hlocal :=
    norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le_of_goodPrime
      hnonzero hrankTwo hR hselectedCut d.t d.u
  have hconstant :
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card
            (SelectedCFZFormIndex d.e)) ≤
        selectedCFZCarryEulerTailErrorConstant k := by
    exact
      complexArithmeticZetaRatioErrorConstant_mono
        (card_selectedCFZFormIndex_le d.e)
  unfold
    SelectedCFZCarryFourierBlockData.primeArithmeticToZetaLocalRatio
    SelectedCFZCarryFourierBlockData.carryAdjustedFamily
  exact hlocal.trans
    (div_le_div_of_nonneg_right hconstant
      (sq_nonneg (p : ℝ)))

/-! ## Uniform large-prime tail -/

/-- **Uniform CFZ carry-block Euler tail.**  Let every carry-block datum
except the ambient progression length `k` vary arbitrarily.  If the smooth
scale is eventually at least two and the primorial cutoff tends to infinity,
then the masked arithmetic/zeta correction product tends to one.

In particular, `N`, the selected family, paired divisor choice, quotient
block, residue class, all carry constants, and all Fourier variables may
depend on the asymptotic parameter. -/
theorem tendsto_selectedCFZCarryLargePrimeEulerCorrection_one
    {α : Type*} {𝓕 : Filter α} {k : ℕ}
    (hk : 2 ≤ k)
    (d : α → SelectedCFZCarryFourierBlockData k)
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
    norm_selectedCFZCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
      hk (d n) hnR p hpW (hnlarge.trans_lt hp)

end Wikipedia.SzemeredisTheorem
