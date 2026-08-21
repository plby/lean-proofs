import ErdosProblems.Erdos239.External.Erdos67.MRGSA10MovingPerronIntegral
import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TwoBlockAtypicalLargeScalar

/-!
# Moving A.10 contour for prime blocks above the fixed small-prime cutoff

This is the source-facing specialization used after narrowing the first
canonical prime block to begin at `23`.  The two `hlarge` hypotheses of the
Euler comparison are discharged definitionally from the block endpoints.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

private theorem mrTwoBlock_selected_large
    (I₁ I₂ : ℕ × ℕ) (hI₁ : 23 ≤ I₁.1) (hI₂ : 23 ≤ I₂.1) :
    (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) →
      23 ≤ p) ∧
    (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧ ¬ mrTwoBlockFirst I₁ p) →
      23 ≤ p) := by
  constructor
  · intro p hp
    exact hI₁.trans (mem_primesInBlock.mp hp.2).2.1
  · intro p hp
    have hpI₂ : p ∈ primesInBlock I₂ := by
      by_contra hpI₂
      exact hp.1 ⟨hp.2, hpI₂⟩
    exact hI₂.trans (mem_primesInBlock.mp hpI₂).2.1

/-- Pointwise source-facing four-factor bound for the narrowed canonical
two-block predicates. -/
theorem norm_LSeries_gsA10TwoBlockCanonicalTailored_le_movingScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (I₁ I₂ : ℕ × ℕ) (hI₁ : 23 ≤ I₁.1) (hI₂ : 23 ≤ I₂.1)
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (ht : |t| ≤ X) :
    ‖LSeries (gsA10TwoBlockTailoredCoefficient f hmul
        (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
        y X alpha beta)
        (((Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
          Complex.I * (t : ℂ))‖ ≤
      gsA10MovingVerticalScalar y A X := by
  obtain ⟨hlarge₂, hlarge₃⟩ :=
    mrTwoBlock_selected_large I₁ I₂ hI₁ hI₂
  exact norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar
    hmul hcomp hbound (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
    hy hX hnonpret
    (fun p _ hp ↦ hlarge₂ p hp) (fun p _ hp ↦ hlarge₃ p hp)
    hlogy halpha0 halpha hbeta0 hbeta ht

/-- Rectangle-uniform Perron bound for the narrowed canonical two-block
predicates. -/
theorem norm_gsA10TwoBlockCanonicalMovingPerronIntegral_le_scalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (I₁ I₂ : ℕ × ℕ) (hI₁ : 23 ≤ I₁.1) (hI₂ : 23 ≤ I₂.1)
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT0 : 0 ≤ T) (hTX : T ≤ X) :
    ‖gsA10TwoBlockMovingPerronIntegral f hmul
        (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
        y X alpha beta T‖ ≤
      gsA10MovingPerronScalar y A X T := by
  obtain ⟨hlarge₂, hlarge₃⟩ :=
    mrTwoBlock_selected_large I₁ I₂ hI₁ hI₂
  exact norm_gsA10TwoBlockMovingPerronIntegral_le_scalar
    hmul hcomp hbound (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
    hy hX hnonpret
    (fun p _ hp ↦ hlarge₂ p hp) (fun p _ hp ↦ hlarge₃ p hp)
    hlogy halpha0 halpha hbeta0 hbeta hT0 hTX

private theorem gsA10CanonicalLargeBlock_lowers
    {K : ℕ} (hK : 5 ≤ K) :
    23 ≤ (gsA10CanonicalLargeFirstBlock K).1 ∧
      23 ≤ (gsA10CanonicalLargeSecondBlock K).1 := by
  constructor
  · norm_num [gsA10CanonicalLargeFirstBlock]
  · dsimp only [gsA10CanonicalLargeSecondBlock,
      gsA10CanonicalSecondBlock, Prod.fst]
    have hpow : 32 ≤ 2 ^ K := by
      have h := Nat.pow_le_pow_right (by omega : 0 < 2) hK
      norm_num at h ⊢
      exact h
    omega

/-- Pointwise moving-contour estimate on the repaired canonical large
blocks. -/
theorem norm_LSeries_gsA10CanonicalLargeTailored_le_movingScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {K : ℕ} (hK : 5 ≤ K)
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (ht : |t| ≤ X) :
    ‖LSeries (gsA10TwoBlockTailoredCoefficient f hmul
        (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
          (gsA10CanonicalLargeSecondBlock K))
        (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
        y X alpha beta)
        (((Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
          Complex.I * (t : ℂ))‖ ≤
      gsA10MovingVerticalScalar y A X := by
  obtain ⟨hI₁, hI₂⟩ := gsA10CanonicalLargeBlock_lowers hK
  exact norm_LSeries_gsA10TwoBlockCanonicalTailored_le_movingScalar
    hmul hcomp hbound
    (gsA10CanonicalLargeFirstBlock K) (gsA10CanonicalLargeSecondBlock K)
    hI₁ hI₂ hy hX hnonpret hlogy halpha0 halpha hbeta0 hbeta ht

/-- Rectangle-uniform moving Perron estimate on the repaired canonical
large blocks. -/
theorem norm_gsA10CanonicalLargeMovingPerronIntegral_le_scalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {K : ℕ} (hK : 5 ≤ K)
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT0 : 0 ≤ T) (hTX : T ≤ X) :
    ‖gsA10TwoBlockMovingPerronIntegral f hmul
        (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
          (gsA10CanonicalLargeSecondBlock K))
        (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
        y X alpha beta T‖ ≤
      gsA10MovingPerronScalar y A X T := by
  obtain ⟨hI₁, hI₂⟩ := gsA10CanonicalLargeBlock_lowers hK
  exact norm_gsA10TwoBlockCanonicalMovingPerronIntegral_le_scalar
    hmul hcomp hbound
    (gsA10CanonicalLargeFirstBlock K) (gsA10CanonicalLargeSecondBlock K)
    hI₁ hI₂ hy hX hnonpret hlogy halpha0 halpha hbeta0 hbeta hT0 hTX

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_LSeries_gsA10TwoBlockCanonicalTailored_le_movingScalar
#print axioms
  Erdos67.MRHalaszBands.norm_gsA10TwoBlockCanonicalMovingPerronIntegral_le_scalar
#print axioms
  Erdos67.MRHalaszBands.norm_LSeries_gsA10CanonicalLargeTailored_le_movingScalar
#print axioms
  Erdos67.MRHalaszBands.norm_gsA10CanonicalLargeMovingPerronIntegral_le_scalar
