import ErdosProblems.Erdos67b.MRGSA9SmallPrimeDeletion
import ErdosProblems.Erdos67b.MRGSA10PositiveLine
import ErdosProblems.Erdos67b.MRGSA9SourceHalaszPointWide

/-!
# Restoring the fixed small-prime Euler factors

The source-sharp horizontal comparison is applied after deleting the
finitely many primes below `23`.  For the two-block coefficient these
primes all lie in the common outside band, so the original alternating low
series is exactly the deleted alternating low series multiplied by one
fixed finite Euler product.  This file records that exact restoration and
its uniform norm bound.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The actual fixed small-prime Euler product. -/
def gsA9SmallPrimeEulerProduct (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∏ p ∈ gsA9SmallPrimeFinset, gsA9LocalEulerFactor f s p

/-- On any low-prime subfamily containing every prime below `23`, its Euler
product is the fixed small-prime factor times the corresponding product for
the small-prime-deleted coefficient. -/
theorem prod_filter_eq_smallPrimeEulerProduct_mul_delete
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P : ℕ → Prop) [DecidablePred P]
    {y : ℕ} (hy : 23 ≤ y)
    (hsmallP : ∀ p ∈ gsA9SmallPrimeFinset, P p)
    (s : ℂ) :
    (∏ p ∈ (primesUpTo y).filter P,
        gsA9LocalEulerFactor f s p) =
      gsA9SmallPrimeEulerProduct f s *
        ∏ p ∈ (primesUpTo y).filter P,
          gsA9LocalEulerFactor
            (gsDeletePrimeBand f gsA9SmallPrime) s p := by
  let S : Finset ℕ := (primesUpTo y).filter P
  let Ssmall : Finset ℕ := S.filter (fun p ↦ p < 23)
  let Slarge : Finset ℕ := S.filter (fun p ↦ ¬ p < 23)
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  have hsmallSet : Ssmall = gsA9SmallPrimeFinset := by
    ext p
    simp only [Ssmall, S, Finset.mem_filter, gsA9SmallPrimeFinset,
      Finset.mem_filter, Finset.mem_range, mem_primesUpTo]
    constructor
    · rintro ⟨⟨⟨hp, _⟩, _⟩, hp23⟩
      exact ⟨hp23, hp⟩
    · rintro ⟨hp23, hp⟩
      have hpSmall : p ∈ gsA9SmallPrimeFinset := by
        simp only [gsA9SmallPrimeFinset, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨hp23, hp⟩
      exact ⟨⟨⟨hp, hp23.le.trans hy⟩, hsmallP p hpSmall⟩, hp23⟩
  have hsplitF :
      (∏ p ∈ S, gsA9LocalEulerFactor f s p) =
        (∏ p ∈ Ssmall, gsA9LocalEulerFactor f s p) *
          ∏ p ∈ Slarge, gsA9LocalEulerFactor f s p := by
    simpa only [Ssmall, Slarge] using
      (Finset.prod_filter_mul_prod_filter_not S (fun p ↦ p < 23)
        (gsA9LocalEulerFactor f s)).symm
  have hsplitG :
      (∏ p ∈ S, gsA9LocalEulerFactor g s p) =
        (∏ p ∈ Ssmall, gsA9LocalEulerFactor g s p) *
          ∏ p ∈ Slarge, gsA9LocalEulerFactor g s p := by
    simpa only [Ssmall, Slarge] using
      (Finset.prod_filter_mul_prod_filter_not S (fun p ↦ p < 23)
        (gsA9LocalEulerFactor g s)).symm
  have hsmallG :
      (∏ p ∈ Ssmall, gsA9LocalEulerFactor g s p) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    have hp23 : p < 23 := (Finset.mem_filter.mp hp).2
    have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hpS).1).1
    exact gsA9LocalEulerFactor_deleteSmallPrimes_eq_one hmul s hpPrime hp23
  have hlargeEq :
      (∏ p ∈ Slarge, gsA9LocalEulerFactor f s p) =
        ∏ p ∈ Slarge, gsA9LocalEulerFactor g s p := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    have hpLarge : 23 ≤ p := Nat.le_of_not_gt (Finset.mem_filter.mp hp).2
    have hpPrime := (mem_primesUpTo.mp (Finset.mem_filter.mp hpS).1).1
    exact (gsA9LocalEulerFactor_deleteSmallPrimes_eq
      f s hpPrime hpLarge).symm
  change (∏ p ∈ S, gsA9LocalEulerFactor f s p) =
    gsA9SmallPrimeEulerProduct f s *
      ∏ p ∈ S, gsA9LocalEulerFactor g s p
  rw [hsplitF, hsmallSet, hlargeEq, hsplitG, hsmallG, one_mul]
  rfl

/-- Exact restoration for the actual two-block alternating low series.
The hypothesis says precisely that all fixed small primes lie in the
outside band `P₁`. -/
theorem LSeries_twoBlockAlternatingLow_eq_smallPrime_mul_delete
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y : ℕ} (hy : 23 ≤ y)
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {s : ℂ} (hs : 0 < s.re) :
    LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) s =
      gsA9SmallPrimeEulerProduct f s *
        LSeries
          (gsA10TwoBlockAlternatingLow
            (gsDeletePrimeBand f gsA9SmallPrime) P₁ P₂ y) s := by
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let S0 : Finset ℕ := (primesUpTo y).filter (fun p ↦
    ¬ (¬ P₁ p ∧ P₂ p) ∧ ¬ (¬ P₁ p ∧ ¬ P₂ p))
  let S2 : Finset ℕ := (primesUpTo y).filter (fun p ↦ ¬ P₁ p ∧ P₂ p)
  let S3 : Finset ℕ := (primesUpTo y).filter (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hEulerF := twoBlock_alternatingLow_LSeries_eq_EulerFactors_of_pos_re
    hmul hbound P₁ P₂ y hs
  have hEulerG := twoBlock_alternatingLow_LSeries_eq_EulerFactors_of_pos_re
    hmulG hboundG P₁ P₂ y hs
  have hsmallS0 : ∀ p ∈ gsA9SmallPrimeFinset,
      (¬ (¬ P₁ p ∧ P₂ p) ∧ ¬ (¬ P₁ p ∧ ¬ P₂ p)) := by
    intro p hp
    have hp1 := hsmallOutside p hp
    constructor <;> tauto
  have hS0 := prod_filter_eq_smallPrimeEulerProduct_mul_delete
    hmul (fun p ↦ ¬ (¬ P₁ p ∧ P₂ p) ∧ ¬ (¬ P₁ p ∧ ¬ P₂ p))
    hy hsmallS0 s
  have hS2 :
      (∏ p ∈ S2, gsA9LocalEulerFactor f s p) =
        ∏ p ∈ S2, gsA9LocalEulerFactor g s p := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := (mem_primesUpTo.mp hpData.1).1
    have hpNotSmall : ¬ p < 23 := by
      intro hp23
      have hpSmall : p ∈ gsA9SmallPrimeFinset := by
        simp only [gsA9SmallPrimeFinset, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨hp23, hpPrime⟩
      exact hpData.2.1 (hsmallOutside p hpSmall)
    exact (gsA9LocalEulerFactor_deleteSmallPrimes_eq
      f s hpPrime (Nat.le_of_not_gt hpNotSmall)).symm
  have hS3 :
      (∏ p ∈ S3, gsA9LocalEulerFactor f s p) =
        ∏ p ∈ S3, gsA9LocalEulerFactor g s p := by
    apply Finset.prod_congr rfl
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpPrime := (mem_primesUpTo.mp hpData.1).1
    have hpNotSmall : ¬ p < 23 := by
      intro hp23
      have hpSmall : p ∈ gsA9SmallPrimeFinset := by
        simp only [gsA9SmallPrimeFinset, Finset.mem_filter,
          Finset.mem_range]
        exact ⟨hp23, hpPrime⟩
      exact hpData.2.1 (hsmallOutside p hpSmall)
    exact (gsA9LocalEulerFactor_deleteSmallPrimes_eq
      f s hpPrime (Nat.le_of_not_gt hpNotSmall)).symm
  have hEulerF' :
      LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) s =
        (∏ p ∈ S0, gsA9LocalEulerFactor f s p) *
          ((∏ p ∈ S2, gsA9LocalEulerFactor f s p) - 1) *
          ((∏ p ∈ S3, gsA9LocalEulerFactor f s p) - 1) := by
    simpa only [S0, S2, S3] using hEulerF
  have hEulerG' :
      LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) s =
        (∏ p ∈ S0, gsA9LocalEulerFactor g s p) *
          ((∏ p ∈ S2, gsA9LocalEulerFactor g s p) - 1) *
          ((∏ p ∈ S3, gsA9LocalEulerFactor g s p) - 1) := by
    simpa only [S0, S2, S3] using hEulerG
  rw [hEulerF', hS2, hS3]
  rw [show (∏ p ∈ S0, gsA9LocalEulerFactor f s p) =
      gsA9SmallPrimeEulerProduct f s *
        ∏ p ∈ S0, gsA9LocalEulerFactor g s p by
    simpa only [S0] using hS0]
  rw [hEulerG']
  ring

/-- The restored fixed factor costs only the universal small-prime Euler
constant on every source line of real part at least one half. -/
theorem norm_gsA9SmallPrimeEulerProduct_le
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {sigma t : ℝ} (hsigma : 1 / 2 ≤ sigma) :
    ‖gsA9SmallPrimeEulerProduct f
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      gsA9SmallPrimeEulerBound := by
  exact norm_prod_gsA9LocalEulerFactor_smallPrimes_le hbound hsigma

/-- Contour-ready widened Halasz bound for the original two-block
coefficient.  The source estimate is applied to the deleted function and
the fixed small-prime product is then restored exactly. -/
theorem norm_twoBlock_alternatingLow_mul_high_le_wideHalaszPoint
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y : ℕ} (hy : 23 ≤ y)
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {A X : ℕ} (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {sigmaLow t : ℝ}
    (hhalf : 1 / 2 ≤ sigmaLow)
    (hle : sigmaLow ≤ Erdos67b.EulerResidue.taoExponent X)
    (hsigmaLow : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow)
    (hgap : Erdos67b.EulerResidue.taoExponent X - sigmaLow ≤
      3 / Real.log (y : ℝ))
    (ht : |t| ≤ X) :
    let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
    ‖LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
        LSeries (gsA9High f y) sHigh‖ ≤
      gsA9SmallPrimeEulerBound *
        (gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
          Real.exp
            ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2)) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := Erdos67b.MRHalaszEuler.halaszPoint X t
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have hsLow : 0 < sLow.re := by
    simpa only [sLow, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, add_zero] using
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf)
  have hrestore :=
    LSeries_twoBlockAlternatingLow_eq_smallPrime_mul_delete
      hmul hbound P₁ P₂ hy hsmallOutside hsLow
  have hhigh : gsA9High g y = gsA9High f y := by
    exact gsA9High_deleteSmallPrimes_eq f hy
  have hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False := by
    intro p hp h2 h3
    exact h3.2 h2.2
  have hwide :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_wideHalaszPoint
      hmul hbound Q₂ Q₃ hy hdisj hX hnonpret hhalf hle hsigmaLow hgap ht
  have hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hAltEq := LSeries_gsA10TwoBlockAlternatingLow_of_pos_re
    hmulG hboundG P₁ P₂ y hsLow
  have hwide' :
      ‖LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9High g y) sHigh‖ ≤
        gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
          Real.exp
            ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2) := by
    rw [hAltEq]
    simpa only [g, sLow, sHigh, Q₂, Q₃] using hwide
  have hsmall : ‖gsA9SmallPrimeEulerProduct f sLow‖ ≤
      gsA9SmallPrimeEulerBound := by
    simpa only [sLow] using
      (norm_gsA9SmallPrimeEulerProduct_le hbound (t := t) hhalf)
  have hsmall0 : 0 ≤ gsA9SmallPrimeEulerBound :=
    (norm_nonneg _).trans hsmall
  have htarget :
      ‖LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow *
          LSeries (gsA9High f y) sHigh‖ ≤
        gsA9SmallPrimeEulerBound *
          (gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
            Real.exp
              ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
                3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2)) := by
    rw [hrestore, ← hhigh]
    rw [show gsA9SmallPrimeEulerProduct f sLow *
        LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9High g y) sHigh =
        gsA9SmallPrimeEulerProduct f sLow *
          (LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
            LSeries (gsA9High g y) sHigh) by ring]
    rw [norm_mul]
    exact mul_le_mul hsmall hwide' (norm_nonneg _) hsmall0
  simpa only [sLow, sHigh] using htarget

end

end Erdos67b.MRHalaszBands
