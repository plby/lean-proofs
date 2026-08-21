import ErdosProblems.Erdos239.External.Erdos67.MRGSA10PrimeLambdaSourceCumulative

/-!
# The source affine prime row at one contour height

This is the direct row interface consumed by the full A.10 contour theorem.
It combines the row-local beta sieve with the inverse-radius far shell,
without passing through a cumulative or weighted-energy wrapper.
-/

namespace Erdos67.MRHalaszBands

noncomputable section

/-- One eventual threshold supplies a source-sharp affine Gaussian row for
every centre in the prime window and every positive contour height. -/
theorem exists_sum_gsA10PrimeWindow_log_div_gaussian_sourceAffineRow :
    ∃ Cbeta : ℝ, ∃ N : ℕ, 1 ≤ Cbeta ∧
      ∀ y X : ℕ, ∀ T : ℝ,
        N ≤ y → 1 ≤ T →
        ∀ n ∈ gsA10PrimeWindow y X,
          (∑ m ∈ gsA10PrimeWindow y X,
              (Real.log (m : ℝ) / m) *
                finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
                  (Real.log m - Real.log n)) ≤
            gsA10PrimeSourceAffineRowConstant Cbeta / T +
              gsA10PrimeSourceAffineRowSlope Cbeta y X := by
  obtain ⟨Cbeta, N, hCbeta, hnear⟩ :=
    exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_eventual_bound
  refine ⟨Cbeta, N, hCbeta, ?_⟩
  intro y X T hNy hT n hn
  apply sum_gsA10PrimeWindow_log_div_gaussian_le_sourceAffineRow
    (Cbeta := Cbeta) hT hn
  have h := hnear y X n T hNy hn (zero_lt_one.trans_le hT)
  dsimp only [gsA10PrimeSourceAffineRowSlope]
  convert h using 1
  ring

end

end Erdos67.MRHalaszBands
