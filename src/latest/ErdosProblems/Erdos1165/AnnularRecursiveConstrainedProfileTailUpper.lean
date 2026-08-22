/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveProfileTailUpper
import ErdosProblems.Erdos1165.AsymmetricActualFarPairData

/-!
# Fixed-prefix aggregate for corrected recursive profile rows

This finite-sum adapter turns the one-profile corrected recursive row upper
into the exact fixed-prefix constrained tail used by A.16.  It is deliberately
generic in the concrete row mass; the pathwise recursive code assembly only
has to provide the pointwise estimate proved in
`AnnularRecursiveProfileTailUpper`.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRecursiveConstrainedProfileTailUpper

open AppendixFirstMoment AsymmetricActualFarPairData
open ProfileConditionalTailUpper ProfileListExponent ProfileWeightUpper

noncomputable section

/-- Sum arbitrary concrete rows over all constrained extensions while
preserving an arbitrary nonnegative coefficient. -/
theorem sum_fixedPrefix_rows_le_coefficient
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta coefficient : ℝ)
    (hcoefficient : 0 ≤ coefficient)
    (row : Profile n → ℝ≥0∞)
    (hrow : ∀ m ∈ (constrainedProfiles n delta).filter
        (fun m => profilePrefix hstart hstartn m = pref),
      row m ≤ ENNReal.ofReal (coefficient *
        transitionSegmentProduct start (n - start) (profileAtScale m))) :
    (∑ m ∈ (constrainedProfiles n delta).filter
        (fun m => profilePrefix hstart hstartn m = pref), row m) ≤
      ENNReal.ofReal (coefficient *
        constrainedProfileTailWeight n start hstart hstartn pref delta) := by
  let extensions := (constrainedProfiles n delta).filter
    (fun m => profilePrefix hstart hstartn m = pref)
  have href0 (m : Profile n) :
      0 ≤ coefficient *
        transitionSegmentProduct start (n - start) (profileAtScale m) :=
    mul_nonneg hcoefficient
      (transitionSegmentProduct_nonneg start (n - start) (profileAtScale m))
  calc
    (∑ m ∈ extensions, row m) ≤
        ∑ m ∈ extensions, ENNReal.ofReal (coefficient *
          transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hrow m hm
    _ = ENNReal.ofReal
          (∑ m ∈ extensions, coefficient *
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun m hm => href0 m)).symm
    _ = ENNReal.ofReal (coefficient *
          ∑ m ∈ extensions,
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal (coefficient *
          constrainedProfileTailWeight n start hstart hstartn pref delta) := by
      rfl

/-- Fixed-prefix summation with an arbitrary common `ENNReal` continuation
factor.  This is useful when the recursive profile row has already been
attached to a retained remote endpoint kernel. -/
theorem sum_fixedPrefix_rows_le_coefficient_mul
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta coefficient : ℝ)
    (hcoefficient : 0 ≤ coefficient)
    (factor : ℝ≥0∞) (row : Profile n → ℝ≥0∞)
    (hrow : ∀ m ∈ (constrainedProfiles n delta).filter
        (fun m ↦ profilePrefix hstart hstartn m = pref),
      row m ≤ ENNReal.ofReal (coefficient *
        transitionSegmentProduct start (n - start) (profileAtScale m)) *
          factor) :
    (∑ m ∈ (constrainedProfiles n delta).filter
        (fun m ↦ profilePrefix hstart hstartn m = pref), row m) ≤
      ENNReal.ofReal (coefficient *
        constrainedProfileTailWeight n start hstart hstartn pref delta) *
          factor := by
  let extensions := (constrainedProfiles n delta).filter
    (fun m ↦ profilePrefix hstart hstartn m = pref)
  calc
    (∑ m ∈ extensions, row m) ≤
        ∑ m ∈ extensions,
          ENNReal.ofReal (coefficient *
            transitionSegmentProduct start (n - start) (profileAtScale m)) *
              factor := by
      exact Finset.sum_le_sum fun m hm ↦ hrow m hm
    _ = (∑ m ∈ extensions,
          ENNReal.ofReal (coefficient *
            transitionSegmentProduct start (n - start) (profileAtScale m))) *
          factor := by
      rw [Finset.sum_mul]
    _ ≤ ENNReal.ofReal (coefficient *
          constrainedProfileTailWeight n start hstart hstartn pref delta) *
          factor := by
      gcongr
      exact sum_fixedPrefix_rows_le_coefficient hstart hstartn pref delta
        coefficient hcoefficient
        (fun m ↦ ENNReal.ofReal (coefficient *
          transitionSegmentProduct start (n - start) (profileAtScale m)))
        (fun m _ ↦ le_rfl)

/-- Sum arbitrary concrete corrected rows over all constrained extensions of
one exact prefix. -/
theorem sum_fixedPrefix_rows_le_expOne_constrainedProfileTailWeight
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta : ℝ)
    (row : Profile n → ℝ≥0∞)
    (hrow : ∀ m ∈ (constrainedProfiles n delta).filter
        (fun m => profilePrefix hstart hstartn m = pref),
      row m ≤ ENNReal.ofReal (Real.exp 1 *
        transitionSegmentProduct start (n - start) (profileAtScale m))) :
    (∑ m ∈ (constrainedProfiles n delta).filter
        (fun m => profilePrefix hstart hstartn m = pref), row m) ≤
      ENNReal.ofReal (Real.exp 1 *
        constrainedProfileTailWeight n start hstart hstartn pref delta) := by
  let extensions := (constrainedProfiles n delta).filter
    (fun m => profilePrefix hstart hstartn m = pref)
  have href0 (m : Profile n) :
      0 ≤ Real.exp 1 *
        transitionSegmentProduct start (n - start) (profileAtScale m) :=
    mul_nonneg (Real.exp_nonneg _)
      (transitionSegmentProduct_nonneg start (n - start) (profileAtScale m))
  calc
    (∑ m ∈ extensions, row m) ≤
        ∑ m ∈ extensions, ENNReal.ofReal (Real.exp 1 *
          transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      apply Finset.sum_le_sum
      intro m hm
      exact hrow m hm
    _ = ENNReal.ofReal
          (∑ m ∈ extensions, Real.exp 1 *
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun m hm => href0 m)).symm
    _ = ENNReal.ofReal (Real.exp 1 *
          ∑ m ∈ extensions,
            transitionSegmentProduct start (n - start) (profileAtScale m)) := by
      congr 1
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal (Real.exp 1 *
          constrainedProfileTailWeight n start hstart hstartn pref delta) := by
      rfl

/-- The fixed-prefix adapter with the sharpened half-exponential recursive
coefficient. -/
theorem sum_fixedPrefix_rows_le_expHalf_constrainedProfileTailWeight
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta : ℝ)
    (row : Profile n → ℝ≥0∞)
    (hrow : ∀ m ∈ (constrainedProfiles n delta).filter
        (fun m => profilePrefix hstart hstartn m = pref),
      row m ≤ ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
        transitionSegmentProduct start (n - start) (profileAtScale m))) :
    (∑ m ∈ (constrainedProfiles n delta).filter
        (fun m => profilePrefix hstart hstartn m = pref), row m) ≤
      ENNReal.ofReal (Real.exp (1 / 2 : ℝ) *
        constrainedProfileTailWeight n start hstart hstartn pref delta) := by
  exact sum_fixedPrefix_rows_le_coefficient hstart hstartn pref delta
    (Real.exp (1 / 2 : ℝ)) (Real.exp_nonneg _) row hrow

/-- The canonical `expOne` certificate absorbs the complete corrected
fixed-prefix continuation row. -/
theorem sum_fixedPrefix_rows_le_expOne_radialTail
    {delta : ℝ} {blockIndex : ℕ} {x y : Point}
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤
      AppendixPairMoment.pairPrefixScale
        (Proposition13Scales.scaleIndex delta blockIndex)
        (AppendixPair.separationLevel
          (Proposition13Scales.scaleIndex delta blockIndex) x y))
    (pref : Profile (AppendixPairMoment.pairPrefixScale
      (Proposition13Scales.scaleIndex delta blockIndex)
      (AppendixPair.separationLevel
        (Proposition13Scales.scaleIndex delta blockIndex) x y)))
    (row : Profile (Proposition13Scales.scaleIndex delta blockIndex) → ℝ≥0∞)
    (hrow : ∀ m ∈
      (constrainedProfiles (Proposition13Scales.scaleIndex delta blockIndex)
        profileUpperDelta).filter (fun m =>
          profilePrefix
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans
                (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
            (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale m =
              pref),
      row m ≤ ENNReal.ofReal (Real.exp 1 *
        transitionSegmentProduct
          (AppendixPairMoment.pairPrefixScale
            (Proposition13Scales.scaleIndex delta blockIndex)
            (AppendixPair.separationLevel
              (Proposition13Scales.scaleIndex delta blockIndex) x y))
          (Proposition13Scales.scaleIndex delta blockIndex -
            AppendixPairMoment.pairPrefixScale
              (Proposition13Scales.scaleIndex delta blockIndex)
              (AppendixPair.separationLevel
                (Proposition13Scales.scaleIndex delta blockIndex) x y))
          (profileAtScale m))) :
    (∑ m ∈
      (constrainedProfiles (Proposition13Scales.scaleIndex delta blockIndex)
        profileUpperDelta).filter (fun m =>
          profilePrefix
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans
                (ProfileRadialTailCertificate.expOne hcutoff).tailStart)
            (ProfileRadialTailCertificate.expOne hcutoff).start_le_scale m =
              pref), row m) ≤
      ENNReal.ofReal (ProfileRadialTailCertificate.expOne hcutoff).radialTail := by
  let certificate : ProfileRadialTailCertificate delta blockIndex x y :=
    ProfileRadialTailCertificate.expOne hcutoff
  let start := AppendixPairMoment.pairPrefixScale
    (Proposition13Scales.scaleIndex delta blockIndex)
    (AppendixPair.separationLevel
      (Proposition13Scales.scaleIndex delta blockIndex) x y)
  have hstart : 2 ≤ start :=
    (show 2 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans certificate.tailStart
  have hsum := sum_fixedPrefix_rows_le_expOne_constrainedProfileTailWeight
    hstart certificate.start_le_scale pref profileUpperDelta row hrow
  exact hsum.trans (ENNReal.ofReal_le_ofReal
    (certificate.coefficient_mul_constrainedTail_le pref))

end

end Erdos1165.AnnularRecursiveConstrainedProfileTailUpper
