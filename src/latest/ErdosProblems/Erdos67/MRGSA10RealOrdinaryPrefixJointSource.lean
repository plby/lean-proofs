import ErdosProblems.Erdos67.MRGSA10JointProjectionSource
import ErdosProblems.Erdos67.MRGSA10GlobalSecondaryShiu
import ErdosProblems.Erdos67.MRGSA10PrefixUnrestriction
import ErdosProblems.Erdos67.MRRealPrefixFarA10Central

/-!
# Real ordinary prefixes with the joint A.10 projection discharged

This module is generic in the two selected prime blocks.  The joint
near-diagonal/endpoint estimate and the coefficient-mass rectangle remove
the former projection premise.  In the eventual real specialization the
only remaining analytic quantity on the right is the normalized
moving-power contour scalar.
-/

open Filter
open scoped ComplexConjugate

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Generic two-block ordinary-prefix assembly after the joint projection
has been proved.  The contour is left as one normalized numerical input so
that either a real large-zero estimate or another source contour theorem can
be inserted without changing the reconstruction. -/
theorem norm_positivePrefixMean_twoBlock_le_contour_add_jointSource
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {I₁ I₂ : ℕ × ℕ}
    (hdisj : Disjoint (primesInBlock I₁) (primesInBlock I₂))
    {y N : ℕ} (hy : 23 ≤ y) (hyN : y ≤ N) (hN : 2 ≤ N)
    (hlogN : 1 ≤ Real.log (N : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hprimeMass : Erdos67.PrimeEstimates.primeReciprocals N ≤
      Real.log (N : ℝ))
    (hySize : (Real.log (N : ℝ)) ^ 4 ≤ (y : ℝ))
    (hQ₂ : ∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
      mrTwoBlockFirst I₁ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
      ¬ mrTwoBlockFirst I₁ p) → p ≤ y)
    (hperron : ContinuousOn (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10TwoBlockMovingPerronIntegral f hmul
        (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
        y N alpha beta ((Real.log (N : ℝ)) ^ 2)))
      (Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ ×ˢ
        Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹))
    {Econtour rho : ℝ}
    (hcontour :
      ‖gsA10TwoBlockMovingPerronIntegrated f hmul
          (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
          y N (Real.log (y : ℝ))⁻¹ ((Real.log (N : ℝ)) ^ 2)‖ /
          (N : ℝ) ≤ Econtour)
    (hbad : ((atypicalFactorizationSet {I₁, I₂} N).card : ℝ) ≤
      rho * N) :
    ‖positivePrefixMean f N‖ ≤
      Econtour + gsA10JointMovingProjectionSourceBudget y N +
        gsA10GlobalSecondaryShiuConstant *
          Real.log (y : ℝ) / Real.log (N : ℝ) + rho := by
  let P₁ : ℕ → Prop := mrTwoBlockOutside I₁ I₂
  let P₂ : ℕ → Prop := mrTwoBlockFirst I₁
  have hprojection :
      ‖gsA10TwoBlockTailoredIntegratedPrefix f hmul P₁ P₂ y N
            (Real.log (y : ℝ))⁻¹ -
          gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y N
            (Real.log (y : ℝ))⁻¹ ((Real.log (N : ℝ)) ^ 2)‖ /
          (N : ℝ) ≤ gsA10JointMovingProjectionSourceBudget y N := by
    exact
      norm_gsA10TwoBlockTailoredIntegratedPrefix_sub_movingPerronIntegrated_div_le_jointSource
        hmul hcomp hbound P₁ P₂ hy hN hlogN hlogy hprimeMass hySize
          (by simpa only [P₁, P₂] using hQ₂)
          (by simpa only [P₁, P₂] using hQ₃)
          (by simpa only [P₁, P₂] using hperron)
  let tailored : ℂ := gsA10TwoBlockTailoredIntegratedPrefix
    f hmul P₁ P₂ y N (Real.log (y : ℝ))⁻¹
  let moving : ℂ := gsA10TwoBlockMovingPerronIntegrated
    f hmul P₁ P₂ y N (Real.log (y : ℝ))⁻¹
      ((Real.log (N : ℝ)) ^ 2)
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have htailored : ‖tailored‖ / (N : ℝ) ≤
      Econtour + gsA10JointMovingProjectionSourceBudget y N := by
    have htriangle : ‖tailored‖ ≤ ‖moving‖ + ‖tailored - moving‖ := by
      calc
        ‖tailored‖ = ‖moving + (tailored - moving)‖ := by ring_nf
        _ ≤ ‖moving‖ + ‖tailored - moving‖ := norm_add_le _ _
    calc
      ‖tailored‖ / (N : ℝ) ≤
          ‖moving‖ / (N : ℝ) + ‖tailored - moving‖ / (N : ℝ) := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right htriangle hN0
      _ ≤ Econtour + gsA10JointMovingProjectionSourceBudget y N :=
        add_le_add (by simpa only [moving, P₁, P₂] using hcontour)
          (by simpa only [tailored, moving] using hprojection)
  have hrecRaw :=
    norm_positivePrefixSum_gsA10TwoBlockReconstructed_le_tailored_add_log
      hmul hcomp hbound P₁ P₂ hy hyN
        (by simpa only [P₁, P₂] using hQ₂)
        (by simpa only [P₁, P₂] using hQ₃)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrec :
      ‖positivePrefixMean
          (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) N‖ ≤
        Econtour + gsA10JointMovingProjectionSourceBudget y N +
          gsA10GlobalSecondaryShiuConstant *
            Real.log (y : ℝ) / Real.log (N : ℝ) := by
    unfold positivePrefixMean
    rw [norm_div, Complex.norm_natCast]
    calc
      ‖positivePrefixSum
          (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) N‖ /
            (N : ℝ) ≤
          (‖tailored‖ +
              gsA10GlobalSecondaryShiuConstant *
                ((N : ℝ) / Real.log (N : ℝ)) * Real.log (y : ℝ)) /
            (N : ℝ) := by
        exact div_le_div_of_nonneg_right (by
          simpa only [tailored] using hrecRaw) hNpos.le
      _ = ‖tailored‖ / (N : ℝ) +
          gsA10GlobalSecondaryShiuConstant * Real.log (y : ℝ) /
            Real.log (N : ℝ) := by
        field_simp
      _ ≤ Econtour + gsA10JointMovingProjectionSourceBudget y N +
          gsA10GlobalSecondaryShiuConstant * Real.log (y : ℝ) /
            Real.log (N : ℝ) := by
        gcongr
  have hordinary :=
    norm_positivePrefixMean_le_reconstructed_add_atypicalDensity
      hmul hbound hdisj (show 0 < N by omega) hQ₂ hQ₃
      (E := Econtour + gsA10JointMovingProjectionSourceBudget y N +
        gsA10GlobalSecondaryShiuConstant *
          Real.log (y : ℝ) / Real.log (N : ℝ))
      (rho := rho) (by simpa only [P₁, P₂] using hrec) hbad
  exact hordinary

/-- Eventual real large-zero specialization, generic in the two selected
prime blocks and their cutoff.  The old projection premise is absent.  The
only analytic scalar retained on the right is the normalized moving-power
contour budget; all other terms are explicit source errors. -/
theorem exists_eventually_norm_positivePrefixMean_real_largeZero_twoBlock_le_jointSource :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∃ Sβ : ℕ, 101 ≤ Sβ ∧
        Real.log Cβ ≤ 2 * (Sβ - 100 : ℕ) / 99 ∧
      ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ)
        (hmul : IsMultiplicativeOnPositiveNat f),
        IsCompletelyMultiplicativeOnPositive f →
        (∀ n, 0 < n → conj (f n) = f n) →
        (∀ n, ‖f n‖ ≤ 1) →
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
            pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
        ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ∀ (I₁ I₂ : ℕ × ℕ),
        Disjoint (primesInBlock I₁) (primesInBlock I₂) →
        (∀ p ∈ gsA9SmallPrimeFinset, mrTwoBlockOutside I₁ I₂ p) →
        ∀ {y : ℕ}, 23 ≤ y → y ≤ Z →
        1 ≤ Real.log (Z : ℝ) →
        6 ≤ Real.log (y : ℝ) →
        Real.log (Z : ℝ) ^ 2 ≤ Z →
        Erdos67.PrimeEstimates.primeReciprocals Z ≤ Real.log (Z : ℝ) →
        Real.log (Z : ℝ) ^ 4 ≤ (y : ℝ) →
        (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
          mrTwoBlockFirst I₁ p) → p ≤ y) →
        (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧
          ¬ mrTwoBlockFirst I₁ p) → p ≤ y) →
        ContinuousOn (Function.uncurry (fun alpha beta : ℝ ↦
          gsA10TwoBlockMovingPerronIntegral f hmul
            (mrTwoBlockOutside I₁ I₂) (mrTwoBlockFirst I₁)
            y Z alpha beta ((Real.log (Z : ℝ)) ^ 2)))
          (Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ ×ˢ
            Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹) →
        ∀ {rho : ℝ},
        ((atypicalFactorizationSet {I₁, I₂} Z).card : ℝ) ≤ rho * Z →
        ‖positivePrefixMean f Z‖ ≤
          gsA10MovingRpowRestoredNormalizedBudget Cβ 3 Sβ y
              (realPrefixMovingThreshold X) Z
              (Real.log (y : ℝ))⁻¹ (Real.log (Z : ℝ) ^ 2) +
            gsA10JointMovingProjectionSourceBudget y Z +
            gsA10GlobalSecondaryShiuConstant *
              Real.log (y : ℝ) / Real.log (Z : ℝ) + rho := by
  obtain ⟨Cβ, hCβ, hcontour⟩ :=
    exists_eventually_norm_gsA10MovingPerronIntegrated_real_largeZero_le_movingRpow
  obtain ⟨Sβ, hSβ, hlogCβ⟩ := Erdos67.exists_admissible_betaSieveDepth Cβ
  refine ⟨Cβ, hCβ, Sβ, hSβ, hlogCβ, ?_⟩
  filter_upwards [hcontour] with X hcontourX
  intro f hmul hcomp hreal hbound hzero Z hXZ hZX I₁ I₂ hdisj hsmall
    y hy hyZ hlogZ hlogy hlogZsqZ hprimeMass hySize hQ₂ hQ₃ hperron
    rho hbad
  let P₁ : ℕ → Prop := mrTwoBlockOutside I₁ I₂
  let P₂ : ℕ → Prop := mrTwoBlockFirst I₁
  have heta0 : 0 ≤ (Real.log (y : ℝ))⁻¹ := by
    exact (inv_pos.mpr (by linarith)).le
  have hraw := hcontourX f hmul hreal hbound hzero Z hXZ hZX P₁ P₂
    (by simpa only [P₁] using hsmall) hy hyZ
    (by norm_num : 3 ≤ (3 : ℕ)) (by omega : 3 ≤ y) hSβ hlogCβ
    hlogy hlogZsqZ heta0 le_rfl
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hdiv := div_le_div_of_nonneg_right hraw hZpos.le
  have hcontourNorm :
      ‖gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y Z
          (Real.log (y : ℝ))⁻¹ (Real.log (Z : ℝ) ^ 2)‖ / (Z : ℝ) ≤
        gsA10MovingRpowRestoredNormalizedBudget Cβ 3 Sβ y
          (realPrefixMovingThreshold X) Z
          (Real.log (y : ℝ))⁻¹ (Real.log (Z : ℝ) ^ 2) := by
    calc
      _ ≤ (2 * (2 * Real.pi)⁻¹ *
          gsA10MovingRpowRestoredCoefficient Cβ 3 Sβ y
            (realPrefixMovingThreshold X) Z (Real.log (Z : ℝ) ^ 2) *
          (2 * Real.exp 1 * (Real.log (y : ℝ))⁻¹ *
            ((Z : ℝ) / Real.log (Z : ℝ)))) / (Z : ℝ) := hdiv
      _ = _ := gsA10MovingRpowRestoredIntegrated_rhs_div_eq_normalized
        (show 1 < Z by omega)
  exact norm_positivePrefixMean_twoBlock_le_contour_add_jointSource
    hmul hcomp (fun n _hn ↦ hbound n) hdisj hy hyZ (by omega)
      hlogZ hlogy hprimeMass hySize hQ₂ hQ₃
      (by simpa only [P₁, P₂] using hperron)
      (Econtour := gsA10MovingRpowRestoredNormalizedBudget Cβ 3 Sβ y
        (realPrefixMovingThreshold X) Z
        (Real.log (y : ℝ))⁻¹ (Real.log (Z : ℝ) ^ 2))
      (rho := rho) (by simpa only [P₁, P₂] using hcontourNorm) hbad

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixMean_twoBlock_le_contour_add_jointSource
#print axioms
  Erdos67.MRHalaszBands.exists_eventually_norm_positivePrefixMean_real_largeZero_twoBlock_le_jointSource
