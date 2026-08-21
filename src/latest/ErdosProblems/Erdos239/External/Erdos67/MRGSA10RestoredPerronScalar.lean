import ErdosProblems.Erdos239.External.Erdos67.MRGSA10FixedHighRestoredPerron

/-!
# The restored fixed-high Perron contour at the source scales

This file makes the choices
`eta = (log y)⁻¹` and `T = (log X)^2` in the restored A.10 contour.
After division by `X`, the factor `X` in the Perron kernel cancels exactly.
The resulting bound displays the source saving `(log y)⁻²`, while retaining
the already scalar prime Schur energies and the geometric higher-prime-power
mass.
-/

open scoped LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The normalized restored fixed-high contour budget at the source choices
`eta = (log y)⁻¹` and `T = (log X)^2`.  The first term is the paired prime
Schur energy; the second is the explicit ordinary-multiplicative
higher-prime-power correction. -/
def gsA10RestoredFixedHighSourceScalarBudget
    (Cβ : ℝ) (Q S y A X : ℕ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    (4 * Real.exp 2 * (Real.log (y : ℝ))⁻¹ ^ 2 *
      gsA10RestoredFixedHighHalaszEnvelope A X) *
    ((gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
        (2 * (Real.log (y : ℝ))⁻¹) ((Real.log (X : ℝ)) ^ 2)) ^
          ((1 : ℝ) / 2) *
      (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X
        ((Real.log (X : ℝ)) ^ 2)) ^ ((1 : ℝ) / 2) +
      2 * (Real.log (X : ℝ)) ^ 2 *
        ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
          (2 * gsA10PrimeLambdaHarmonicBudget X *
              gsA10HigherPrimePowerGeometricMass y X +
            (gsA10HigherPrimePowerGeometricMass y X) ^ 2)))

/-- The higher-prime-power part of the source budget after applying its
geometric mass theorem.  Unlike the exact mass, this displays the decisive
factor `log X / y`. -/
def gsA10RestoredFixedHighSourceScalarUpperBudget
    (Cβ : ℝ) (Q S y A X : ℕ) : ℝ :=
  let E := 12 * Real.log X / y * PrimeEstimates.primeReciprocals X
  (2 * Real.pi)⁻¹ *
    (4 * Real.exp 2 * (Real.log (y : ℝ))⁻¹ ^ 2 *
      gsA10RestoredFixedHighHalaszEnvelope A X) *
    ((gsA10PrimeLambdaLeftEnergyBound Cβ Q S X y
        (2 * (Real.log (y : ℝ))⁻¹) ((Real.log (X : ℝ)) ^ 2)) ^
          ((1 : ℝ) / 2) *
      (gsA10PrimeLambdaRightEnergyBound Cβ Q S y X
        ((Real.log (X : ℝ)) ^ 2)) ^ ((1 : ℝ) / 2) +
      2 * (Real.log (X : ℝ)) ^ 2 *
        ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
          (2 * gsA10PrimeLambdaHarmonicBudget X * E + E ^ 2)))

theorem gsA10HigherPrimePowerGeometricMass_nonneg_source
    (y X : ℕ) : 0 ≤ gsA10HigherPrimePowerGeometricMass y X := by
  unfold gsA10HigherPrimePowerGeometricMass
  apply Finset.sum_nonneg
  intro p hp
  have hpData := Erdos67.mem_primesUpTo.mp
    (Finset.mem_filter.mp hp).1
  apply mul_nonneg
  · exact Real.log_nonneg (by exact_mod_cast hpData.1.one_le)
  · apply Finset.sum_nonneg
    intro k hk
    exact div_nonneg (sub_nonneg.mpr (one_le_pow₀ (by norm_num)))
      (by positivity)

/-- Replacing the exact higher-prime-power mass by its standard geometric
upper bound only enlarges the source scalar budget. -/
theorem gsA10RestoredFixedHighSourceScalarBudget_le_upper
    {Cβ : ℝ} {Q S y A X : ℕ} (hy : 3 ≤ y) (hX : 2 ≤ X) :
    gsA10RestoredFixedHighSourceScalarBudget Cβ Q S y A X ≤
      gsA10RestoredFixedHighSourceScalarUpperBudget Cβ Q S y A X := by
  let G := gsA10HigherPrimePowerGeometricMass y X
  let E := 12 * Real.log X / y * PrimeEstimates.primeReciprocals X
  have hG0 : 0 ≤ G := gsA10HigherPrimePowerGeometricMass_nonneg_source y X
  have hGE : G ≤ E := by
    simpa only [G, E] using gsA10HigherPrimePowerGeometricMass_le hy
  have hE0 : 0 ≤ E := hG0.trans hGE
  have hH0 : 0 ≤ gsA10PrimeLambdaHarmonicBudget X := by
    unfold gsA10PrimeLambdaHarmonicBudget
    positivity
  have hpoly :
      2 * gsA10PrimeLambdaHarmonicBudget X * G + G ^ 2 ≤
        2 * gsA10PrimeLambdaHarmonicBudget X * E + E ^ 2 := by
    nlinarith
  have hM0 : 0 ≤ gsA10RestoredFixedHighHalaszEnvelope A X :=
    gsA10RestoredFixedHighHalaszEnvelope_nonneg A X (by omega)
  unfold gsA10RestoredFixedHighSourceScalarBudget
    gsA10RestoredFixedHighSourceScalarUpperBudget
  dsimp only [E]
  have hinner :
      (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
          (2 * gsA10PrimeLambdaHarmonicBudget X *
              gsA10HigherPrimePowerGeometricMass y X +
            gsA10HigherPrimePowerGeometricMass y X ^ 2) ≤
        (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
          (2 * gsA10PrimeLambdaHarmonicBudget X *
              (12 * Real.log X / y * PrimeEstimates.primeReciprocals X) +
            (12 * Real.log X / y * PrimeEstimates.primeReciprocals X) ^ 2) := by
    apply mul_le_mul_of_nonneg_left
    · simpa only [G, E] using hpoly
    · exact Real.rpow_nonneg (by positivity) _
  have hhpp :
      2 * Real.log (X : ℝ) ^ 2 *
          ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                gsA10HigherPrimePowerGeometricMass y X +
              gsA10HigherPrimePowerGeometricMass y X ^ 2)) ≤
        2 * Real.log (X : ℝ) ^ 2 *
          ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
            (2 * gsA10PrimeLambdaHarmonicBudget X *
                (12 * Real.log X / y * PrimeEstimates.primeReciprocals X) +
              (12 * Real.log X / y * PrimeEstimates.primeReciprocals X) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  apply mul_le_mul_of_nonneg_left
  · linarith only [hhpp]
  · positivity

/-- Exact scalarization of the normalized source budget.  In particular,
there is no residual factor of `X` after normalization. -/
theorem two_mul_invLogSq_mul_restoredPerronBudget_div_eq_sourceScalar
    {Cβ : ℝ} {Q S y A X : ℕ} (hX : 0 < X) :
    (2 * (Real.log (y : ℝ))⁻¹ ^ 2 *
        gsA10RestoredFixedHighPerronBudget Cβ Q S y A X
          (Real.log (y : ℝ))⁻¹ ((Real.log (X : ℝ)) ^ 2)) /
      (X : ℝ) =
        gsA10RestoredFixedHighSourceScalarBudget Cβ Q S y A X := by
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast hX.ne'
  unfold gsA10RestoredFixedHighSourceScalarBudget
    gsA10RestoredFixedHighPerronBudget
    gsA10FixedHighPerronKernelScale
  field_simp [hXR]
  ring

/-- The restored two-block moving Perron rectangle at the source scales,
normalized by `X`.  The assumptions on `Q,S,y` are exactly those required
by the finite beta-sieve row theorem.  The harmless condition
`(log X)^2 ≤ X` is kept explicit, since it is only the contour truncation
condition and is independent of the scalar cancellation. -/
theorem exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_sourceScalar_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        (hlogy : 6 ≤ Real.log (y : ℝ))
        (hlogXsqX : (Real.log (X : ℝ)) ^ 2 ≤ X),
        (∀ t : ℝ, |t| ≤ (Real.log (X : ℝ)) ^ 2 →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X) →
        ‖gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y X
            (Real.log (y : ℝ))⁻¹ ((Real.log (X : ℝ)) ^ 2)‖ / (X : ℝ) ≤
          gsA10RestoredFixedHighSourceScalarBudget Cβ Q S y A X := by
  obtain ⟨Cβ, hCβ, hbase⟩ :=
    exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_restored_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside y A X Q S hy hyX hX
    hQ hQy hS hlogCβ hlogy hlogXsqX hdist
  have hlogyPos : 0 < Real.log (y : ℝ) := lt_of_lt_of_le (by norm_num) hlogy
  have hlogXPos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hraw := hbase hmul hbound P₁ P₂ hsmallOutside hy hyX hX
    hQ hQy hS hlogCβ hlogy
    (inv_pos.mpr hlogyPos).le le_rfl (sq_pos_of_pos hlogXPos) hlogXsqX hdist
  have hdiv := div_le_div_of_nonneg_right hraw (by positivity : (0 : ℝ) ≤ X)
  rw [two_mul_invLogSq_mul_restoredPerronBudget_div_eq_sourceScalar
    (show 0 < X by omega)] at hdiv
  exact hdiv

/-- Fully explicit higher-prime-power version of the normalized source-scale
contour theorem.  This is the same estimate as the preceding theorem, with
the geometric mass replaced by `12 log X / y` times the reciprocal-prime
mass. -/
theorem exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_sourceScalarUpper_le :
    ∃ Cβ : ℝ, 1 ≤ Cβ ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
        (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
        {y A X Q S : ℕ} (hy : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
        (hQ : 3 ≤ Q) (hQy : Q ≤ y) (hS : 101 ≤ S)
        (hlogCβ : Real.log Cβ ≤ 2 * (S - 100 : ℕ) / 99)
        (hlogy : 6 ≤ Real.log (y : ℝ))
        (hlogXsqX : (Real.log (X : ℝ)) ^ 2 ≤ X),
        (∀ t : ℝ, |t| ≤ (Real.log (X : ℝ)) ^ 2 →
          (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist t) X) →
        ‖gsA10TwoBlockMovingPerronIntegrated f hmul P₁ P₂ y X
            (Real.log (y : ℝ))⁻¹ ((Real.log (X : ℝ)) ^ 2)‖ / (X : ℝ) ≤
          gsA10RestoredFixedHighSourceScalarUpperBudget Cβ Q S y A X := by
  obtain ⟨Cβ, hCβ, hbase⟩ :=
    exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_sourceScalar_le
  refine ⟨Cβ, hCβ, ?_⟩
  intro f hmul hbound P₁ P₂ _ _ hsmallOutside y A X Q S hy hyX hX
    hQ hQy hS hlogCβ hlogy hlogXsqX hdist
  exact (hbase hmul hbound P₁ P₂ hsmallOutside hy hyX hX
    hQ hQy hS hlogCβ hlogy hlogXsqX hdist).trans
      (gsA10RestoredFixedHighSourceScalarBudget_le_upper (by omega) hX)

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.two_mul_invLogSq_mul_restoredPerronBudget_div_eq_sourceScalar
#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_sourceScalar_le
#print axioms
  Erdos67.MRHalaszBands.gsA10RestoredFixedHighSourceScalarBudget_le_upper
#print axioms
  Erdos67.MRHalaszBands.exists_norm_gsA10TwoBlockMovingPerronIntegrated_fixedHigh_sourceScalarUpper_le
