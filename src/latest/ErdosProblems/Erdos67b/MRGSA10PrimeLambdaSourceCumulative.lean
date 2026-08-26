import ErdosProblems.Erdos67b.MRGSA10PrimeLocalRow
import ErdosProblems.Erdos67b.MRGSA10PrimeGaussianFarShell
import ErdosProblems.Erdos67b.MRGSA10PrimeLambdaDiagonal
import ErdosProblems.Erdos67b.MRGSA10PrimeLambdaBetaDiagonal
import ErdosProblems.Erdos67b.MRGSA10WeightedVerticalCauchy
import ErdosProblems.Erdos67b.MRGSA10SourceYSchedule

/-!
# Source-scheduled cumulative prime-Lambda energy

This downstream leaf packages the analytic assembly after a prime Gaussian
row has been written in the affine form `A / R + B`.  The inverse-radius
term becomes the height-independent energy `E₀`, while only `B` is charged
to the dyadic-shell coefficient `E₁`.

The source-local row supplies `1536 * Csrc / R`; the multiplicative-shell
far theorem supplies another universal `80 * M / R`.  Thus both enter
`E₀`.  Only the source-small density tail and finite-level remainder enter
`E₁`, so the dyadic shell count never multiplies a large `log X` term.
-/

open scoped BigOperators
open Complex MeasureTheory

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Scalar cumulative-energy constant attached to an inverse-radius row
coefficient. -/
def gsA10PrimeAffineEnergyConstant
    (A growth : ℝ) (X : ℕ) : ℝ :=
  Real.exp 1 * Real.sqrt Real.pi * A * growth *
    gsA10PrimeLambdaHarmonicBudget X

/-- Scalar cumulative-energy slope attached to the genuinely affine part
of a prime Gaussian row. -/
def gsA10PrimeAffineEnergySlope
    (B growth : ℝ) (X : ℕ) : ℝ :=
  Real.exp 1 * Real.sqrt Real.pi * B * growth *
    gsA10PrimeLambdaHarmonicBudget X

/-- The central-window constant used when the affine row is available only
above a source height `L`. -/
def gsA10PrimeCentralAffineEnergyConstant
    (A B L growth : ℝ) (X : ℕ) : ℝ :=
  gsA10PrimeAffineEnergyConstant A growth X +
    gsA10PrimeAffineEnergySlope B growth X * L

/-- The universal inverse-radius coefficient in the concrete source row.
It contains the local beta-sieve main term and the inverse-radius far-shell
constant. -/
def gsA10PrimeSourceAffineRowConstant (Cbeta : ℝ) : ℝ :=
  1536 * gsA10BetaSourceDensityConstant Cbeta +
    80 * gsA10PrimeLogHarmonicFactorFourConstant

/-- The source-small slope in the concrete source row. -/
def gsA10PrimeSourceAffineRowSlope
    (Cbeta : ℝ) (y X : ℕ) : ℝ :=
  72 * gsA10BetaSourceDensityConstant Cbeta / y +
    8 * (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cbeta : ℕ) *
      Real.log ((4 * X : ℕ) : ℝ) * (y : ℝ) ^ (-7 / 8 : ℝ)

/-- Ready-to-use source energy constant for either Tao shift. -/
def gsA10PrimeSourceEnergyConstant
    (Cbeta growth : ℝ) (X : ℕ) : ℝ :=
  gsA10PrimeAffineEnergyConstant
    (gsA10PrimeSourceAffineRowConstant Cbeta) growth X

/-- Ready-to-use source-small energy slope for either Tao shift. -/
def gsA10PrimeSourceEnergySlope
    (Cbeta : ℝ) (y X : ℕ) (growth : ℝ) : ℝ :=
  gsA10PrimeAffineEnergySlope
    (gsA10PrimeSourceAffineRowSlope Cbeta y X) growth X

/-- Common row factor left after the dyadic Perron-weighted transfer, before
either prime-Lambda diagonal is scalarized. -/
def gsA10PrimeSourceWeightedRowFactor
    (Cbeta : ℝ) (y X K : ℕ) : ℝ :=
  Real.exp 1 * Real.sqrt Real.pi *
    (6 * gsA10PrimeSourceAffineRowConstant Cbeta +
      (2 + 4 * K) * gsA10PrimeSourceAffineRowSlope Cbeta y X)

theorem gsA10PrimeAffineEnergyConstant_nonneg
    {A growth : ℝ} (hA : 0 ≤ A) (hgrowth : 0 ≤ growth) (X : ℕ) :
    0 ≤ gsA10PrimeAffineEnergyConstant A growth X := by
  unfold gsA10PrimeAffineEnergyConstant gsA10PrimeLambdaHarmonicBudget
  positivity

theorem gsA10PrimeAffineEnergySlope_nonneg
    {B growth : ℝ} (hB : 0 ≤ B) (hgrowth : 0 ≤ growth) (X : ℕ) :
    0 ≤ gsA10PrimeAffineEnergySlope B growth X := by
  unfold gsA10PrimeAffineEnergySlope gsA10PrimeLambdaHarmonicBudget
  positivity

theorem gsA10PrimeSourceAffineRowConstant_nonneg
    {Cbeta : ℝ} (hCbeta : 1 ≤ Cbeta) :
    0 ≤ gsA10PrimeSourceAffineRowConstant Cbeta := by
  unfold gsA10PrimeSourceAffineRowConstant
    gsA10BetaSourceDensityConstant
  have hM := gsA10PrimeLogHarmonicFactorFourConstant_nonneg
  positivity

theorem gsA10PrimeSourceAffineRowSlope_nonneg
    {Cbeta : ℝ} (hCbeta : 1 ≤ Cbeta)
    {y X : ℕ} (hy : 1 ≤ y) (hX : 1 ≤ X) :
    0 ≤ gsA10PrimeSourceAffineRowSlope Cbeta y X := by
  unfold gsA10PrimeSourceAffineRowSlope gsA10BetaSourceDensityConstant
  have hlog : 0 ≤ Real.log ((4 * X : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 4 * X by omega))
  positivity

/-- A scheduled near-row estimate plus the inverse-radius far-shell theorem
give the precise affine row consumed by the cumulative-energy assembly. -/
theorem sum_gsA10PrimeWindow_log_div_gaussian_le_sourceAffineRow
    {Cbeta : ℝ} {y X n : ℕ} {R : ℝ} (hR : 1 ≤ R)
    (hnWindow : n ∈ gsA10PrimeWindow y X)
    (hnear :
      (∑ m ∈ gsA10PrimeNearWindow y X n,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤
        1536 * gsA10BetaSourceDensityConstant Cbeta / R +
          gsA10PrimeSourceAffineRowSlope Cbeta y X) :
    (∑ m ∈ gsA10PrimeWindow y X,
        (Real.log (m : ℝ) / m) *
          finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
            (Real.log m - Real.log n)) ≤
      gsA10PrimeSourceAffineRowConstant Cbeta / R +
        gsA10PrimeSourceAffineRowSlope Cbeta y X := by
  let term : ℕ → ℝ := fun m ↦
    (Real.log (m : ℝ) / m) *
      finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
        (Real.log m - Real.log n)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (gsA10PrimeWindow y X)
    (fun m ↦ m ∈ Finset.Ioc (n / 4) (4 * n)) term
  have hfar :=
    sum_gsA10PrimeFarWindow_log_div_gaussian_le_shell_constant_div
      hR hnWindow
  have hEq :
      (∑ m ∈ gsA10PrimeWindow y X, term m) =
        (∑ m ∈ gsA10PrimeNearWindow y X n, term m) +
          ∑ m ∈ gsA10PrimeFarWindow y X n, term m := by
    simpa only [gsA10PrimeNearWindow, gsA10PrimeFarWindow] using hsplit.symm
  change (∑ m ∈ gsA10PrimeWindow y X, term m) ≤ _
  rw [hEq]
  calc
    _ ≤ (1536 * gsA10BetaSourceDensityConstant Cbeta / R +
          gsA10PrimeSourceAffineRowSlope Cbeta y X) +
        (80 * gsA10PrimeLogHarmonicFactorFourConstant) / R :=
      add_le_add (by simpa only [term] using hnear)
        (by simpa only [term] using hfar)
    _ = gsA10PrimeSourceAffineRowConstant Cbeta / R +
        gsA10PrimeSourceAffineRowSlope Cbeta y X := by
      unfold gsA10PrimeSourceAffineRowConstant
      ring

/-- Row-dependent Schur followed by exact cancellation of the Gaussian
normalization.  This theorem retains the affine split instead of replacing
`1/R` by its worst value. -/
theorem intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (sigma R A B : ℝ) (hR : 0 < R)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ A / R + B) :
    (∫ t in -R..R,
        Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X sigma t)) ≤
      Real.exp 1 * (Real.sqrt Real.pi * (A + B * R) *
        (∑ n ∈ gsA10PrimeWindow y X,
          gsA10PrimeLambdaSchurWeight hmul y sigma n)) := by
  have hbase :=
    intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_rowDependentSchur
      hmul y X sigma R (fun _ ↦ A / R + B) hR hrow
  rw [sqrt_pi_div_inv_sq_local R hR] at hbase
  calc
    (∫ t in -R..R,
        Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X sigma t)) ≤
        Real.exp 1 *
          (Real.sqrt Real.pi * R *
            (∑ n ∈ gsA10PrimeWindow y X,
              gsA10PrimeLambdaSchurWeight hmul y sigma n *
                (A / R + B))) := by
      simpa only [Finset.mul_sum] using hbase
    _ = Real.exp 1 * (Real.sqrt Real.pi * (A + B * R) *
          (∑ n ∈ gsA10PrimeWindow y X,
            gsA10PrimeLambdaSchurWeight hmul y sigma n)) := by
      rw [← Finset.sum_mul]
      field_simp [ne_of_gt hR]

/-- The two opposite Tao shifts obtained from one uniform affine row.  The
left shift retains its exact `((X / y) : ℝ) ^ (2 * beta)` factor. -/
theorem two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) (beta R A B : ℝ)
    (hX : 2 ≤ X) (hbeta : 0 ≤ beta) (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ A / R + B) :
    (∫ t in -R..R,
        Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67b.EulerResidue.taoExponent X - beta) t)) ≤
      gsA10PrimeAffineEnergyConstant A
          (((X / y : ℕ) : ℝ) ^ (2 * beta)) X +
        gsA10PrimeAffineEnergySlope B
          (((X / y : ℕ) : ℝ) ^ (2 * beta)) X * R ∧
    (∫ t in -R..R,
        Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67b.EulerResidue.taoExponent X + beta) t)) ≤
      gsA10PrimeAffineEnergyConstant A 1 X +
        gsA10PrimeAffineEnergySlope B 1 X * R := by
  have hrowFactor : 0 ≤ A + B * R := by positivity
  have hleft := intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
    hmul y X (Erdos67b.EulerResidue.taoExponent X - beta) R A B hR hrow
  have hright := intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
    hmul y X (Erdos67b.EulerResidue.taoExponent X + beta) R A B hR hrow
  constructor
  · calc
      _ ≤ Real.exp 1 * (Real.sqrt Real.pi * (A + B * R) *
          (∑ n ∈ gsA10PrimeWindow y X,
            gsA10PrimeLambdaSchurWeight hmul y
              (Erdos67b.EulerResidue.taoExponent X - beta) n)) := hleft
      _ ≤ Real.exp 1 * (Real.sqrt Real.pi * (A + B * R) *
          ((((X / y : ℕ) : ℝ) ^ (2 * beta)) *
            gsA10PrimeLambdaHarmonicBudget X)) := by
        gcongr
        exact sum_gsA10PrimeLambdaSchurWeight_tao_sub_le
          hmul hbound hX hbeta
      _ = gsA10PrimeAffineEnergyConstant A
            (((X / y : ℕ) : ℝ) ^ (2 * beta)) X +
          gsA10PrimeAffineEnergySlope B
            (((X / y : ℕ) : ℝ) ^ (2 * beta)) X * R := by
        unfold gsA10PrimeAffineEnergyConstant gsA10PrimeAffineEnergySlope
        ring
  · calc
      _ ≤ Real.exp 1 * (Real.sqrt Real.pi * (A + B * R) *
          (∑ n ∈ gsA10PrimeWindow y X,
            gsA10PrimeLambdaSchurWeight hmul y
              (Erdos67b.EulerResidue.taoExponent X + beta) n)) := hright
      _ ≤ Real.exp 1 * (Real.sqrt Real.pi * (A + B * R) *
          gsA10PrimeLambdaHarmonicBudget X) := by
        gcongr
        exact sum_gsA10PrimeLambdaSchurWeight_tao_add_le
          hmul hbound hX hbeta
      _ = gsA10PrimeAffineEnergyConstant A 1 X +
          gsA10PrimeAffineEnergySlope B 1 X * R := by
        unfold gsA10PrimeAffineEnergyConstant gsA10PrimeAffineEnergySlope
        ring

/-- Dyadic Perron-weighted energies from a uniform affine row valid at all
radii through the chosen outer shell.  The shell count multiplies `E₁`
only; the inverse-radius local main term stays in `E₀`. -/
theorem two_gsA10WeightedVerticalEnergy_tao_le_affineRow
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) (beta sigma T A B : ℝ) (K : ℕ)
    (hX : 2 ≤ X) (hbeta : 0 ≤ beta) (hsigma : 1 / 2 ≤ sigma)
    (hT : 0 ≤ T) (hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      ∀ n ∈ gsA10PrimeWindow y X,
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤ A / R + B) :
    gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X - beta))
        sigma (-T) T ≤
      6 * gsA10PrimeAffineEnergyConstant A
          (((X / y : ℕ) : ℝ) ^ (2 * beta)) X +
        (2 + 4 * K) * gsA10PrimeAffineEnergySlope B
          (((X / y : ℕ) : ℝ) ^ (2 * beta)) X ∧
    gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X + beta))
        sigma (-T) T ≤
      6 * gsA10PrimeAffineEnergyConstant A 1 X +
        (2 + 4 * K) * gsA10PrimeAffineEnergySlope B 1 X := by
  let growth : ℝ := (((X / y : ℕ) : ℝ) ^ (2 * beta))
  have hgrowth : 0 ≤ growth := by dsimp only [growth]; positivity
  have hE0L : 0 ≤ gsA10PrimeAffineEnergyConstant A growth X :=
    gsA10PrimeAffineEnergyConstant_nonneg hA hgrowth X
  have hE1L : 0 ≤ gsA10PrimeAffineEnergySlope B growth X :=
    gsA10PrimeAffineEnergySlope_nonneg hB hgrowth X
  have hE0R : 0 ≤ gsA10PrimeAffineEnergyConstant A 1 X :=
    gsA10PrimeAffineEnergyConstant_nonneg hA (by norm_num) X
  have hE1R : 0 ≤ gsA10PrimeAffineEnergySlope B 1 X :=
    gsA10PrimeAffineEnergySlope_nonneg hB (by norm_num) X
  have henergyL : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67b.EulerResidue.taoExponent X - beta) t)) ≤
        gsA10PrimeAffineEnergyConstant A growth X +
          gsA10PrimeAffineEnergySlope B growth X * R := by
    intro R hR hRK
    simpa only [growth] using
      (two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow
        hmul hbound y X beta R A B hX hbeta (zero_lt_one.trans_le hR)
          hA hB (hrow R hR hRK)).1
  have henergyR : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67b.EulerResidue.taoExponent X + beta) t)) ≤
        gsA10PrimeAffineEnergyConstant A 1 X +
          gsA10PrimeAffineEnergySlope B 1 X * R := by
    intro R hR hRK
    exact (two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow
      hmul hbound y X beta R A B hX hbeta (zero_lt_one.trans_le hR)
        hA hB (hrow R hR hRK)).2
  constructor
  · simpa only [growth] using
      gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
        _ (continuous_gsA10PrimeLambdaPolynomial hmul y X _) hsigma
        hE0L hE1L hT K hTK henergyL
  · exact gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
      _ (continuous_gsA10PrimeLambdaPolynomial hmul y X _) hsigma
      hE0R hE1R hT K hTK henergyR

/-- Affine-row weighted energies with both exact prime-Lambda diagonals
retained.  This is the input for the symmetric beta square-root estimate. -/
theorem two_gsA10WeightedVerticalEnergy_tao_le_affineRow_diagonal
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (beta sigma T A B : ℝ) (K : ℕ)
    (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    (hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      ∀ n ∈ gsA10PrimeWindow y X,
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤ A / R + B) :
    let Q := Real.exp 1 * Real.sqrt Real.pi *
      (6 * A + (2 + 4 * K) * B)
    gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X - beta))
        sigma (-T) T ≤
      Q * (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X - beta) n) ∧
    gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X + beta))
        sigma (-T) T ≤
      Q * (∑ n ∈ gsA10PrimeWindow y X,
        gsA10PrimeLambdaSchurWeight hmul y
          (Erdos67b.EulerResidue.taoExponent X + beta) n) := by
  dsimp only
  let DL : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67b.EulerResidue.taoExponent X - beta) n
  let DR : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67b.EulerResidue.taoExponent X + beta) n
  have hDL : 0 ≤ DL := by
    dsimp only [DL]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hDR : 0 ≤ DR := by
    dsimp only [DR]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  let E0L := Real.exp 1 * Real.sqrt Real.pi * A * DL
  let E1L := Real.exp 1 * Real.sqrt Real.pi * B * DL
  let E0R := Real.exp 1 * Real.sqrt Real.pi * A * DR
  let E1R := Real.exp 1 * Real.sqrt Real.pi * B * DR
  have hE0L : 0 ≤ E0L := by dsimp only [E0L]; positivity
  have hE1L : 0 ≤ E1L := by dsimp only [E1L]; positivity
  have hE0R : 0 ≤ E0R := by dsimp only [E0R]; positivity
  have hE1R : 0 ≤ E1R := by dsimp only [E1R]; positivity
  have henergyL : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67b.EulerResidue.taoExponent X - beta) t)) ≤
        E0L + E1L * R := by
    intro R hR hRK
    have hbase := intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
      hmul y X (Erdos67b.EulerResidue.taoExponent X - beta) R A B
        (zero_lt_one.trans_le hR) (hrow R hR hRK)
    dsimp only [E0L, E1L, DL]
    convert hbase using 1
    ring
  have henergyR : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq
          (gsA10PrimeLambdaPolynomial hmul y X
            (Erdos67b.EulerResidue.taoExponent X + beta) t)) ≤
        E0R + E1R * R := by
    intro R hR hRK
    have hbase := intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
      hmul y X (Erdos67b.EulerResidue.taoExponent X + beta) R A B
        (zero_lt_one.trans_le hR) (hrow R hR hRK)
    dsimp only [E0R, E1R, DR]
    convert hbase using 1
    ring
  have hleft := gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
    _ (continuous_gsA10PrimeLambdaPolynomial hmul y X _) hsigma
      hE0L hE1L hT K hTK henergyL
  have hright := gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
    _ (continuous_gsA10PrimeLambdaPolynomial hmul y X _) hsigma
      hE0R hE1R hT K hTK henergyR
  constructor
  · dsimp only [E0L, E1L, DL] at hleft ⊢
    convert hleft using 1
    ring
  · dsimp only [E0R, E1R, DR] at hright ⊢
    convert hright using 1
    ring

/-- Contour-facing square-root product.  The common row factor is kept
outside the two diagonal square roots, where the beta-sensitive symmetric
diagonal theorem can be used without reverting to separate harmonic bounds. -/
theorem rpow_half_mul_gsA10WeightedVerticalEnergy_tao_le_affineRow_symmetric
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) (beta sigma T A B : ℝ) (K : ℕ)
    (hX : 2 ≤ X) (hN : 2 ≤ X / y)
    (hbeta : 0 ≤ beta) (hbetaHalf : beta ≤ 1 / 2)
    (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    (hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      ∀ n ∈ gsA10PrimeWindow y X,
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤ A / R + B) :
    (gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X - beta))
        sigma (-T) T) ^ ((1 : ℝ) / 2) *
      (gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X + beta))
        sigma (-T) T) ^ ((1 : ℝ) / 2) ≤
      (Real.exp 1 * Real.sqrt Real.pi *
        (6 * A + (2 + 4 * K) * B)) *
        (((X / y : ℕ) : ℝ) ^ beta *
          gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) := by
  let WL := gsA10WeightedVerticalEnergy
    (gsA10PrimeLambdaPolynomial hmul y X
      (Erdos67b.EulerResidue.taoExponent X - beta)) sigma (-T) T
  let WR := gsA10WeightedVerticalEnergy
    (gsA10PrimeLambdaPolynomial hmul y X
      (Erdos67b.EulerResidue.taoExponent X + beta)) sigma (-T) T
  let DL : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67b.EulerResidue.taoExponent X - beta) n
  let DR : ℝ := ∑ n ∈ gsA10PrimeWindow y X,
    gsA10PrimeLambdaSchurWeight hmul y
      (Erdos67b.EulerResidue.taoExponent X + beta) n
  let Q : ℝ := Real.exp 1 * Real.sqrt Real.pi *
    (6 * A + (2 + 4 * K) * B)
  have hDL : 0 ≤ DL := by
    dsimp only [DL]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hDR : 0 ≤ DR := by
    dsimp only [DR]
    apply Finset.sum_nonneg
    intro n hn
    unfold gsA10PrimeLambdaSchurWeight
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hWL : 0 ≤ WL := by
    dsimp only [WL, gsA10WeightedVerticalEnergy]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun t ht ↦ mul_nonneg
        (gsA10VerticalPerronWeight_nonneg _ _)
        (Complex.normSq_nonneg _))
  have hWR : 0 ≤ WR := by
    dsimp only [WR, gsA10WeightedVerticalEnergy]
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun t ht ↦ mul_nonneg
        (gsA10VerticalPerronWeight_nonneg _ _)
        (Complex.normSq_nonneg _))
  have hpair := two_gsA10WeightedVerticalEnergy_tao_le_affineRow_diagonal
    hmul y X beta sigma T A B K hsigma hT hTK hA hB hrow
  have hWLhalf : WL ^ ((1 : ℝ) / 2) ≤
      (Q * DL) ^ ((1 : ℝ) / 2) := by
    apply Real.rpow_le_rpow hWL
    · simpa only [WL, Q, DL] using hpair.1
    · norm_num
  have hWRhalf : WR ^ ((1 : ℝ) / 2) ≤
      (Q * DR) ^ ((1 : ℝ) / 2) := by
    apply Real.rpow_le_rpow hWR
    · simpa only [WR, Q, DR] using hpair.2
    · norm_num
  have hdiag :=
    rpow_half_sum_gsA10PrimeLambdaSchurWeight_symmetric_le
      hmul hbound hX hN hbeta hbetaHalf
  change WL ^ ((1 : ℝ) / 2) * WR ^ ((1 : ℝ) / 2) ≤ _
  calc
    WL ^ ((1 : ℝ) / 2) * WR ^ ((1 : ℝ) / 2) ≤
        (Q * DL) ^ ((1 : ℝ) / 2) *
          (Q * DR) ^ ((1 : ℝ) / 2) :=
      mul_le_mul hWLhalf hWRhalf (Real.rpow_nonneg hWR _)
        (Real.rpow_nonneg (mul_nonneg hQ hDL) _)
    _ = Q * (DL ^ ((1 : ℝ) / 2) * DR ^ ((1 : ℝ) / 2)) := by
      rw [Real.mul_rpow hQ hDL, Real.mul_rpow hQ hDR]
      have hQhalf : Q ^ ((1 : ℝ) / 2) * Q ^ ((1 : ℝ) / 2) = Q := by
        rw [← Real.sqrt_eq_rpow, Real.mul_self_sqrt hQ]
      calc
        _ = (Q ^ ((1 : ℝ) / 2) * Q ^ ((1 : ℝ) / 2)) *
            (DL ^ ((1 : ℝ) / 2) * DR ^ ((1 : ℝ) / 2)) := by ring
        _ = _ := by rw [hQhalf]
    _ ≤ Q * (((X / y : ℕ) : ℝ) ^ beta *
          gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) := by
      apply mul_le_mul_of_nonneg_left _ hQ
      simpa only [DL, DR] using hdiag
    _ = _ := by rfl

/-- Central-window transfer for an affine row which is available only at
radii `R ≥ L`.  Integrals below `L` are enlarged to the interval `[-L,L]`.
Consequently the shell factor still multiplies only `E₁`; the one-time
central charge `E₁ L` is placed in `E₀`. -/
theorem two_gsA10WeightedVerticalEnergy_tao_le_affineRow_above
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y X : ℕ) (beta sigma T A B L : ℝ) (K : ℕ)
    (hX : 2 ≤ X) (hbeta : 0 ≤ beta) (hsigma : 1 / 2 ≤ sigma)
    (hT : 0 ≤ T) (hTK : T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ))
    (hL : 1 ≤ L) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrow : ∀ R : ℝ, L ≤ R →
      ∀ n ∈ gsA10PrimeWindow y X,
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤ A / R + B) :
    gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X - beta))
        sigma (-T) T ≤
      6 * gsA10PrimeCentralAffineEnergyConstant A B L
          (((X / y : ℕ) : ℝ) ^ (2 * beta)) X +
        (2 + 4 * K) * gsA10PrimeAffineEnergySlope B
          (((X / y : ℕ) : ℝ) ^ (2 * beta)) X ∧
    gsA10WeightedVerticalEnergy
        (gsA10PrimeLambdaPolynomial hmul y X
          (Erdos67b.EulerResidue.taoExponent X + beta))
        sigma (-T) T ≤
      6 * gsA10PrimeCentralAffineEnergyConstant A B L 1 X +
        (2 + 4 * K) * gsA10PrimeAffineEnergySlope B 1 X := by
  let growth : ℝ := (((X / y : ℕ) : ℝ) ^ (2 * beta))
  let FL : ℝ → ℂ := gsA10PrimeLambdaPolynomial hmul y X
    (Erdos67b.EulerResidue.taoExponent X - beta)
  let FR : ℝ → ℂ := gsA10PrimeLambdaPolynomial hmul y X
    (Erdos67b.EulerResidue.taoExponent X + beta)
  have hgrowth : 0 ≤ growth := by dsimp only [growth]; positivity
  have hSL : 0 ≤ gsA10PrimeAffineEnergySlope B growth X :=
    gsA10PrimeAffineEnergySlope_nonneg hB hgrowth X
  have hSR : 0 ≤ gsA10PrimeAffineEnergySlope B 1 X :=
    gsA10PrimeAffineEnergySlope_nonneg hB (by norm_num) X
  have hCL : 0 ≤ gsA10PrimeCentralAffineEnergyConstant A B L growth X := by
    unfold gsA10PrimeCentralAffineEnergyConstant
    exact add_nonneg
      (gsA10PrimeAffineEnergyConstant_nonneg hA hgrowth X)
      (mul_nonneg hSL (zero_le_one.trans hL))
  have hCR : 0 ≤ gsA10PrimeCentralAffineEnergyConstant A B L 1 X := by
    unfold gsA10PrimeCentralAffineEnergyConstant
    exact add_nonneg
      (gsA10PrimeAffineEnergyConstant_nonneg hA (by norm_num) X)
      (mul_nonneg hSR (zero_le_one.trans hL))
  have hAtL := two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow
    hmul hbound y X beta L A B hX hbeta (zero_lt_one.trans_le hL)
      hA hB (hrow L le_rfl)
  have hFLcont : Continuous FL := by
    exact continuous_gsA10PrimeLambdaPolynomial hmul y X _
  have hFRcont : Continuous FR := by
    exact continuous_gsA10PrimeLambdaPolynomial hmul y X _
  have henergyL : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq (FL t)) ≤
        gsA10PrimeCentralAffineEnergyConstant A B L growth X +
          gsA10PrimeAffineEnergySlope B growth X * R := by
    intro R hR _hRK
    by_cases hRL : L ≤ R
    · have hdirect :=
        (two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow
          hmul hbound y X beta R A B hX hbeta
            (zero_lt_one.trans_le hR) hA hB (hrow R hRL)).1
      dsimp only [FL]
      calc
        _ ≤ gsA10PrimeAffineEnergyConstant A growth X +
            gsA10PrimeAffineEnergySlope B growth X * R := by
          simpa only [growth] using hdirect
        _ ≤ gsA10PrimeCentralAffineEnergyConstant A B L growth X +
            gsA10PrimeAffineEnergySlope B growth X * R := by
          unfold gsA10PrimeCentralAffineEnergyConstant
          have hnonneg := mul_nonneg hSL (zero_le_one.trans hL)
          linarith
    · have hRL' : R ≤ L := le_of_not_ge hRL
      have hmono : (∫ t in -R..R, Complex.normSq (FL t)) ≤
          ∫ t in -L..L, Complex.normSq (FL t) := by
        apply intervalIntegral.integral_mono_interval
          (by linarith) (by linarith) hRL'
        · exact ae_restrict_of_forall_mem measurableSet_Ioc
            (fun t ht ↦ Complex.normSq_nonneg _)
        · exact (Complex.continuous_normSq.comp hFLcont).intervalIntegrable _ _
      calc
        _ ≤ ∫ t in -L..L, Complex.normSq (FL t) := hmono
        _ ≤ gsA10PrimeCentralAffineEnergyConstant A B L growth X := by
          simpa only [FL, growth, gsA10PrimeCentralAffineEnergyConstant]
            using hAtL.1
        _ ≤ gsA10PrimeCentralAffineEnergyConstant A B L growth X +
            gsA10PrimeAffineEnergySlope B growth X * R := by
          have hnonneg := mul_nonneg hSL (zero_le_one.trans hR)
          linarith
  have henergyR : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      (∫ t in -R..R, Complex.normSq (FR t)) ≤
        gsA10PrimeCentralAffineEnergyConstant A B L 1 X +
          gsA10PrimeAffineEnergySlope B 1 X * R := by
    intro R hR _hRK
    by_cases hRL : L ≤ R
    · have hdirect :=
        (two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow
          hmul hbound y X beta R A B hX hbeta
            (zero_lt_one.trans_le hR) hA hB (hrow R hRL)).2
      dsimp only [FR]
      calc
        _ ≤ gsA10PrimeAffineEnergyConstant A 1 X +
            gsA10PrimeAffineEnergySlope B 1 X * R := hdirect
        _ ≤ gsA10PrimeCentralAffineEnergyConstant A B L 1 X +
            gsA10PrimeAffineEnergySlope B 1 X * R := by
          unfold gsA10PrimeCentralAffineEnergyConstant
          have hnonneg := mul_nonneg hSR (zero_le_one.trans hL)
          linarith
    · have hRL' : R ≤ L := le_of_not_ge hRL
      have hmono : (∫ t in -R..R, Complex.normSq (FR t)) ≤
          ∫ t in -L..L, Complex.normSq (FR t) := by
        apply intervalIntegral.integral_mono_interval
          (by linarith) (by linarith) hRL'
        · exact ae_restrict_of_forall_mem measurableSet_Ioc
            (fun t ht ↦ Complex.normSq_nonneg _)
        · exact (Complex.continuous_normSq.comp hFRcont).intervalIntegrable _ _
      calc
        _ ≤ ∫ t in -L..L, Complex.normSq (FR t) := hmono
        _ ≤ gsA10PrimeCentralAffineEnergyConstant A B L 1 X := by
          simpa only [FR, gsA10PrimeCentralAffineEnergyConstant] using hAtL.2
        _ ≤ gsA10PrimeCentralAffineEnergyConstant A B L 1 X +
            gsA10PrimeAffineEnergySlope B 1 X * R := by
          have hnonneg := mul_nonneg hSR (zero_le_one.trans hR)
          linarith
  constructor
  · simpa only [FL, growth] using
      gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
        FL hFLcont hsigma hCL hSL hT K hTK henergyL
  · simpa only [FR] using
      gsA10WeightedVerticalEnergy_le_of_dyadic_cumulative
        FR hFRcont hsigma hCR hSR hT K hTK henergyR

/-- Concrete source-scheduled prime-Lambda weighted energies.  The
height-independent row coefficient is universal once `Cbeta` is fixed;
the dyadic shell count multiplies only the source-small density and
finite-level remainder slope. -/
theorem exists_two_gsA10WeightedVerticalEnergy_tao_sourceSchedule :
    ∃ Cbeta : ℝ, ∃ N : ℕ, 1 ≤ Cbeta ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X : ℕ) (beta sigma T : ℝ) (K : ℕ),
        N ≤ y → 2 ≤ X → 0 ≤ beta → 1 / 2 ≤ sigma → 0 ≤ T →
        T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
        gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul y X
              (Erdos67b.EulerResidue.taoExponent X - beta))
            sigma (-T) T ≤
          6 * gsA10PrimeSourceEnergyConstant Cbeta
              (((X / y : ℕ) : ℝ) ^ (2 * beta)) X +
            (2 + 4 * K) * gsA10PrimeSourceEnergySlope Cbeta y X
              (((X / y : ℕ) : ℝ) ^ (2 * beta)) ∧
        gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul y X
              (Erdos67b.EulerResidue.taoExponent X + beta))
            sigma (-T) T ≤
          6 * gsA10PrimeSourceEnergyConstant Cbeta 1 X +
            (2 + 4 * K) * gsA10PrimeSourceEnergySlope Cbeta y X 1 := by
  obtain ⟨Cbeta, N₀, hCbeta, hnear⟩ :=
    exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_eventual_bound
  let N := max N₀ 1
  refine ⟨Cbeta, N, hCbeta, ?_⟩
  intro f hmul hbound y X beta sigma T K hNy hX hbeta hsigma hT hTK
  have hN₀y : N₀ ≤ y := (le_max_left N₀ 1).trans hNy
  have hy : 1 ≤ y := (le_max_right N₀ 1).trans hNy
  let A := gsA10PrimeSourceAffineRowConstant Cbeta
  let B := gsA10PrimeSourceAffineRowSlope Cbeta y X
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact gsA10PrimeSourceAffineRowConstant_nonneg hCbeta
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact gsA10PrimeSourceAffineRowSlope_nonneg hCbeta hy (by omega)
  have hrow : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      ∀ n ∈ gsA10PrimeWindow y X,
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤ A / R + B := by
    intro R hR _hRK n hn
    have hnearR := hnear y X n R hN₀y hn (zero_lt_one.trans_le hR)
    apply sum_gsA10PrimeWindow_log_div_gaussian_le_sourceAffineRow
      (Cbeta := Cbeta) hR hn
    dsimp only [B, gsA10PrimeSourceAffineRowSlope]
    convert hnearR using 1
    ring
  have hresult := two_gsA10WeightedVerticalEnergy_tao_le_affineRow
    hmul hbound y X beta sigma T A B K hX hbeta hsigma hT hTK
      hA hB hrow
  simpa only [A, B, gsA10PrimeSourceEnergyConstant,
    gsA10PrimeSourceEnergySlope] using hresult

/-- Contour-facing source-scheduled square-root product.  Unlike the two
separate energy bounds, this conclusion retains the beta-sensitive
symmetric diagonal budget. -/
theorem exists_rpow_half_mul_gsA10WeightedVerticalEnergy_tao_sourceSchedule_symmetric :
    ∃ Cbeta : ℝ, ∃ N : ℕ, 1 ≤ Cbeta ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (y X : ℕ) (beta sigma T : ℝ) (K : ℕ),
        N ≤ y → 2 ≤ X → 2 ≤ X / y →
        0 ≤ beta → beta ≤ 1 / 2 → 1 / 2 ≤ sigma → 0 ≤ T →
        T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
        (gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul y X
              (Erdos67b.EulerResidue.taoExponent X - beta))
            sigma (-T) T) ^ ((1 : ℝ) / 2) *
          (gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul y X
              (Erdos67b.EulerResidue.taoExponent X + beta))
            sigma (-T) T) ^ ((1 : ℝ) / 2) ≤
          gsA10PrimeSourceWeightedRowFactor Cbeta y X K *
            (((X / y : ℕ) : ℝ) ^ beta *
              gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) := by
  obtain ⟨Cbeta, N₀, hCbeta, hnear⟩ :=
    exists_sum_gsA10PrimeNearWindow_log_div_gaussian_source_uniform_eventual_bound
  let N := max N₀ 1
  refine ⟨Cbeta, N, hCbeta, ?_⟩
  intro f hmul hbound y X beta sigma T K hNy hX hN hbeta hbetaHalf
    hsigma hT hTK
  have hN₀y : N₀ ≤ y := (le_max_left N₀ 1).trans hNy
  have hy : 1 ≤ y := (le_max_right N₀ 1).trans hNy
  let A := gsA10PrimeSourceAffineRowConstant Cbeta
  let B := gsA10PrimeSourceAffineRowSlope Cbeta y X
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact gsA10PrimeSourceAffineRowConstant_nonneg hCbeta
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact gsA10PrimeSourceAffineRowSlope_nonneg hCbeta hy (by omega)
  have hrow : ∀ R : ℝ, 1 ≤ R →
      R ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
      ∀ n ∈ gsA10PrimeWindow y X,
        (∑ m ∈ gsA10PrimeWindow y X,
            (Real.log (m : ℝ) / m) *
              finiteHalaszGaussianPairKernel (R⁻¹ ^ 2)
                (Real.log m - Real.log n)) ≤ A / R + B := by
    intro R hR _hRK n hn
    have hnearR := hnear y X n R hN₀y hn (zero_lt_one.trans_le hR)
    apply sum_gsA10PrimeWindow_log_div_gaussian_le_sourceAffineRow
      (Cbeta := Cbeta) hR hn
    dsimp only [B, gsA10PrimeSourceAffineRowSlope]
    convert hnearR using 1
    ring
  have hresult :=
    rpow_half_mul_gsA10WeightedVerticalEnergy_tao_le_affineRow_symmetric
      hmul hbound y X beta sigma T A B K hX hN hbeta hbetaHalf
        hsigma hT hTK hA hB hrow
  simpa only [A, B, gsA10PrimeSourceWeightedRowFactor] using hresult

/-- The same paired estimate with the natural cutoff
`ceil (exp (sqrt (log X)))` inserted.  The remaining condition is a single
finite threshold on `X`, since the source cutoff tends to infinity. -/
theorem exists_two_gsA10WeightedVerticalEnergy_tao_sourceCutoff :
    ∃ Cbeta : ℝ, ∃ N : ℕ, 1 ≤ Cbeta ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (X : ℕ) (beta sigma T : ℝ) (K : ℕ),
        N ≤ gsA10SourceCutoff X → 2 ≤ X → 0 ≤ beta →
        1 / 2 ≤ sigma → 0 ≤ T →
        T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
        gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul (gsA10SourceCutoff X) X
              (Erdos67b.EulerResidue.taoExponent X - beta))
            sigma (-T) T ≤
          6 * gsA10PrimeSourceEnergyConstant Cbeta
              (((X / gsA10SourceCutoff X : ℕ) : ℝ) ^ (2 * beta)) X +
            (2 + 4 * K) *
              gsA10PrimeSourceEnergySlope Cbeta (gsA10SourceCutoff X) X
                (((X / gsA10SourceCutoff X : ℕ) : ℝ) ^ (2 * beta)) ∧
        gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul (gsA10SourceCutoff X) X
              (Erdos67b.EulerResidue.taoExponent X + beta))
            sigma (-T) T ≤
          6 * gsA10PrimeSourceEnergyConstant Cbeta 1 X +
            (2 + 4 * K) *
              gsA10PrimeSourceEnergySlope Cbeta (gsA10SourceCutoff X) X 1 := by
  obtain ⟨Cbeta, N, hCbeta, hraw⟩ :=
    exists_two_gsA10WeightedVerticalEnergy_tao_sourceSchedule
  refine ⟨Cbeta, N, hCbeta, ?_⟩
  intro f hmul hbound X beta sigma T K hN hX hbeta hsigma hT hTK
  exact hraw hmul hbound (gsA10SourceCutoff X) X beta sigma T K
    hN hX hbeta hsigma hT hTK

/-- Natural-source-cutoff version of the contour-facing symmetric product. -/
theorem exists_rpow_half_mul_gsA10WeightedVerticalEnergy_tao_sourceCutoff_symmetric :
    ∃ Cbeta : ℝ, ∃ N : ℕ, 1 ≤ Cbeta ∧
      ∀ {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
        (_hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
        (X : ℕ) (beta sigma T : ℝ) (K : ℕ),
        N ≤ gsA10SourceCutoff X → 2 ≤ X →
        2 ≤ X / gsA10SourceCutoff X →
        0 ≤ beta → beta ≤ 1 / 2 → 1 / 2 ≤ sigma → 0 ≤ T →
        T ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) →
        (gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul (gsA10SourceCutoff X) X
              (Erdos67b.EulerResidue.taoExponent X - beta))
            sigma (-T) T) ^ ((1 : ℝ) / 2) *
          (gsA10WeightedVerticalEnergy
            (gsA10PrimeLambdaPolynomial hmul (gsA10SourceCutoff X) X
              (Erdos67b.EulerResidue.taoExponent X + beta))
            sigma (-T) T) ^ ((1 : ℝ) / 2) ≤
          gsA10PrimeSourceWeightedRowFactor Cbeta
              (gsA10SourceCutoff X) X K *
            (((X / gsA10SourceCutoff X : ℕ) : ℝ) ^ beta *
              gsA10PrimeLambdaSymmetricBetaDiagonalBudget X beta) := by
  obtain ⟨Cbeta, N, hCbeta, hraw⟩ :=
    exists_rpow_half_mul_gsA10WeightedVerticalEnergy_tao_sourceSchedule_symmetric
  refine ⟨Cbeta, N, hCbeta, ?_⟩
  intro f hmul hbound X beta sigma T K hN hX hquot hbeta hbetaHalf
    hsigma hT hTK
  exact hraw hmul hbound (gsA10SourceCutoff X) X beta sigma T K
    hN hX hquot hbeta hbetaHalf hsigma hT hTK

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.intervalIntegral_normSq_gsA10PrimeLambdaPolynomial_le_affineRow
#print axioms
  Erdos67b.MRHalaszBands.two_intervalIntegral_normSq_gsA10PrimeLambda_tao_le_affineRow
#print axioms
  Erdos67b.MRHalaszBands.two_gsA10WeightedVerticalEnergy_tao_le_affineRow
#print axioms
  Erdos67b.MRHalaszBands.two_gsA10WeightedVerticalEnergy_tao_le_affineRow_above
#print axioms
  Erdos67b.MRHalaszBands.sum_gsA10PrimeWindow_log_div_gaussian_le_sourceAffineRow
#print axioms
  Erdos67b.MRHalaszBands.exists_two_gsA10WeightedVerticalEnergy_tao_sourceSchedule
#print axioms
  Erdos67b.MRHalaszBands.exists_two_gsA10WeightedVerticalEnergy_tao_sourceCutoff
#print axioms
  Erdos67b.MRHalaszBands.two_gsA10WeightedVerticalEnergy_tao_le_affineRow_diagonal
#print axioms
  Erdos67b.MRHalaszBands.rpow_half_mul_gsA10WeightedVerticalEnergy_tao_le_affineRow_symmetric
#print axioms
  Erdos67b.MRHalaszBands.exists_rpow_half_mul_gsA10WeightedVerticalEnergy_tao_sourceSchedule_symmetric
#print axioms
  Erdos67b.MRHalaszBands.exists_rpow_half_mul_gsA10WeightedVerticalEnergy_tao_sourceCutoff_symmetric
