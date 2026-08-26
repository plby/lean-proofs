import ErdosProblems.Erdos67b.MRRealCentralWindowDistance
import ErdosProblems.Erdos67b.MRGSA10MovingRpowRestoredIntegrated

/-!
# The real large-zero branch on the moving A.10 contour

The real prefix dichotomy retains a large pretentious distance at the zero
twist.  The shrinking-pole argument in `MRRealCentralWindowDistance` turns
this into the pointwise distance lower bound on the complete fixed-high A.10
window.  This file inserts that conclusion into the restored moving-power
Perron theorem.  In particular, the remote minimizing twist is not needed
for the central contour estimate.
-/

open Filter
open scoped ComplexConjugate

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The exact pointwise scalar left by the restored fixed-high Perron
estimate when the moving power is retained. -/
def gsA10RestoredFixedHighMovingRpowBudget
    (Cbeta : ℝ) (Q S y A X : ℕ) (alpha beta T : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ((gsA10RestoredFixedHighHalaszEnvelope A X *
        gsA10MovingPerronKernelScale X alpha beta) *
          (gsA10PrimeLambdaLeftEnergyBound Cbeta Q S X y
            (2 * beta) T) ^ ((1 : ℝ) / 2) *
        (gsA10PrimeLambdaRightEnergyBound Cbeta Q S y X T) ^
          ((1 : ℝ) / 2) +
      2 * T *
        (gsA10RestoredFixedHighHalaszEnvelope A X *
          gsA10MovingPerronKernelScale X alpha beta) *
        ((X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) *
          (2 * gsA10PrimeLambdaHarmonicBudget X *
              gsA10HigherPrimePowerGeometricMass y X +
            (gsA10HigherPrimePowerGeometricMass y X) ^ 2)))

/-- Normalized form of the integrated moving-power budget. -/
def gsA10MovingRpowRestoredNormalizedBudget
    (Cbeta : ℝ) (Q S y A X : ℕ) (eta T : ℝ) : ℝ :=
  2 * (2 * Real.pi)⁻¹ *
    gsA10MovingRpowRestoredCoefficient Cbeta Q S y A X T *
      (2 * Real.exp 1 * eta / Real.log (X : ℝ))

/-- Dividing the integrated moving-power estimate by the prefix length
cancels its sole factor of `X` exactly. -/
theorem gsA10MovingRpowRestoredIntegrated_rhs_div_eq_normalized
    {Cbeta : ℝ} {Q S y A X : ℕ} {eta T : ℝ} (hX : 1 < X) :
    (2 * (2 * Real.pi)⁻¹ *
          gsA10MovingRpowRestoredCoefficient Cbeta Q S y A X T *
            (2 * Real.exp 1 * eta *
              ((X : ℝ) / Real.log (X : ℝ)))) / (X : ℝ) =
      gsA10MovingRpowRestoredNormalizedBudget
        Cbeta Q S y A X eta T := by
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
  have hlogX : Real.log (X : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hX)).ne'
  unfold gsA10MovingRpowRestoredNormalizedBudget
  field_simp [hXR, hlogX]

/-- A large zero-frequency distance at `3 * X` gives the actual restored
moving-power A.10 contour estimate at every prefix `Z ∈ [X,3X]`.  The
distance hypothesis of the complex contour theorem is fully discharged;
the remaining right side is its explicit finite prime-window scalar. -/
theorem exists_eventually_norm_gsA10MovingPerronIntegral_real_largeZero_le_movingRpow :
    ∃ Cbeta : ℝ, 1 ≤ Cbeta ∧
      ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ)
        (hmul : IsMultiplicativeOnPositiveNat f),
        (∀ n, 0 < n → conj (f n) = f n) →
        (∀ n, ‖f n‖ ≤ 1) →
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
          pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
        ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ∀ (P1 P2 : ℕ → Prop) [DecidablePred P1] [DecidablePred P2],
        (∀ p ∈ gsA9SmallPrimeFinset, P1 p) →
        ∀ {y Q S : ℕ}, 23 ≤ y → 3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cbeta ≤ 2 * (S - 100 : ℕ) / 99 →
        6 ≤ Real.log (y : ℝ) →
        (Real.log (Z : ℝ)) ^ 2 ≤ Z →
        ∀ {alpha beta : ℝ}, 0 ≤ alpha →
        alpha ≤ (Real.log (y : ℝ))⁻¹ →
        0 ≤ beta → beta ≤ (Real.log (y : ℝ))⁻¹ →
        ‖gsA10TwoBlockMovingPerronIntegral
            f hmul P1 P2 y Z alpha beta
              ((Real.log (Z : ℝ)) ^ 2)‖ ≤
          gsA10RestoredFixedHighMovingRpowBudget Cbeta Q S y
            (realPrefixMovingThreshold X) Z alpha beta
              ((Real.log (Z : ℝ)) ^ 2) := by
  obtain ⟨Cbeta, hCbeta, hperron⟩ :=
    exists_norm_gsA10MovingPerronIntegral_fixedHigh_restored_le_movingRpow
  refine ⟨Cbeta, hCbeta, ?_⟩
  filter_upwards
      [Erdos67b.eventually_real_centralWindow_at_prefix_of_large_zero_three_mul,
        eventually_ge_atTop 2] with X hcentral hX
  intro f hmul hreal hbound hzero Z hXZ hZX P1 P2 _ _ hsmall
    y Q S hy hQ hQy hS hlogCbeta hlogy hlogZsqZ alpha beta
    halpha0 halpha hbeta0 hbeta
  have hZ : 2 ≤ Z := hX.trans hXZ
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hdist : ∀ t : ℝ, |t| ≤ (Real.log (Z : ℝ)) ^ 2 →
      (realPrefixMovingThreshold X : ℝ) ≤
        pretentiousDistSq f (archimedeanTwist t) Z :=
    hcentral f hreal hbound hzero Z hXZ hZX
  have hraw := hperron hmul (fun n hn ↦ hbound n) P1 P2 hsmall hy hZ
    hQ hQy hS hlogCbeta hlogy halpha0 halpha hbeta0 hbeta
    (sq_pos_of_pos hlogZ) hlogZsqZ hdist
  simpa only [gsA10RestoredFixedHighMovingRpowBudget] using hraw

/-- Integrated source-rectangle form of the real large-zero estimate.
Exact moving-power cancellation has already been performed. -/
theorem exists_eventually_norm_gsA10MovingPerronIntegrated_real_largeZero_le_movingRpow :
    ∃ Cbeta : ℝ, 1 ≤ Cbeta ∧
      ∀ᶠ X : ℕ in atTop, ∀ (f : ℕ → ℂ)
        (hmul : IsMultiplicativeOnPositiveNat f),
        (∀ n, 0 < n → conj (f n) = f n) →
        (∀ n, ‖f n‖ ≤ 1) →
        (3 / 4 : ℝ) * Real.log (Real.log (X : ℝ)) <
          pretentiousDistSq f (archimedeanTwist 0) (3 * X) →
        ∀ Z : ℕ, X ≤ Z → Z ≤ 3 * X →
        ∀ (P1 P2 : ℕ → Prop) [DecidablePred P1] [DecidablePred P2],
        (∀ p ∈ gsA9SmallPrimeFinset, P1 p) →
        ∀ {y Q S : ℕ}, 23 ≤ y → y ≤ Z →
        3 ≤ Q → Q ≤ y → 101 ≤ S →
        Real.log Cbeta ≤ 2 * (S - 100 : ℕ) / 99 →
        6 ≤ Real.log (y : ℝ) →
        (Real.log (Z : ℝ)) ^ 2 ≤ Z →
        ∀ {eta : ℝ}, 0 ≤ eta →
        eta ≤ (Real.log (y : ℝ))⁻¹ →
        ‖gsA10TwoBlockMovingPerronIntegrated
            f hmul P1 P2 y Z eta ((Real.log (Z : ℝ)) ^ 2)‖ ≤
          2 * (2 * Real.pi)⁻¹ *
            gsA10MovingRpowRestoredCoefficient Cbeta Q S y
              (realPrefixMovingThreshold X) Z
                ((Real.log (Z : ℝ)) ^ 2) *
              (2 * Real.exp 1 * eta *
                ((Z : ℝ) / Real.log (Z : ℝ))) := by
  obtain ⟨Cbeta, hCbeta, hperron⟩ :=
    exists_norm_gsA10TwoBlockMovingPerronIntegrated_restored_le_movingRpow
  refine ⟨Cbeta, hCbeta, ?_⟩
  filter_upwards
      [Erdos67b.eventually_real_centralWindow_at_prefix_of_large_zero_three_mul,
        eventually_ge_atTop 2] with X hcentral hX
  intro f hmul hreal hbound hzero Z hXZ hZX P1 P2 _ _ hsmall
    y Q S hy hyZ hQ hQy hS hlogCbeta hlogy hlogZsqZ eta heta0 heta
  have hZ : 2 ≤ Z := hX.trans hXZ
  have hlogZ : 0 < Real.log (Z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hdist : ∀ t : ℝ, |t| ≤ (Real.log (Z : ℝ)) ^ 2 →
      (realPrefixMovingThreshold X : ℝ) ≤
        pretentiousDistSq f (archimedeanTwist t) Z :=
    hcentral f hreal hbound hzero Z hXZ hZX
  exact hperron hmul (fun n hn ↦ hbound n) P1 P2 hsmall hy hyZ hZ
    hQ hQy hS hlogCbeta hlogy heta0 heta (sq_pos_of_pos hlogZ)
    hlogZsqZ hdist

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.exists_eventually_norm_gsA10MovingPerronIntegral_real_largeZero_le_movingRpow
#print axioms
  Erdos67b.MRHalaszBands.exists_eventually_norm_gsA10MovingPerronIntegrated_real_largeZero_le_movingRpow
