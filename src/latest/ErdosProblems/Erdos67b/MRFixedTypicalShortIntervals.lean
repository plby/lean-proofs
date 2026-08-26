import ErdosProblems.Erdos67b.MRFixedTypicalEnergy
import ErdosProblems.Erdos67b.MRShortIntervalBudget

/-!
# Quantitative short sums retaining one fixed typical family

The family and ambient thresholds precede every partial short length and
cutoff. This is the form needed before a residue/character expansion.
-/

open Finset MeasureTheory
open scoped Interval

namespace Erdos67b

noncomputable section

theorem mrExists_fixed_typical_short_meanSquare
    {eta p q c epsilon : ℝ} (heta0 : 0 < eta) (heta1 : eta ≤ 1 / 12)
    (hp : 2 ≤ p) (hq : 1 ≤ q) (hpq : 2 * p ≤ q)
    (hlogq : 1 ≤ Real.log q) (hbudget : 4096 * Real.log q ≤ eta * p)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q - Real.log p)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2) (hepsilon : 0 < epsilon) :
    ∃ K M₀ X₀ : ℕ, 0 < K ∧ 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ {h Z : ℕ}, 0 < h → h ≤ X → 2 * X ≤ Z →
        (∑ n ∈ Finset.Ioc X (2 * X),
          Complex.normSq (typicalModulatedShortSum (mrScheduledBlocks p q K) Z f n h 0)) ≤
          4 * lemma14UniversalScaledLowConstant *
              (2 * mrFirstSmallRelativeBudget eta p q c + epsilon) * (h : ℝ) ^ 2 * X +
            512 * lemma14UniversalScaledHighConstant * X * (c⁻¹ + Real.pi / c ^ 2) +
              (h : ℝ) ^ 3 := by
  obtain ⟨K, M₀, X₀, hK, hM₀, hX₀, henergy⟩ :=
    mrExists_fixed_typical_energy_le_relativeBudget heta0 heta1 hp hq hpq hlogq hbudget
      hmertens hc0.le hc1 hepsilon
  refine ⟨K, M₀, X₀, hK, hM₀, hX₀, ?_⟩
  intro M X hM hX f hmul hbound hnonpret h Z hh hhX hZ
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hE := henergy hM hX hmul hbound hnonpret (mul_pos hc0 hXpos).le
    (le_refl (c * (X : ℝ)))
  have hvertical : (∫ t in -(c * X)..(c * X), Complex.normSq
      (dyadicVerticalDirichletPolynomial (typicalFactorizationSet (mrScheduledBlocks p q K) Z)
        f X t)) ≤ 2 * mrFirstSmallRelativeBudget eta p q c + epsilon := by
    rw [integral_dyadicVerticalDirichletPolynomial_typical_eq _ f hZ]
    exact hE
  have hsmall : 0 ≤ 2 * mrFirstSmallRelativeBudget eta p q c + epsilon :=
    add_nonneg (mul_nonneg (by norm_num) (mrFirstSmallRelativeBudget_nonneg eta p q hc0.le))
      hepsilon.le
  have hshort := mrDyadicShortInterval_le_energy_meanTail
    (typicalFactorizationSet (mrScheduledBlocks p q K) Z) hbound hh hhX hc0 hsmall hvertical
  have hboundary := sum_normSq_typicalModulatedShortSum_le_dyadic_add_boundary
    (mrScheduledBlocks p q K) Z hbound X h
  linarith

end

end Erdos67b
