import ErdosProblems.Erdos421.TorusMoments

/-! # Integrating the moments of all polynomial prefixes -/

namespace Erdos421

open MeasureTheory

noncomputable local instance polynomialPrefixCircleMeasure : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance polynomialPrefixCircleHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance polynomialPrefixCircleProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

noncomputable def polynomialPrefixMoment (k M p : ℕ) (a : UnitAddTorus (Fin k)) : ℝ :=
  ∑ m ∈ Finset.range (M + 1), ‖torusVinogradovWeylSum k m a‖ ^ p

theorem polynomialPrefixMoment_nonneg (k M p : ℕ) (a : UnitAddTorus (Fin k)) :
    0 ≤ polynomialPrefixMoment k M p a :=
  Finset.sum_nonneg (fun _ _ ↦ pow_nonneg (norm_nonneg _) _)

theorem continuous_polynomialPrefixMoment (k M p : ℕ) :
    Continuous (polynomialPrefixMoment k M p) := by
  apply continuous_finsetSum
  intro m _
  exact (continuous_torusCharacterSum Finset.univ
    (vinogradovIntegerPoint k : Fin m → Fin k → ℤ)).norm.pow p

theorem integrable_polynomialPrefixMoment (k M p : ℕ) :
    Integrable (polynomialPrefixMoment k M p) :=
  (continuous_polynomialPrefixMoment k M p).integrable_of_hasCompactSupport
    (isClosed_tsupport _).isCompact

theorem integral_polynomialPrefixMoment (s k M : ℕ) :
    (∫ a : UnitAddTorus (Fin k), polynomialPrefixMoment k M (2 * s) a) =
      ∑ m ∈ Finset.range (M + 1), (vinogradovCount s k m : ℝ) := by
  unfold polynomialPrefixMoment
  rw [integral_finsetSum]
  · simp only [torusVinogradovWeylSum_moment]
  · intro m _
    have hcont := (continuous_torusCharacterSum Finset.univ
      (vinogradovIntegerPoint k : Fin m → Fin k → ℤ)).norm.pow (2 * s)
    exact hcont.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

theorem integral_polynomialPrefixMoment_le (s k M : ℕ) :
    (∫ a : UnitAddTorus (Fin k), polynomialPrefixMoment k M (2 * s) a) ≤
      (M + 1 : ℕ) * (vinogradovCount s k M : ℝ) := by
  rw [integral_polynomialPrefixMoment]
  calc
    _ ≤ ∑ _m ∈ Finset.range (M + 1), (vinogradovCount s k M : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact Nat.cast_le.mpr (vinogradovCount_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) s k)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Erdos421
