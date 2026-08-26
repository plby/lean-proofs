import ErdosProblems.Erdos520.HarperGaussianVaryingWalk
import ErdosProblems.Erdos520.HarperBlockLaw
import ErdosProblems.Erdos520.HarperPrimeBlockAsymptotic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem520

noncomputable section

noncomputable def harperScheduledGaussianVariance
    (y start n : ℕ) (t : ℝ) (i : Fin n) : ℝ≥0 :=
  harperLinearBlockVarianceNNReal y
    (harperScheduledPrimeBlock y (start + i.val)) t t

noncomputable def harperScheduledGaussianProductMeasure
    (y start n : ℕ) (t : ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi fun i ↦ gaussianReal 0
    (harperScheduledGaussianVariance y start n t i)

instance harperScheduledGaussianProductMeasure_isProbabilityMeasure
    (y start n : ℕ) (t : ℝ) :
    IsProbabilityMeasure (harperScheduledGaussianProductMeasure y start n t) := by
  unfold harperScheduledGaussianProductMeasure
  infer_instance

theorem exists_eventually_harperScheduledGaussianVariance_third_threeEighths
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ i : Fin n,
            (1 / 3 : ℝ≥0) ≤ harperScheduledGaussianVariance y start n t i ∧
              harperScheduledGaussianVariance y start n t i ≤ (3 / 8 : ℝ≥0) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledDiagonalVariance_third_threeEighths M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper i
  have hindex : J ≤ start + i.val :=
    hstart.trans (Nat.le_add_right start i.val)
  have hendpoint : harperBlockEndpoint (start + i.val + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hv := hJ (start + i.val) hindex y hendpoint t htLower htUpper
  constructor
  · exact_mod_cast hv.1.le
  · exact_mod_cast hv.2.le

theorem exists_eventually_harperScheduledGaussianWalk_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ x : ℝ, 0 ≤ x →
          (harperScheduledGaussianProductMeasure y start n t).real
              (gaussianWalkSurvivalSet n x) ≤
            64 * (x + 2) / Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledGaussianVariance_third_threeEighths M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper x hx
  have hvar := hJ start hstart n y hy t htLower htUpper
  have h := gaussianVarianceWalk_third_threeEighths_probability_le_fin
    n hn (harperScheduledGaussianVariance y start n t) hx
    (fun i ↦ (hvar i).1) (fun i ↦ (hvar i).2)
  simpa only [harperScheduledGaussianProductMeasure] using! h

theorem exists_eventually_harperScheduledGaussianWalk_timeBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ (s B : ℝ) (b : Fin n → ℝ), 0 ≤ B - s → (∀ i, b i ≤ B) →
            (harperScheduledGaussianProductMeasure y start n t).real
                (gaussianWalkTimeBarrierSet n s b) ≤
              64 * (B - s + 2) / Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledGaussianWalk_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper s B b hstartB hb
  have hsubset : gaussianWalkTimeBarrierSet n s b ⊆
      gaussianWalkSurvivalSet n (B - s) := by
    intro omega homega
    have hflat := gaussianWalkTimeBarrierSurvives_mono n s hb homega
    exact (gaussianWalkTimeBarrierSurvives_const_iff n s B omega).1 hflat
  exact (measureReal_mono hsubset).trans
    (hJ start hstart n hn y hy t htLower htUpper (B - s) hstartB)

theorem exists_eventually_harperScheduledGaussianWalk_logBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M →
          ∀ x c : ℝ, 0 ≤ x → 0 ≤ c →
            (harperScheduledGaussianProductMeasure y start n t).real
                (gaussianWalkTimeBarrierSet n 0
                  (fun i ↦ x + c * Real.log ((i.val + 2 : ℕ) : ℝ))) ≤
              64 * (x + c * Real.log ((n + 1 : ℕ) : ℝ) + 2) /
                Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledGaussianVariance_third_threeEighths M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper x c hx hc
  have hvar := hJ start hstart n y hy t htLower htUpper
  have h := gaussianVarianceWalk_third_threeEighths_logBarrier_probability_le_fin
    n hn (harperScheduledGaussianVariance y start n t) hx hc
    (fun i ↦ (hvar i).1) (fun i ↦ (hvar i).2)
  simpa only [harperScheduledGaussianProductMeasure] using! h

end
end Erdos.Problem520
