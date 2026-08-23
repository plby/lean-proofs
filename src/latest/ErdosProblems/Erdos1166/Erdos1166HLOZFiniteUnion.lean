import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalProduct

/-!
The finite conditional-product/union-bound step in HLOZ Proposition 4.9,
equations (4.55)--(4.58).
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1166.HLOZFiniteUnion

variable {ι : Type*} [Fintype ι]

/-- The event that at least one candidate coordinate falls in its prescribed
narrow band. -/
def anyCoordinateInBand (candidate : Finset ι) (band : ι → Set ℕ) :
    Set (ι → ℕ) :=
  ⋃ i : ↥candidate, Function.eval i.1 ⁻¹' band i.1

omit [Fintype ι] in theorem measurableSet_anyCoordinateInBand
    (candidate : Finset ι) (band : ι → Set ℕ)
    (hband : ∀ i ∈ candidate, MeasurableSet (band i)) :
    MeasurableSet (anyCoordinateInBand candidate band) := by
  apply MeasurableSet.iUnion
  intro i
  exact (hband i.1 i.2).preimage (measurable_pi_apply i.1)

/-- Under the independent product of the coordinate laws, the chance that
some candidate coordinate lies in its narrow band is bounded by the number
of candidates times a uniform one-coordinate bound. Independence is used to
identify each coordinate marginal; the last step is only the finite union
bound. -/
theorem independent_anyCoordinateInBand_le_card_mul
    (coordinateLaw : ι → PMF ℕ)
    (candidate : Finset ι) (band : ι → Set ℕ)
    (hbandMeas : ∀ i ∈ candidate, MeasurableSet (band i))
    {r : ℝ≥0∞}
    (hband : ∀ i ∈ candidate,
      (coordinateLaw i).toMeasure (band i) ≤ r) :
    (Measure.pi fun i ↦ (coordinateLaw i).toMeasure)
        (anyCoordinateInBand candidate band) ≤
      (candidate.card : ℝ≥0∞) * r := by
  rw [anyCoordinateInBand]
  calc
    (Measure.pi fun i ↦ (coordinateLaw i).toMeasure)
          (⋃ i : ↥candidate, Function.eval i.1 ⁻¹' band i.1) ≤
        ∑ i : ↥candidate,
          (Measure.pi fun i ↦ (coordinateLaw i).toMeasure)
            (Function.eval i.1 ⁻¹' band i.1) :=
      measure_iUnion_fintype_le _ _
    _ = ∑ i : ↥candidate, (coordinateLaw i.1).toMeasure (band i.1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        (Measure.pi fun j ↦ (coordinateLaw j).toMeasure)
            (Function.eval i.1 ⁻¹' band i.1) =
            ((Measure.pi fun j ↦ (coordinateLaw j).toMeasure).map
              (Function.eval i.1)) (band i.1) := by
              rw [Measure.map_apply (measurable_pi_apply i.1)
                (hbandMeas i.1 i.2)]
        _ = (coordinateLaw i.1).toMeasure (band i.1) := by
          rw [(measurePreserving_eval
            (fun j ↦ (coordinateLaw j).toMeasure) i.1).map_eq]
    _ ≤ ∑ _i : ↥candidate, r := by
      exact Finset.sum_le_sum fun i _hi ↦ hband i.1 i.2
    _ = (candidate.card : ℝ≥0∞) * r := by simp

/-- A coordinate law filtered to a broad admissible band. -/
noncomputable def filteredCoordinateLaw
    (baseLaw : ι → PMF ℕ) (broadBand : ι → Set ℕ)
    (hpos : ∀ i, ∃ x ∈ broadBand i, x ∈ (baseLaw i).support)
    (i : ι) : PMF ℕ :=
  (baseLaw i).filter (broadBand i) (hpos i)

/-- The product of the independently filtered coordinate laws. This is the
law supplied by `HLOZConditionalProduct.filter_blockEvent_apply_eq_prod`
after the source-specific external path has been fixed. -/
noncomputable def independentFilteredMeasure
    (baseLaw : ι → PMF ℕ) (broadBand : ι → Set ℕ)
    (hpos : ∀ i, ∃ x ∈ broadBand i, x ∈ (baseLaw i).support) :
    Measure (ι → ℕ) :=
  Measure.pi fun i ↦ (filteredCoordinateLaw baseLaw broadBand hpos i).toMeasure

/-- The conditional-product identity, promoted from singleton masses to an
equality of measures.  This is the direct bridge from
`HLOZConditionalProduct.filter_blockEvent_apply_eq_prod` to the independent
filtered measure used by the union-bound lemmas below. -/
theorem filter_blockEvent_toMeasure_eq_independentFilteredMeasure
    (jointLaw : PMF (ι → ℕ)) (coordinateLaw : ι → PMF ℕ)
    (hprod : ∀ x, jointLaw x = ∏ i, coordinateLaw i (x i))
    (broadBand : ∀ _i, Finset ℕ)
    (hpos : ∀ i, ∃ x ∈ (broadBand i : Set ℕ),
      x ∈ (coordinateLaw i).support) :
    (jointLaw.filter
      (HLOZConditionalProduct.blockEvent broadBand)
      (HLOZConditionalProduct.blockEvent_meets_support
        jointLaw coordinateLaw hprod broadBand hpos)).toMeasure =
      independentFilteredMeasure coordinateLaw
        (fun i ↦ (broadBand i : Set ℕ)) hpos := by
  apply Measure.ext_of_singleton
  intro x
  rw [PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x)]
  rw [independentFilteredMeasure, Measure.pi_singleton]
  rw [HLOZConditionalProduct.filter_blockEvent_apply_eq_prod
    jointLaw coordinateLaw hprod broadBand hpos x]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [filteredCoordinateLaw,
    PMF.toMeasure_apply_singleton _ (x i) (measurableSet_singleton (x i))]

/-- Finite union bound for independently filtered coordinates. -/
theorem independentFiltered_anyCoordinateInBand_le_card_mul
    (baseLaw : ι → PMF ℕ) (broadBand : ι → Set ℕ)
    (hpos : ∀ i, ∃ x ∈ broadBand i, x ∈ (baseLaw i).support)
    (candidate : Finset ι) (narrowBand : ι → Set ℕ)
    (hnarrowMeas : ∀ i ∈ candidate, MeasurableSet (narrowBand i))
    {r : ℝ≥0∞}
    (hnarrow : ∀ i ∈ candidate,
      (filteredCoordinateLaw baseLaw broadBand hpos i).toMeasure
          (narrowBand i) ≤ r) :
    independentFilteredMeasure baseLaw broadBand hpos
        (anyCoordinateInBand candidate narrowBand) ≤
      (candidate.card : ℝ≥0∞) * r := by
  exact independent_anyCoordinateInBand_le_card_mul
    (filteredCoordinateLaw baseLaw broadBand hpos)
    candidate narrowBand hnarrowMeas hnarrow

/-- The one-coordinate polynomial ratio in HLOZ (4.55)--(4.57). -/
noncomputable def polynomialBandRatio
    (C κ₁ α : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (C * (m : ℝ) ^ (α - κ₁))

/-- Equations (4.55)--(4.58): if there are at most `(log m)^2`
candidates and each independently filtered coordinate has narrow-band
probability at most `C m^(α-κ₁)`, then their union has probability at most
`(log m)^2 C m^(α-κ₁)`.  The source use of this lemma is in the
range `0 < α < κ₁`, so this is the decaying factor
`m^(-(κ₁-α))`. -/
theorem independentFiltered_anyCoordinateInBand_le_log_sq_mul_power
    (baseLaw : ι → PMF ℕ) (broadBand : ι → Set ℕ)
    (hpos : ∀ i, ∃ x ∈ broadBand i, x ∈ (baseLaw i).support)
    (candidate : Finset ι) (narrowBand : ι → Set ℕ)
    (hnarrowMeas : ∀ i ∈ candidate, MeasurableSet (narrowBand i))
    (m : ℕ) {C κ₁ α : ℝ} (hC : 0 ≤ C) (hα : 0 < α) (hακ : α < κ₁)
    (hcandidate : (candidate.card : ℝ) ≤ Real.log (m : ℝ) ^ 2)
    (hnarrow : ∀ i ∈ candidate,
      (filteredCoordinateLaw baseLaw broadBand hpos i).toMeasure
          (narrowBand i) ≤ polynomialBandRatio C κ₁ α m) :
    independentFilteredMeasure baseLaw broadBand hpos
        (anyCoordinateInBand candidate narrowBand) ≤
      ENNReal.ofReal
        (Real.log (m : ℝ) ^ 2 * (C * (m : ℝ) ^ (α - κ₁))) := by
  have _hsourceRange : 0 < α ∧ α < κ₁ := ⟨hα, hακ⟩
  have hfinite := independentFiltered_anyCoordinateInBand_le_card_mul
    baseLaw broadBand hpos candidate narrowBand hnarrowMeas hnarrow
  calc
    independentFilteredMeasure baseLaw broadBand hpos
        (anyCoordinateInBand candidate narrowBand) ≤
        (candidate.card : ℝ≥0∞) * polynomialBandRatio C κ₁ α m := hfinite
    _ ≤ ENNReal.ofReal (Real.log (m : ℝ) ^ 2) *
          polynomialBandRatio C κ₁ α m := by
      have hcardENN : (candidate.card : ℝ≥0∞) ≤
          ENNReal.ofReal (Real.log (m : ℝ) ^ 2) := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hcandidate
      simpa only [mul_comm] using
        mul_le_mul_right hcardENN (polynomialBandRatio C κ₁ α m)
    _ = ENNReal.ofReal
        (Real.log (m : ℝ) ^ 2 * (C * (m : ℝ) ^ (α - κ₁))) := by
      have hratio : 0 ≤ C * (m : ℝ) ^ (α - κ₁) :=
        mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
      rw [mul_comm, polynomialBandRatio, ← ENNReal.ofReal_mul hratio]
      congr 1
      ring

/-- Direct PMF form of the Proposition 4.9 finite step.  The hypothesis
`hprod` is the pre-conditioning product identity, and the conclusion concerns
the joint law after every coordinate is filtered to its broad band. -/
theorem filter_blockEvent_anyCoordinateInBand_le_log_sq_mul_power
    (jointLaw : PMF (ι → ℕ)) (coordinateLaw : ι → PMF ℕ)
    (hprod : ∀ x, jointLaw x = ∏ i, coordinateLaw i (x i))
    (broadBand : ∀ _i, Finset ℕ)
    (hpos : ∀ i, ∃ x ∈ (broadBand i : Set ℕ),
      x ∈ (coordinateLaw i).support)
    (candidate : Finset ι) (narrowBand : ι → Set ℕ)
    (hnarrowMeas : ∀ i ∈ candidate, MeasurableSet (narrowBand i))
    (m : ℕ) {C κ₁ α : ℝ} (hC : 0 ≤ C) (hα : 0 < α) (hακ : α < κ₁)
    (hcandidate : (candidate.card : ℝ) ≤ Real.log (m : ℝ) ^ 2)
    (hnarrow : ∀ i ∈ candidate,
      (filteredCoordinateLaw coordinateLaw
        (fun j ↦ (broadBand j : Set ℕ)) hpos i).toMeasure
          (narrowBand i) ≤ polynomialBandRatio C κ₁ α m) :
    (jointLaw.filter
      (HLOZConditionalProduct.blockEvent broadBand)
      (HLOZConditionalProduct.blockEvent_meets_support
        jointLaw coordinateLaw hprod broadBand hpos)).toMeasure
        (anyCoordinateInBand candidate narrowBand) ≤
      ENNReal.ofReal
        (Real.log (m : ℝ) ^ 2 * (C * (m : ℝ) ^ (α - κ₁))) := by
  rw [filter_blockEvent_toMeasure_eq_independentFilteredMeasure
    jointLaw coordinateLaw hprod broadBand hpos]
  exact independentFiltered_anyCoordinateInBand_le_log_sq_mul_power
    coordinateLaw (fun j ↦ (broadBand j : Set ℕ)) hpos
    candidate narrowBand hnarrowMeas m hC hα hακ hcandidate hnarrow

/-- Transfer form for the conditional law produced by the source-specific
external-path decomposition and the conditional-product identity. -/
theorem conditional_anyCoordinateInBand_le_log_sq_mul_power
    (conditionalLaw : Measure (ι → ℕ))
    (baseLaw : ι → PMF ℕ) (broadBand : ι → Set ℕ)
    (hpos : ∀ i, ∃ x ∈ broadBand i, x ∈ (baseLaw i).support)
    (hlaw : conditionalLaw = independentFilteredMeasure baseLaw broadBand hpos)
    (candidate : Finset ι) (narrowBand : ι → Set ℕ)
    (hnarrowMeas : ∀ i ∈ candidate, MeasurableSet (narrowBand i))
    (m : ℕ) {C κ₁ α : ℝ} (hC : 0 ≤ C) (hα : 0 < α) (hακ : α < κ₁)
    (hcandidate : (candidate.card : ℝ) ≤ Real.log (m : ℝ) ^ 2)
    (hnarrow : ∀ i ∈ candidate,
      (filteredCoordinateLaw baseLaw broadBand hpos i).toMeasure
          (narrowBand i) ≤ polynomialBandRatio C κ₁ α m) :
    conditionalLaw (anyCoordinateInBand candidate narrowBand) ≤
      ENNReal.ofReal
        (Real.log (m : ℝ) ^ 2 * (C * (m : ℝ) ^ (α - κ₁))) := by
  rw [hlaw]
  exact independentFiltered_anyCoordinateInBand_le_log_sq_mul_power
    baseLaw broadBand hpos candidate narrowBand hnarrowMeas m hC
    hα hακ hcandidate hnarrow

end Erdos1166.HLOZFiniteUnion
