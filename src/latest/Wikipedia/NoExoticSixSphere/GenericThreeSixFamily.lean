import Wikipedia.NoExoticSixSphere.GenericThreeSixJet

/-!
# One small perturbation controls both singular jets and double points

Both requirements hold almost everywhere in the same actual operator
parameter space. Their intersection therefore contains arbitrarily small
operators. The result does not choose unrelated perturbations for the
diagonal and off-diagonal problems.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.DoublePointPerturbation

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem ae_regular_double_points [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ∀ᵐ A ∂μ, ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → difference f A q = 0 →
      Surjective (fderiv ℝ (difference f A) q) :=
  ParametricRegular.ae_affine_regular_operators_on μ (baseDifference f) direction
    (contDiff_baseDifference f hf) contDiff_direction (distinctDomain V)
    (fun _ h ↦ sub_ne_zero.mpr h)

theorem ae_generic_families [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) :
    ∀ᵐ A ∂μ,
      OperatorRank.RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2) ∧
      ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → difference f A q = 0 →
        Surjective (fderiv ℝ (difference f A) q) :=
  (ae_regular_jets μ f hf hv hw).and (ae_regular_double_points μ f hf)

theorem exists_small_generic_family (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : V →L[ℝ] W, ‖A‖ < ε ∧
      OperatorRank.RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2) ∧
      ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → difference f A q = 0 →
        Surjective (fderiv ℝ (difference f A) q) := by
  let : MeasurableSpace (V →L[ℝ] W) := borel (V →L[ℝ] W)
  let : BorelSpace (V →L[ℝ] W) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae (ae_generic_families addHaar f hf hv hw)
  obtain ⟨A, hA, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨A, by simpa only [dist_zero_left] using hsmall, hA⟩

end NoExoticSixSphere.DoublePointPerturbation
