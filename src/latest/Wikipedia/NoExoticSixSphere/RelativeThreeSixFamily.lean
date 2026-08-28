import Wikipedia.NoExoticSixSphere.RelativeThreeSixJet

/-!
# One endpoint-preserving perturbation controls jets and double points

Both genericity requirements hold almost everywhere in the same finite-
dimensional operator parameter space. Their intersection contains arbitrarily
small parameters. The resulting actual smooth family agrees with the original
family at both endpoints and at every exterior time.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.RelativeDoublePointPerturbation

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

theorem ae_regular_double_points [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f)) :
    ∀ᵐ A ∂μ, ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → q.1 ∈ Ioo (0 : ℝ) 1 →
      difference f A q = 0 → Surjective (fderiv ℝ (difference f A) q) := by
  apply (ParametricRegular.ae_affine_regular_operators_on μ
    (DoublePointPerturbation.baseDifference f) direction
    (DoublePointPerturbation.contDiff_baseDifference f hf) contDiff_direction (domain V)
    (fun q hq ↦ smul_ne_zero (cutoff_pos hq.2).ne' (sub_ne_zero.mpr hq.1))).mono
  intro A hA q hq ht hz
  exact hA q ⟨hq, ht⟩ hz

theorem ae_generic_families [MeasurableSpace (V →L[ℝ] W)]
    [BorelSpace (V →L[ℝ] W)] (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) :
    ∀ᵐ A ∂μ,
      OperatorRank.RegularThreeSixOn (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2)
        {q | q.1 ∈ Ioo (0 : ℝ) 1} ∧
      ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → q.1 ∈ Ioo (0 : ℝ) 1 →
        difference f A q = 0 → Surjective (fderiv ℝ (difference f A) q) :=
  (ae_regular_jets μ f hf hv hw).and (ae_regular_double_points μ f hf)

theorem exists_small_generic_family (f : ℝ → V → W) (hf : ContDiff ℝ ∞ (uncurry f))
    (hv : finrank ℝ V = 3) (hw : finrank ℝ W = 6) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : V →L[ℝ] W, ‖A‖ < ε ∧ ContDiff ℝ ∞ (uncurry (perturb f A)) ∧
      (∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, perturb f A t x = f t x) ∧
      OperatorRank.RegularThreeSixOn (fun q : ℝ × V ↦ fderiv ℝ (perturb f A q.1) q.2)
        {q | q.1 ∈ Ioo (0 : ℝ) 1} ∧
      ∀ q : ℝ × (V × V), q.2.1 ≠ q.2.2 → q.1 ∈ Ioo (0 : ℝ) 1 →
        difference f A q = 0 → Surjective (fderiv ℝ (difference f A) q) := by
  let : MeasurableSpace (V →L[ℝ] W) := borel (V →L[ℝ] W)
  let : BorelSpace (V →L[ℝ] W) := ⟨rfl⟩
  have hdense := Measure.dense_of_ae (ae_generic_families addHaar f hf hv hw)
  obtain ⟨A, hA, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨A, by simpa only [dist_zero_left] using hsmall, contDiff_perturb f hf A,
    fun _ ht x ↦ perturb_eq_outside f A ht x, hA⟩

end NoExoticSixSphere.RelativeDoublePointPerturbation
