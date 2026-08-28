import Wikipedia.NoExoticSixSphere.CorankOneCoordinateCover
import Wikipedia.NoExoticSixSphere.CorankOneGeneric

/-!
# One perturbation parameter for countably many operator coordinate charts

The coordinate change is an actual continuous linear equivalence on the
operator space. Its pushforward of Haar measure is Haar measure, so the null
exceptional set in each chart pulls back to a null set in the original
parameter space. Countable intersection then controls every chosen chart.
-/

noncomputable section

open Set Function Module
open MeasureTheory MeasureTheory.Measure
open scoped ContDiff

namespace NoExoticSixSphere.CorankOneCoordinates

open CorankOne

variable {X V W E F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace (V →L[ℝ] W)] [BorelSpace (V →L[ℝ] W)]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem ae_regular_coordinates (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (c : Coordinates V W E F) (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D) :
    ∀ᵐ A ∂μ, ∀ x, D x + A ∈ domain c → residual (operatorEquiv c (D x + A)) = 0 →
      Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y + A))) x) := by
  let : MeasurableSpace (BlockMap E F) := borel (BlockMap E F)
  let : BorelSpace (BlockMap E F) := ⟨rfl⟩
  let Q : (V →L[ℝ] W) ≃L[ℝ] BlockMap E F := operatorEquiv c
  let : IsAddHaarMeasure (μ.map Q) := Q.isAddHaarMeasure_map μ
  have h := ae_regular_translations (μ.map Q) (fun x ↦ Q (D x)) (Q.contDiff.comp hD)
  have hp := ae_of_ae_map Q.continuous.measurable.aemeasurable h
  change ∀ᵐ A ∂μ, ∀ x, Q (D x + A) ∈ chart → residual (Q (D x + A)) = 0 →
    Surjective (fderiv ℝ (fun y ↦ residual (Q (D y + A))) x)
  simpa only [map_add] using hp

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
theorem ae_regular_countable_coordinates (μ : Measure (V →L[ℝ] W)) [IsAddHaarMeasure μ]
    (C : Set (Coordinates V W E F)) (hC : C.Countable)
    (D : X → V →L[ℝ] W) (hD : ContDiff ℝ ∞ D) :
    ∀ᵐ A ∂μ, ∀ c ∈ C, ∀ x, D x + A ∈ domain c →
      residual (operatorEquiv c (D x + A)) = 0 →
        Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c (D y + A))) x) := by
  let : Countable C := hC.to_subtype
  have h : ∀ᵐ A ∂μ, ∀ c : C, ∀ x, D x + A ∈ domain c.val →
      residual (operatorEquiv c.val (D x + A)) = 0 →
        Surjective (fderiv ℝ (fun y ↦ residual (operatorEquiv c.val (D y + A))) x) :=
    ae_all_iff.mpr fun c ↦ ae_regular_coordinates μ c.val D hD
  exact h.mono fun A hA c hc ↦ hA ⟨c, hc⟩

end NoExoticSixSphere.CorankOneCoordinates
