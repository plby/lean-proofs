import Wikipedia.HopfProblem.DegreeCollapseCubicFieldAutomorphisms
import Wikipedia.SmoothSixDPoincare.PartialChartVectorField

/-!
# Absorbing a model-field automorphism into the original native chart

Changing an actual native coordinate chart by a continuous linear
automorphism commuting with its model field leaves the pulled-back native
field unchanged. This is proved from the actual manifold derivative and
pullback composition, including the original tangent-space identifications.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- The ordinary field automorphism is also an automorphism of the native
model tangent field, with its actual tangent-space identifications. -/
theorem mpullback_model_linear_automorphism (T : D ≃L[ℝ] D) (W : D → D)
    (hcomm : ∀ z, T (W z) = W (T z)) :
    VectorField.mpullback 𝓘(ℝ, D) 𝓘(ℝ, D) T
      (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) =
      (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) := by
  funext y
  rw [VectorField.mpullback_apply, mfderiv_eq_fderiv, T.fderiv]
  change T.toContinuousLinearMap.inverse (W (T y)) = W y
  rw [ContinuousLinearMap.inverse_equiv]
  change T.symm (W (T y)) = W y
  rw [← hcomm, T.symm_apply_apply]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Composition with a model-field automorphism retains the original
native pullback field at every point of the original chart source. -/
theorem partialChartField_linear_change
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, D) M D ∞)
    (T : D ≃L[ℝ] D) (W : D → D) (hcomm : ∀ z, T (W z) = W (T z))
    {x : M} (hx : x ∈ e.source) :
    FlowConstruction.partialChartField (e.trans T.toDiffeomorph.toPartialDiffeomorph) W x =
      FlowConstruction.partialChartField e W x := by
  have hT : (mfderivWithin 𝓘(ℝ, D) 𝓘(ℝ, D) T univ (e x)).IsInvertible := by
    rw [mfderivWithin_univ, mfderiv_eq_fderiv, T.fderiv]
    exact ⟨T, rfl⟩
  have hh := VectorField.mpullbackWithin_comp_of_left
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, D)) (I'' := 𝓘(ℝ, D))
    (f := (e : M → D)) (g := (T : D → D))
    (V := fun y => (NormedSpace.fromTangentSpace y).symm (W y))
    (s := univ) (t := univ)
    (e.mdifferentiableAt (by simp) hx).mdifferentiableWithinAt
    (mapsTo_univ _ _) (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hT
  simp only [VectorField.mpullbackWithin_univ,
    mpullback_model_linear_automorphism T W hcomm] at hh
  exact hh

/-- In particular, the actual cubic field survives the arbitrary commuting
transverse change in a native endpoint chart. -/
theorem native_cubic_field_transverse_chart_change {m : ℕ} (σ : Fin m → ℝ)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, Model m) M (Model m) ∞)
    (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hcomm : ∀ z, T (fun i => σ i * z i) = fun i => σ i * T z i)
    (t : ℝ) {x : M} (hx : x ∈ e.source) :
    FlowConstruction.partialChartField
        (e.trans (transverseFieldChange T).toDiffeomorph.toPartialDiffeomorph)
        (cubicDescent σ t) x = FlowConstruction.partialChartField e (cubicDescent σ t) x :=
  partialChartField_linear_change e (transverseFieldChange T) (cubicDescent σ t)
    (transverseFieldChange_cubicDescent σ T hcomm t) hx

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
