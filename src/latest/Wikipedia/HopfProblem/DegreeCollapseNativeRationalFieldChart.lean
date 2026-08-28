import Wikipedia.HopfProblem.DegreeCollapseRationalFieldCoordinates

/-!
# Native cubic endpoint field charts from linear Morse field charts

Pullback composition transports the proved rational model conjugacy into
the original tangent bundle. The critical endpoint belongs to the actual
chart source. The original native field is unchanged on the whole target;
neither a cubic function identity nor a relation with critical values is
assumed.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {D F E M : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- A proved coordinate-field conjugacy composes with an actual native chart. -/
theorem partialChartField_of_model_conjugacy
    (P : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, F) D F ∞)
    (Q : PartialDiffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) F M ∞)
    (W : D → D) (U : F → F)
    (hpush : ∀ p ∈ P.source, fderiv ℝ P p (W p) = U (P p))
    {x : M} (hx : x ∈ (P.trans Q).target) :
    FlowConstruction.partialChartField (P.trans Q).symm W x =
      FlowConstruction.partialChartField Q.symm U x := by
  have hxQ : x ∈ Q.target := hx.1
  have hxP : Q.symm x ∈ P.target := hx.2
  have hdiff : P.symm.toOpenPartialHomeomorph.MDifferentiable 𝓘(ℝ, F) 𝓘(ℝ, D) :=
    ⟨P.symm.mdifferentiableOn (by simp), P.mdifferentiableOn (by simp)⟩
  have hinv : (mfderivWithin 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm univ (Q.symm x)).IsInvertible := by
    rw [mfderivWithin_univ]
    exact ⟨hdiff.mfderiv hxP, rfl⟩
  have hh := VectorField.mpullbackWithin_comp_of_left
    (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, F)) (I'' := 𝓘(ℝ, D))
    (f := (Q.symm : M → F)) (g := (P.symm : F → D))
    (V := fun y => (NormedSpace.fromTangentSpace y).symm (W y))
    (s := univ) (t := univ)
    (Q.symm.mdifferentiableAt (by simp) hxQ).mdifferentiableWithinAt
    (mapsTo_univ _ _) (uniqueMDiffWithinAt_univ 𝓘(ℝ, E)) hinv
  simp only [VectorField.mpullbackWithin_univ] at hh
  have hv : VectorField.mpullback 𝓘(ℝ, F) 𝓘(ℝ, D) P.symm
      (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) (Q.symm x) =
      (NormedSpace.fromTangentSpace (Q.symm x)).symm (U (Q.symm x)) := by
    change FlowConstruction.partialChartField P.symm W (Q.symm x) = _
    rw [FlowConstruction.partialChartField_eq_mfderiv_symm P.symm W hxP]
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ P (P.symm (Q.symm x)) (W (P.symm (Q.symm x))) = U (Q.symm x)
    have hp : P.symm (Q.symm x) ∈ P.source := P.map_target' hxP
    rw [hpush (P.symm (Q.symm x)) hp]
    exact congrArg U (P.right_inv' hxP)
  change VectorField.mpullback 𝓘(ℝ, E) 𝓘(ℝ, D) (P.symm ∘ Q.symm)
    (fun y => (NormedSpace.fromTangentSpace y).symm (W y)) x = _
  rw [hh, VectorField.mpullback_apply, hv]
  rfl

/-- The constructed chart includes the critical endpoint and represents the
original native linear-model field by the exact cubic field everywhere. -/
theorem exists_native_cubic_field_endpoint {m : ℕ} (σ : Fin m → ℝ)
    {a : ℝ} (ha : 0 < a) {e : ℝ} (he : e ^ 2 = 1)
    (Q : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞)
    (h0 : (0 : Model m) ∈ Q.source)
    (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (hmodel : ∀ x ∈ Q.target,
      V x = FlowConstruction.partialChartField Q.symm (endpointLinearField σ a e) x) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, Model m) 𝓘(ℝ, E) (Model m) M ∞,
      (e * a, (0 : Fin m → ℝ)) ∈ Φ.source ∧ Φ (e * a, 0) = Q 0 ∧
      Φ.target ⊆ Q.target ∧
      (∀ x ∈ Φ.target, V x = nativeCubicDescent σ Φ (-(a ^ 2)) x) ∧
      (Φ : Model m → M) = Q ∘ endpointFieldProduct a e := by
  obtain ⟨P, hp, hcenter, hP, hpush⟩ := exists_endpoint_field_product_chart σ ha he
  let Φ := P.trans Q
  have hsource : (e * a, (0 : Fin m → ℝ)) ∈ Φ.source := by
    change (e * a, (0 : Fin m → ℝ)) ∈ P.source ∧ P (e * a, 0) ∈ Q.source
    exact ⟨hp, hcenter.symm ▸ h0⟩
  refine ⟨Φ, hsource, ?_, fun _ hx => hx.1, ?_, ?_⟩
  · change Q (P (e * a, 0)) = Q 0
    rw [hcenter]
  · intro x hx
    rw [hmodel x hx.1]
    exact (partialChartField_of_model_conjugacy P Q (cubicDescent σ (-(a ^ 2)))
      (endpointLinearField σ a e) hpush hx).symm
  · change Q ∘ P = Q ∘ endpointFieldProduct a e
    rw [hP]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
