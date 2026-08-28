import Wikipedia.NoExoticSixSphere.SphereThreeFramedDerivative
import Wikipedia.NoExoticSixSphere.PartialFrameRangeCoordinates

/-!
# Genuine chart coordinates for the global quaternionic tangent frame

The ambient derivative of an inverse sphere chart spans exactly the original
tangent hyperplane. Extracting its quaternionic-frame coordinates gives a
linear equivalence. Both that map and its inverse vary continuously on the
whole original chart domain, not merely on a chosen linking sphere.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization

variable (c : PartialDiffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Vector 3) ∞)

def chartTangent (x : c.source) : Vector 3 →L[ℝ] Vector 4 :=
  fderiv ℝ (fun z ↦ (c.symm z).val) (c x.val)

def inverseChartDifferential (x : c.source) : Vector 3 ≃L[ℝ] Vector 3 :=
  (show IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c.symm (c x.val) from
    ⟨c.symm, c.map_source x.property, fun _ _ ↦ rfl⟩).mfderivToContinuousLinearEquiv (by simp)

theorem chartTangent_eq (x : c.source) :
    chartTangent c x = (inclusionDerivative x.val).comp
      (inverseChartDifferential c x).toContinuousLinearMap := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hc := c.contMDiffOn_invFun.contMDiffAt
    (c.open_target.mem_nhds (c.map_source x.property))
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  have h := mfderiv_comp (c x.val) (hi.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at h
  change chartTangent c x = (inclusionDerivative (c.symm (c x.val))).comp
    (inverseChartDifferential c x).toContinuousLinearMap at h
  have he : c.symm (c x.val) = x.val := c.left_inv x.property
  rw [he] at h
  exact h

theorem chartTangent_injective (x : c.source) : Injective (chartTangent c x) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : Injective (inclusionDerivative x.val) := by
    convert! injective_mvfderiv_subtypeVal_sphere x.val
  rw [chartTangent_eq]
  exact hi.comp (inverseChartDifferential c x).injective

theorem chartTangent_range (x : c.source) :
    (chartTangent c x).range = (operator x.val.val).range := by
  rw [chartTangent_eq]
  change ((inclusionDerivative x.val).toLinearMap.comp
    (inverseChartDifferential c x).toLinearMap).range = _
  rw [LinearMap.range_comp_of_range_eq_top _ (inverseChartDifferential c x).toLinearEquiv.range,
    range_inclusionDerivative, range_operator]

theorem continuous_chartTangent : Continuous (chartTangent c) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  have hc : ContDiffOn ℝ ∞ (fun z ↦ (c.symm z).val) c.target :=
    (hi.comp_contMDiffOn c.contMDiffOn_invFun).contDiffOn
  exact (hc.continuousOn_fderiv_of_isOpen c.open_target (by simp)).comp_continuous
    c.toOpenPartialHomeomorph.continuousOn.domRestrict (fun x ↦ c.map_source x.property)

def chartCoordinatesOperator (x : c.source) : Vector 3 →L[ℝ] Vector 3 :=
  (operator x.val.val).adjoint.comp (chartTangent c x)

theorem operator_comp_chartCoordinates (x : c.source) :
    (operator x.val.val).comp (chartCoordinatesOperator c x) = chartTangent c x := by
  apply ContinuousLinearMap.ext
  intro v
  apply Stiefel.RangeCoordinates.self_adjoint (frame x.val)
  change chartTangent c x v ∈ (operator x.val.val).range
  rw [← chartTangent_range c x]
  exact ⟨v, rfl⟩

theorem chartCoordinatesOperator_injective (x : c.source) :
    Injective (chartCoordinatesOperator c x) := by
  intro v w hvw
  apply chartTangent_injective c x
  have he := congrArg (operator x.val.val) hvw
  change ((operator x.val.val).comp (chartCoordinatesOperator c x)) v =
    ((operator x.val.val).comp (chartCoordinatesOperator c x)) w at he
  rwa [operator_comp_chartCoordinates] at he

def chartCoordinates (x : c.source) : Vector 3 ≃L[ℝ] Vector 3 := by
  let e := LinearEquiv.ofBijective (chartCoordinatesOperator c x).toLinearMap
    ⟨chartCoordinatesOperator_injective c x,
      LinearMap.surjective_of_injective (chartCoordinatesOperator_injective c x)⟩
  exact e.toContinuousLinearEquiv

theorem chartCoordinates_toContinuousLinearMap (x : c.source) :
    (chartCoordinates c x).toContinuousLinearMap = chartCoordinatesOperator c x := rfl

theorem chartCoordinates_symm_toContinuousLinearMap (x : c.source) :
    (chartCoordinates c x).symm.toContinuousLinearMap = (chartCoordinatesOperator c x).inverse :=
  (ContinuousLinearMap.inverse_equiv (chartCoordinates c x)).symm

theorem continuous_chartCoordinates :
    Continuous (fun x : c.source ↦ (chartCoordinates c x).toContinuousLinearMap) := by
  simp_rw [chartCoordinates_toContinuousLinearMap]
  have ht := contDiff_operator.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val : Continuous (fun x : c.source ↦ x.val.val))
  exact (ContinuousLinearMap.adjoint.continuous.comp ht).clm_comp (continuous_chartTangent c)

theorem continuous_inverse_chartCoordinates :
    Continuous (fun x : c.source ↦ (chartCoordinates c x).symm.toContinuousLinearMap) := by
  rw [continuous_iff_continuousAt]
  intro x
  simp_rw [chartCoordinates_symm_toContinuousLinearMap]
  have hi : (chartCoordinatesOperator c x).IsInvertible := ⟨chartCoordinates c x, rfl⟩
  exact (hi.contDiffAt_map_inverse (n := ∞)).continuousAt.comp
    (continuous_chartCoordinates c).continuousAt

theorem chartTangent_comp_inverse_coordinates (x : c.source) :
    (chartTangent c x).comp (chartCoordinates c x).symm.toContinuousLinearMap =
      operator x.val.val := by
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (chartCoordinates c x).surjective v
  change chartTangent c x ((chartCoordinates c x).symm (chartCoordinates c x w)) = _
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact (congrArg (fun L : Vector 3 →L[ℝ] Vector 4 ↦ L w)
    (operator_comp_chartCoordinates c x)).symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem extensionDerivative_comp_chartTangent (f : Sphere 3 → F)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, F) ∞ f) (x : c.source) :
    (fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3) f) x.val.val).comp
      (chartTangent c x) = fderiv ℝ (f ∘ c.symm) (c x.val) := by
  let : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hc := c.contMDiffOn_invFun.contMDiffAt
    (c.open_target.mem_nhds (c.map_source x.property))
  have hi : ContMDiff (𝓡 3) (𝓡 4) ∞ (fun s : Sphere 3 ↦ s.val) := contMDiff_coe_sphere
  have hJ : DifferentiableAt ℝ (fun z ↦ (c.symm z).val) (c x.val) :=
    (hi.contMDiffAt.comp _ hc).contDiffAt.differentiableAt (by simp)
  have he : SmoothSphereAmbient.extension (Stiefel.pole 3) f ∘ (fun z ↦ (c.symm z).val) =
      f ∘ c.symm := funext (fun z ↦ SmoothSphereAmbient.extension_coe (Stiefel.pole 3) f _)
  have h := fderiv_comp (c x.val)
    ((SmoothSphereAmbient.contDiff_extension (Stiefel.pole 3) f hf).differentiable (by simp) _) hJ
  have hx : c.symm (c x.val) = x.val := c.left_inv x.property
  rw [he, hx] at h
  exact h.symm

theorem framedDerivative_in_chart (f : Sphere 3 → F)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, F) ∞ f) (x : c.source) :
    framedDerivative f x.val = (fderiv ℝ (f ∘ c.symm) (c x.val)).comp
      (chartCoordinates c x).symm.toContinuousLinearMap := by
  change (fderiv ℝ (SmoothSphereAmbient.extension (Stiefel.pole 3) f) x.val.val).comp
    (operator x.val.val) = _
  rw [← chartTangent_comp_inverse_coordinates c x, ← ContinuousLinearMap.comp_assoc,
    extensionDerivative_comp_chartTangent c f hf x]

end NoExoticSixSphere.SphereThreeTangentFrame
