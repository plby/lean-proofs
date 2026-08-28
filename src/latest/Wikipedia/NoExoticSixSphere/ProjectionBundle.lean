import Wikipedia.NoExoticSixSphere.ProjectionTransport
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Vector bundles from smooth families of projections

The actual ranges of a smooth constant-rank projection family form a smooth
vector bundle. A model-space equivalence is chosen separately at each chart
center; no smoothness or compatibility of these choices is assumed. Smooth
transition maps are instead supplied by the explicit ambient transport.
-/

open scoped Manifold ContDiff Topology Bundle
open Function Set Bundle

namespace NoExoticSixSphere.ProjectionBundle

variable {F K : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  (P : M → F →L[ℝ] F) (hP : ∀ x, IsIdempotentElem (P x))
  (q : ∀ x, (P x).range ≃L[ℝ] K)

/-- Local fiber coordinates, extended by total linear maps outside the chart. -/
noncomputable def toCoordinates (x₀ x : M) : (P x).range →L[ℝ] K :=
  (q x₀).toContinuousLinearMap.comp ((P x₀).rangeRestrict.comp
    ((projectionIntertwiner (P x₀) (P x)).inverse.comp (P x).range.subtypeL))

/-- The inverse fiber-coordinate map, also defined away from the chart. -/
noncomputable def fromCoordinates (x₀ x : M) : K →L[ℝ] (P x).range :=
  (P x).rangeRestrict.comp ((projectionIntertwiner (P x₀) (P x)).comp
    ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap))

/-- Within its domain, the coordinate map is a continuous linear equivalence. -/
noncomputable def coordinateEquiv (x₀ x : M)
    (hx : x ∈ projectionTransportDomain P x₀) : (P x).range ≃L[ℝ] K :=
  (projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx).symm.trans (q x₀)

omit [CompleteSpace F] [TopologicalSpace M] in
/-- The total coordinate formula agrees with the local equivalence. -/
theorem toCoordinates_eq (x₀ x : M) (hx : x ∈ projectionTransportDomain P x₀) :
    toCoordinates P q x₀ x = (coordinateEquiv P hP q x₀ x hx).toContinuousLinearMap := by
  ext v
  change q x₀ ((P x₀).rangeRestrict ((projectionIntertwiner (P x₀) (P x)).inverse v)) =
    q x₀ ((projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx).symm v)
  congr 1
  apply Subtype.ext
  change P x₀ ((projectionIntertwiner (P x₀) (P x)).inverse v) = _
  rw [← projectionRangeEquiv_symm_apply (P x₀) (P x) (hP x₀) (hP x) hx v]
  exact projection_apply_range (P x₀) (hP x₀) _

omit [CompleteSpace F] [TopologicalSpace M] in
/-- The total inverse formula agrees with the inverse local equivalence. -/
theorem fromCoordinates_eq (x₀ x : M) (hx : x ∈ projectionTransportDomain P x₀) :
    fromCoordinates P q x₀ x =
      (coordinateEquiv P hP q x₀ x hx).symm.toContinuousLinearMap := by
  ext v
  change P x (projectionIntertwiner (P x₀) (P x) ((q x₀).symm v)) =
    (projectionRangeEquiv (P x₀) (P x) (hP x₀) (hP x) hx ((q x₀).symm v) : F)
  rw [← projectionRangeEquiv_apply (P x₀) (P x) (hP x₀) (hP x) hx ((q x₀).symm v)]
  exact projection_apply_range (P x) (hP x) _

include hP in
omit [CompleteSpace F] [TopologicalSpace M] in
/-- Applying coordinates and then their inverse recovers the fiber vector. -/
theorem fromCoordinates_toCoordinates (x₀ x : M)
    (hx : x ∈ projectionTransportDomain P x₀) (v : (P x).range) :
    fromCoordinates P q x₀ x (toCoordinates P q x₀ x v) = v := by
  rw [toCoordinates_eq P hP q x₀ x hx, fromCoordinates_eq P hP q x₀ x hx]
  exact (coordinateEquiv P hP q x₀ x hx).symm_apply_apply v

include hP in
omit [CompleteSpace F] [TopologicalSpace M] in
/-- Applying inverse coordinates and then coordinates recovers the model vector. -/
theorem toCoordinates_fromCoordinates (x₀ x : M)
    (hx : x ∈ projectionTransportDomain P x₀) (v : K) :
    toCoordinates P q x₀ x (fromCoordinates P q x₀ x v) = v := by
  rw [toCoordinates_eq P hP q x₀ x hx, fromCoordinates_eq P hP q x₀ x hx]
  exact (coordinateEquiv P hP q x₀ x hx).apply_symm_apply v

variable (hs : ContMDiff I 𝓘(ℝ, F →L[ℝ] F) ∞ P)

/-- Inverse coordinates viewed as an ambient-vector-valued operator. -/
noncomputable def ambientFromCoordinates (x₀ x : M) : K →L[ℝ] F :=
  (P x).comp ((projectionIntertwiner (P x₀) (P x)).comp
    ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap))

/-- Coordinates applied to an arbitrary ambient vector. -/
noncomputable def ambientToCoordinates (x₀ x : M) : F →L[ℝ] K :=
  (q x₀).toContinuousLinearMap.comp ((P x₀).rangeRestrict.comp
    (projectionIntertwiner (P x₀) (P x)).inverse)

omit [CompleteSpace F] [TopologicalSpace M] in
/-- Forgetting range membership in inverse coordinates gives the ambient formula. -/
theorem coe_fromCoordinates (x₀ x : M) (v : K) :
    (fromCoordinates P q x₀ x v : F) = ambientFromCoordinates P q x₀ x v := rfl

omit [CompleteSpace F] [TopologicalSpace M] in
/-- Local coordinates are the ambient coordinate formula restricted to the fiber. -/
theorem toCoordinates_apply (x₀ x : M) (v : (P x).range) :
    toCoordinates P q x₀ x v = ambientToCoordinates P q x₀ x v := rfl

include hs in
omit [CompleteSpace F] in
/-- The inverse coordinate formula is globally smooth as an ambient operator. -/
theorem contMDiff_ambientFromCoordinates (x₀ : M) :
    ContMDiff I 𝓘(ℝ, K →L[ℝ] F) ∞ (ambientFromCoordinates P q x₀) :=
  hs.clm_comp ((contMDiff_projectionIntertwiner P hs x₀).clm_comp contMDiff_const)

include hs in
/-- The ambient coordinate formula is smooth throughout its chart domain. -/
theorem contMDiffOn_ambientToCoordinates (x₀ : M) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] K) ∞ (ambientToCoordinates P q x₀)
      (projectionTransportDomain P x₀) :=
  contMDiffOn_const.clm_comp (contMDiffOn_const.clm_comp
    (contMDiffOn_projectionIntertwiner_inverse P hs x₀))

/-- A local trivialization of the actual range fibers, before defining total-space topology. -/
noncomputable def pretrivialization (x₀ : M) :
    Pretrivialization K (π K (fun x ↦ (P x).range)) where
  toFun p := ⟨p.1, toCoordinates P q x₀ p.1 p.2⟩
  invFun p := ⟨p.1, fromCoordinates P q x₀ p.1 p.2⟩
  source := TotalSpace.proj ⁻¹' projectionTransportDomain P x₀
  target := projectionTransportDomain P x₀ ×ˢ univ
  map_source' := fun _ h ↦ ⟨h, mem_univ _⟩
  map_target' := fun _ h ↦ h.1
  left_inv' := by
    rintro ⟨x, v⟩ hx
    simp only [TotalSpace.mk_inj]
    exact fromCoordinates_toCoordinates P hP q x₀ x hx v
  right_inv' := by
    rintro ⟨x, v⟩ ⟨hx, _⟩
    simp only [Prod.mk_right_inj]
    exact toCoordinates_fromCoordinates P hP q x₀ x hx v
  open_target := (isOpen_projectionTransportDomain P hs x₀).prod isOpen_univ
  baseSet := projectionTransportDomain P x₀
  open_baseSet := isOpen_projectionTransportDomain P hs x₀
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/-- The local range trivializations are fiberwise linear. -/
instance pretrivialization_isLinear (x₀ : M) :
    (pretrivialization P hP q hs x₀).IsLinear ℝ where
  linear x _ := (toCoordinates P q x₀ x).toLinearMap.isLinear

/-- The inverse local trivialization is the explicit inverse coordinate map. -/
theorem pretrivialization_symm_apply (x₀ x : M)
    (hx : x ∈ projectionTransportDomain P x₀) (v : K) :
    (pretrivialization P hP q hs x₀).symm x v = fromCoordinates P q x₀ x v := by
  rw [Pretrivialization.symm_apply]
  · rfl
  · exact hx

/-- Coordinate transition, expressed solely by fixed maps and ambient operators. -/
noncomputable def coordinateChange (x₀ x₁ x : M) : K →L[ℝ] K :=
  (q x₁).toContinuousLinearMap.comp ((P x₁).rangeRestrict.comp
    ((projectionIntertwiner (P x₁) (P x)).inverse.comp ((P x).comp
      ((projectionIntertwiner (P x₀) (P x)).comp
        ((P x₀).range.subtypeL.comp (q x₀).symm.toContinuousLinearMap)))))

omit [CompleteSpace F] [TopologicalSpace M] in
/-- The ambient transition formula is exactly the change of local fiber coordinates. -/
theorem coordinateChange_eq (x₀ x₁ x : M) :
    coordinateChange P q x₀ x₁ x =
      (toCoordinates P q x₁ x).comp (fromCoordinates P q x₀ x) := by
  ext v
  rfl

include hs in
/-- Range-bundle transition functions are smooth on the overlap. -/
theorem contMDiffOn_coordinateChange (x₀ x₁ : M) :
    ContMDiffOn I 𝓘(ℝ, K →L[ℝ] K) ∞ (coordinateChange P q x₀ x₁)
      (projectionTransportDomain P x₀ ∩ projectionTransportDomain P x₁) := by
  have hi := (contMDiffOn_projectionIntertwiner_inverse P hs x₁).mono
    (inter_subset_right (s := projectionTransportDomain P x₀))
  exact contMDiffOn_const.clm_comp (contMDiffOn_const.clm_comp
    (hi.clm_comp (hs.contMDiffOn.clm_comp
      ((contMDiff_projectionIntertwiner P hs x₀).contMDiffOn.clm_comp contMDiffOn_const))))

/-- The transition formula agrees with the pretrivializations on their overlap. -/
theorem coordinateChange_apply (x₀ x₁ x : M)
    (hx : x ∈ projectionTransportDomain P x₀ ∩ projectionTransportDomain P x₁) (v : K) :
    coordinateChange P q x₀ x₁ x v =
      ((pretrivialization P hP q hs x₁)
        ⟨x, (pretrivialization P hP q hs x₀).symm x v⟩).2 := by
  rw [pretrivialization_symm_apply P hP q hs x₀ x hx.1]
  rfl

/-- The compatible linear charts give a vector prebundle on the actual projection ranges. -/
noncomputable def vectorPrebundle : VectorPrebundle ℝ K (fun x ↦ (P x).range) where
  pretrivializationAtlas := Set.range (pretrivialization P hP q hs)
  pretrivialization_linear' := by
    rintro _ ⟨x₀, rfl⟩
    infer_instance
  pretrivializationAt := pretrivialization P hP q hs
  mem_base_pretrivializationAt := mem_projectionTransportDomain P hP
  pretrivialization_mem_atlas x := ⟨x, rfl⟩
  exists_coordChange := by
    rintro _ ⟨x₀, rfl⟩ _ ⟨x₁, rfl⟩
    exact ⟨coordinateChange P q x₀ x₁,
      (contMDiffOn_coordinateChange P q hs x₀ x₁).continuousOn,
      coordinateChange_apply P hP q hs x₀ x₁⟩
  totalSpaceMk_isInducing := by
    intro x
    change Topology.IsInducing (fun v : (P x).range ↦ (x, toCoordinates P q x x v))
    have hx := mem_projectionTransportDomain P hP x
    rw [toCoordinates_eq P hP q x x hx]
    exact Topology.isInducing_const_prod.mpr
      (coordinateEquiv P hP q x x hx).toHomeomorph.isInducing

/-- The range prebundle has smooth transition maps. -/
instance vectorPrebundle_isContMDiff :
    (vectorPrebundle P hP q hs).IsContMDiff I ∞ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨x₀, rfl⟩ _ ⟨x₁, rfl⟩
    exact ⟨coordinateChange P q x₀ x₁,
      contMDiffOn_coordinateChange P q hs x₀ x₁,
      coordinateChange_apply P hP q hs x₀ x₁⟩

end NoExoticSixSphere.ProjectionBundle
