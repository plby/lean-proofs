import Wikipedia.NoExoticSixSphere.UnitSurgerySmoothMaps
import Wikipedia.NoExoticSixSphere.SphereRadialHeightCoordinates
import Wikipedia.NoExoticSixSphere.OpenCodomainLocalDiffeomorph

/-!
# Local smooth inverses for all three canonical surgery maps

The exterior and handle maps are open restrictions of the canonical patches.
The collar uses an actual radial partial diffeomorphism followed by the
original attaching-tube local diffeomorphism.
-/

noncomputable section

open Function Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

omit [CompactSpace M] in
theorem isLocalDiffeomorphAt_oldMap (p : OldPatch A hR) :
    letI := targetChartedSpace A hR;
    IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞
      (FramedSurgery.oldMap (E := Vector 4) (face A hR) 2) p := by
  let := targetChartedSpace A hR
  let D := boundaryData A hR
  exact ⟨D.oldPartial, by rw [D.old_source]; trivial, fun q _ ↦ (D.old_point q).symm⟩

omit [CompactSpace M] in
theorem isLocalDiffeomorphAt_newMap (p : FramedSurgery.NewPatch (Vector 4) (Vector 3)) :
    letI := targetChartedSpace A hR;
    IsLocalDiffeomorphAt ((𝓡 4).prod (𝓡 2)) (𝓡 6) ∞
      (FramedSurgery.newMap (E := Vector 4) (face A hR) 2) p := by
  let := targetChartedSpace A hR
  let D := boundaryData A hR
  exact ⟨D.newPartial, by rw [D.new_source]; trivial, fun q _ ↦ (D.new_point q).symm⟩

omit [IsManifold (𝓡 6) ∞ M] in
theorem isLocalDiffeomorphAt_exteriorPoint (p : retainedExterior A) :
    IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞ (exteriorPoint A hR) p :=
  isLocalDiffeomorphAt_codRestrict (OldPatch A hR)
    (fun q : retainedExterior A ↦ (exteriorPoint A hR q).property)
    (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 6) (retainedExterior A) p)

omit [IsManifold (𝓡 6) ∞ M] [T2Space M] in
theorem isLocalDiffeomorphAt_handlePoint (p : boundaryHandleParameters A) :
    IsLocalDiffeomorphAt ((𝓡 4).prod (𝓡 2)) ((𝓡 4).prod (𝓡 2)) ∞ (handlePoint A) p := by
  let U := FramedSurgery.openUnitDisk (Vector 4)
  let d := openSubsetPartialDiffeomorph (I := 𝓡 4) U ⟨(handlePoint A p).1⟩
  let Φ := partialDiffeomorphProd d.symm (Diffeomorph.refl (𝓡 2) (Sphere 2) ∞).toPartialDiffeomorph
  have hd : d.target = (U : Set (Vector 4)) :=
    Opens.openPartialHomeomorphSubtypeCoe_target U ⟨(handlePoint A p).1⟩
  have hp : p.val ∈ Φ.source := by
    change p.val.1 ∈ d.target ∧ True
    rw [hd]
    exact ⟨(handlePoint A p).1.property, trivial⟩
  have he : (fun q : boundaryHandleParameters A ↦ Φ q.val) = handlePoint A := by
    funext q
    apply Prod.ext
    · apply Subtype.ext
      change (d.symm q.val.1).val = q.val.1
      exact d.right_inv (by rw [hd]; exact (handlePoint A q).1.property)
    · rfl
  have hf := (isLocalDiffeomorphAt_openSubset_val (I := (𝓡 4).prod (𝓡 2))
    (boundaryHandleParameters A) p).comp ((𝓡 4).prod (𝓡 2))
      (FramedSurgery.NewPatch (Vector 4) (Vector 3)) ⟨Φ, hp, eqOn_refl _ _⟩
  change IsLocalDiffeomorphAt _ _ ∞ (fun q : boundaryHandleParameters A ↦ Φ q.val) p at hf
  rw [he] at hf
  exact hf

omit [IsManifold (𝓡 6) ∞ M] in
theorem isLocalDiffeomorphAt_collarPoint (p : boundaryCollarParameters A) :
    IsLocalDiffeomorphAt boundaryParameterModel (𝓡 6) ∞ (collarPoint A hR) p := by
  let Φ := partialDiffeomorphProd (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞).toPartialDiffeomorph
    (SphereRadialHeightCoordinates.chart (E := Vector 3) (n := 2) (pole 2))
  have hp : p.val ∈ Φ.source := ⟨trivial, collar_parameter_gt_neg_one A p⟩
  have hc : IsLocalDiffeomorphAt boundaryParameterModel ((𝓡 3).prod (𝓡 3)) ∞
      (fun q : boundaryCollarParameters A ↦ (q.val.1, collarOriginalVector A q)) p :=
    (isLocalDiffeomorphAt_openSubset_val (I := boundaryParameterModel)
      (boundaryCollarParameters A) p).comp ((𝓡 3).prod (𝓡 3))
        (Sphere 3 × Vector 3) ⟨Φ, hp, eqOn_refl _ _⟩
  have ht := hc.comp (𝓡 6) M
    (A.tube_localDiffeomorph p.val.1 _ (collarOriginalVector_mem A hR p))
  exact isLocalDiffeomorphAt_codRestrict (OldPatch A hR)
    (fun q : boundaryCollarParameters A ↦ (collarPoint A hR q).property) ht

theorem isLocalDiffeomorphAt_exteriorMap (p : retainedExterior A) :
    letI := targetChartedSpace A hR;
    IsLocalDiffeomorphAt (𝓡 6) (𝓡 6) ∞ (exteriorMap A hR) p := by
  let := targetChartedSpace A hR
  exact (isLocalDiffeomorphAt_exteriorPoint A hR p).comp (𝓡 6) (Target A hR)
    (isLocalDiffeomorphAt_oldMap A hR _)

theorem isLocalDiffeomorphAt_handleMap (p : boundaryHandleParameters A) :
    letI := targetChartedSpace A hR;
    IsLocalDiffeomorphAt ((𝓡 4).prod (𝓡 2)) (𝓡 6) ∞ (handleMap A hR) p := by
  let := targetChartedSpace A hR
  exact (isLocalDiffeomorphAt_handlePoint A p).comp (𝓡 6) (Target A hR)
    (isLocalDiffeomorphAt_newMap A hR _)

theorem isLocalDiffeomorphAt_collarMap (p : boundaryCollarParameters A) :
    letI := targetChartedSpace A hR;
    IsLocalDiffeomorphAt boundaryParameterModel (𝓡 6) ∞ (collarMap A hR) p := by
  let := targetChartedSpace A hR
  exact (isLocalDiffeomorphAt_collarPoint A hR p).comp (𝓡 6) (Target A hR)
    (isLocalDiffeomorphAt_oldMap A hR _)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
