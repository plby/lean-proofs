import Wikipedia.NoExoticSixSphere.UnitSurgeryOverlapMaps

/-! # Injectivity of the individual canonical surgery coordinate maps -/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery

open GLOrthonormalization Stiefel RoundedHandleCorner RoundedTrace
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

omit [T2Space M] [CompactSpace M] in
theorem tube_coordinates_eq {s t : Sphere 3} {v w : Vector 3}
    (hv : v ∈ closedBall (0 : Vector 3) A.radius)
    (hw : w ∈ closedBall (0 : Vector 3) A.radius) (he : A.tube (s, v) = A.tube (t, w)) :
    s = t ∧ v = w := by
  have hp : (s, (⟨v, hv⟩ : closedBall (0 : Vector 3) A.radius)) = (t, ⟨w, hw⟩) :=
    A.tube_embedded.injective he
  exact ⟨congrArg Prod.fst hp,
    congrArg (fun p : Sphere 3 × closedBall (0 : Vector 3) A.radius ↦ p.2.val) hp⟩

omit [T2Space M] in
theorem collarOriginalVector_norm_sq (p : boundaryCollarParameters A) :
    ‖collarOriginalVector A p‖ ^ 2 = 1 + p.val.2.2 := by
  rw [norm_collarOriginalVector, Real.sq_sqrt (by linarith [collar_parameter_gt_neg_one A p])]

omit [T2Space M] in
theorem normalize_collarOriginalVector (p : boundaryCollarParameters A) :
    NormedSpace.normalize (collarOriginalVector A p) = p.val.2.1.val := by
  rw [collarOriginalVector, NormedSpace.normalize_smul_of_pos
    (Real.sqrt_pos.mpr (by linarith [collar_parameter_gt_neg_one A p]))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm p.val.2.1)

theorem injective_exteriorPoint : Injective (exteriorPoint A hR) := by
  intro p q he
  have ht := congrArg (Subtype.val : OldPatch A hR → M) he
  exact Subtype.ext ht

omit [T2Space M] in
theorem injective_handlePoint : Injective (handlePoint A) := by
  intro p q he
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : FramedSurgery.NewPatch (Vector 4) (Vector 3) ↦ z.1.val) he)
    (congrArg (Prod.snd : FramedSurgery.NewPatch (Vector 4) (Vector 3) → Sphere 2) he)

theorem injective_collarPoint : Injective (collarPoint A hR) := by
  intro p q he
  have ht := tube_coordinates_eq A (collarOriginalVector_mem A hR p)
    (collarOriginalVector_mem A hR q) (congrArg Subtype.val he)
  have hu : p.val.2.2 = q.val.2.2 := by
    have hs := congrArg (fun v : Vector 3 ↦ ‖v‖ ^ 2) ht.2
    rw [collarOriginalVector_norm_sq, collarOriginalVector_norm_sq] at hs
    linarith
  have hw : p.val.2.1 = q.val.2.1 := by
    apply Subtype.ext
    have hs := congrArg NormedSpace.normalize ht.2
    rw [normalize_collarOriginalVector, normalize_collarOriginalVector] at hs
    exact hs
  exact Subtype.ext (Prod.ext ht.1 (Prod.ext hw hu))

theorem injective_exteriorMap : Injective (exteriorMap A hR) :=
  (FramedSurgery.oldMap_isOpenEmbedding (E := Vector 4) (face A hR) 2).injective.comp
    (injective_exteriorPoint A hR)

theorem injective_handleMap : Injective (handleMap A hR) :=
  (FramedSurgery.newMap_isOpenEmbedding (E := Vector 4) (face A hR) 2).injective.comp
    (injective_handlePoint A)

theorem injective_collarMap : Injective (collarMap A hR) :=
  (FramedSurgery.oldMap_isOpenEmbedding (E := Vector 4) (face A hR) 2).injective.comp
    (injective_collarPoint A hR)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.UnitSurgery
