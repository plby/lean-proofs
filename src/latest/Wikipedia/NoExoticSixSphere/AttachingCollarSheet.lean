import Wikipedia.NoExoticSixSphere.AttachingCollarCoordinates

/-!
# A genuine smooth embedded sheet across the attaching rim

The entire original open attaching tube times height is parametrized using
the constructed tube diffeomorphism and the actual cylinder embedding.
The native derivative is injective, and the prescribed original normal
columns span its actual normal space throughout this sheet.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def collarSheet (p : (Sphere 3 × Vector (n - 3)) × ℝ) : Vector (e.ambientDimension + 6) :=
  e.heightCylinder (A.tubeHeightCoordinates p)

theorem collarSheet_apply (p : (Sphere 3 × Vector (n - 3)) × ℝ) :
    A.collarSheet p = e.heightCylinder (A.tube p.1, p.2) := rfl

theorem isEmbedding_collarSheet :
    IsEmbedding (fun p : A.tubeHeightCoordinates.source ↦ A.collarSheet p.val) :=
  e.isEmbedding_heightCylinder.comp
    A.tubeHeightCoordinates.toOpenPartialHomeomorph.isEmbedding_restrict

theorem injOn_collarSheet : InjOn A.collarSheet A.tubeHeightCoordinates.source := by
  intro p hp q hq he
  have hpq : (⟨p, hp⟩ : A.tubeHeightCoordinates.source) = ⟨q, hq⟩ :=
    A.isEmbedding_collarSheet.injective he
  exact congrArg Subtype.val hpq

theorem contMDiffOn_collarSheet :
    ContMDiffOn (((𝓡 3).prod (𝓡 (n - 3))).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + 6)) ∞
      A.collarSheet A.tubeHeightCoordinates.source :=
  e.contMDiff_heightCylinder.comp_contMDiffOn A.tubeHeightCoordinates.contMDiffOn

def collarSheetDerivative (p : (Sphere 3 × Vector (n - 3)) × ℝ) :
    ((Vector 3 × Vector (n - 3)) × ℝ) →L[ℝ] Vector (e.ambientDimension + 6) :=
  mfderiv (((𝓡 3).prod (𝓡 (n - 3))).prod 𝓘(ℝ, ℝ)) (𝓡 (e.ambientDimension + 6)) A.collarSheet p

theorem range_collarSheetDerivative {p : (Sphere 3 × Vector (n - 3)) × ℝ}
    (hp : p ∈ A.tubeHeightCoordinates.source) :
    (A.collarSheetDerivative p).range =
      (e.heightCylinderDerivative (A.tubeHeightCoordinates p)).range := by
  let D : ((Vector 3 × Vector (n - 3)) × ℝ) →L[ℝ] (Vector n × ℝ) :=
    mfderiv (((𝓡 3).prod (𝓡 (n - 3))).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, ℝ))
      A.tubeHeightCoordinates p
  have hl : IsLocalDiffeomorphAt (((𝓡 3).prod (𝓡 (n - 3))).prod 𝓘(ℝ, ℝ))
      ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ A.tubeHeightCoordinates p :=
    ⟨A.tubeHeightCoordinates, hp, Set.eqOn_refl _ _⟩
  have hD : Bijective D :=
    (hl.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hc : A.collarSheetDerivative p =
      (e.heightCylinderDerivative (A.tubeHeightCoordinates p)).comp D :=
    mfderiv_comp p (e.contMDiff_heightCylinder.mdifferentiableAt (by simp))
      (A.tubeHeightCoordinates.mdifferentiableAt (by simp) hp)
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨D v, by rw [hc]; rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := hD.2 v
    refine ⟨w, ?_⟩
    rw [hc]
    exact congrArg (e.heightCylinderDerivative (A.tubeHeightCoordinates p)) hw

theorem injective_collarSheetDerivative {p : (Sphere 3 × Vector (n - 3)) × ℝ}
    (hp : p ∈ A.tubeHeightCoordinates.source) : Injective (A.collarSheetDerivative p) := by
  let D : ((Vector 3 × Vector (n - 3)) × ℝ) →L[ℝ] (Vector n × ℝ) :=
    mfderiv (((𝓡 3).prod (𝓡 (n - 3))).prod 𝓘(ℝ, ℝ)) ((𝓡 n).prod 𝓘(ℝ, ℝ))
      A.tubeHeightCoordinates p
  have hl : IsLocalDiffeomorphAt (((𝓡 3).prod (𝓡 (n - 3))).prod 𝓘(ℝ, ℝ))
      ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ A.tubeHeightCoordinates p :=
    ⟨A.tubeHeightCoordinates, hp, Set.eqOn_refl _ _⟩
  have hD : Injective D :=
    (hl.mfderivToContinuousLinearEquiv (by simp)).injective
  have hc : A.collarSheetDerivative p =
      (e.heightCylinderDerivative (A.tubeHeightCoordinates p)).comp D :=
    mfderiv_comp p (e.contMDiff_heightCylinder.mdifferentiableAt (by simp))
      (A.tubeHeightCoordinates.mdifferentiableAt (by simp) hp)
  rw [hc]
  exact (e.injective_heightCylinderDerivative _).comp hD

def collarSheetFrame (p : (Sphere 3 × Vector (n - 3)) × ℝ) :
    Vector ((e.ambientDimension - n) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  boundaryFrameOperator (a.orthonormal (A.tubeHeightCoordinates p).1).val

theorem contMDiffOn_collarSheetFrame :
    ContMDiffOn (((𝓡 3).prod (𝓡 (n - 3))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Vector ((e.ambientDimension - n) + 5) →L[ℝ] Vector (e.ambientDimension + 6)) ∞
      A.collarSheetFrame A.tubeHeightCoordinates.source :=
  (contMDiff_boundaryFrameOperator a.contMDiff_orthonormal).comp_contMDiffOn
    (contMDiff_fst.comp_contMDiffOn A.tubeHeightCoordinates.contMDiffOn)

theorem collarSheetFrame_norm (p : (Sphere 3 × Vector (n - 3)) × ℝ)
    (v : Vector ((e.ambientDimension - n) + 5)) : ‖A.collarSheetFrame p v‖ = ‖v‖ :=
  norm_boundaryFrameOperator (a.orthonormal (A.tubeHeightCoordinates p).1) v

theorem collarSheetFrame_range {p : (Sphere 3 × Vector (n - 3)) × ℝ}
    (hp : p ∈ A.tubeHeightCoordinates.source) :
    (A.collarSheetFrame p).range = (A.collarSheetDerivative p).rangeᗮ := by
  rw [A.range_collarSheetDerivative hp]
  exact e.heightCylinder_frame_range a (A.tubeHeightCoordinates p)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct
