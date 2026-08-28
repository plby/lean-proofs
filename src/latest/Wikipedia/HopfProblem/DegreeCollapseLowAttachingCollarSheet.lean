import Wikipedia.HopfProblem.DegreeCollapseLowAttachingCollarCoordinates

/-!

# The actual smooth embedded sheet across a low-dimensional attaching rim

The whole original open attaching tube times height is parametrized using
the actual tube partial diffeomorphism and original cylinder embedding.
Its native derivative is injective, and the original normal columns span
the actual full normal space throughout this same sheet.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def collarSheet (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  (LowHeightCylinder.heightCylinder d e) (A.tubeHeightCoordinates p)

theorem collarSheet_apply (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :
    A.collarSheet p = (LowHeightCylinder.heightCylinder d e) (A.tube p.1, p.2) := rfl

theorem isEmbedding_collarSheet :
    IsEmbedding (fun p : A.tubeHeightCoordinates.source ↦ A.collarSheet p.val) :=
  (LowHeightCylinder.isEmbedding_heightCylinder d e).comp
    A.tubeHeightCoordinates.toOpenPartialHomeomorph.isEmbedding_restrict

theorem injOn_collarSheet : InjOn A.collarSheet A.tubeHeightCoordinates.source := by
  intro p hp q hq he
  have hpq : (⟨p, hp⟩ : A.tubeHeightCoordinates.source) = ⟨q, hq⟩ :=
    A.isEmbedding_collarSheet.injective he
  exact congrArg Subtype.val hpq

theorem contMDiffOn_collarSheet :
    ContMDiffOn (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ))
      (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      A.collarSheet A.tubeHeightCoordinates.source :=
  (LowHeightCylinder.contMDiff_heightCylinder d e).comp_contMDiffOn
    A.tubeHeightCoordinates.contMDiffOn

def collarSheetDerivative (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :
    ((Vector d × Vector (7 - d)) × ℝ) →L[ℝ] Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  mfderiv (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ))
    (𝓡 (e.ambientDimension + (1 + (1 + (d + 1))))) A.collarSheet p

theorem range_collarSheetDerivative {p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ}
    (hp : p ∈ A.tubeHeightCoordinates.source) :
    (A.collarSheetDerivative p).range =
      ((LowHeightCylinder.heightCylinderDerivative d e) (A.tubeHeightCoordinates p)).range := by
  let D : ((Vector d × Vector (7 - d)) × ℝ) →L[ℝ] (Vector 7 × ℝ) :=
    mfderiv (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ)) ((𝓡 7).prod 𝓘(ℝ, ℝ))
      A.tubeHeightCoordinates p
  have hl : IsLocalDiffeomorphAt (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ))
      ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞ A.tubeHeightCoordinates p :=
    ⟨A.tubeHeightCoordinates, hp, Set.eqOn_refl _ _⟩
  have hD : Bijective D :=
    (hl.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hc : A.collarSheetDerivative p =
      ((LowHeightCylinder.heightCylinderDerivative d e) (A.tubeHeightCoordinates p)).comp D :=
    mfderiv_comp p ((LowHeightCylinder.contMDiff_heightCylinder d e).mdifferentiableAt (by simp))
      (A.tubeHeightCoordinates.mdifferentiableAt (by simp) hp)
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨D v, by rw [hc]; rfl⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨w, hw⟩ := hD.2 v
    refine ⟨w, ?_⟩
    rw [hc]
    exact congrArg ((LowHeightCylinder.heightCylinderDerivative d e) (A.tubeHeightCoordinates p)) hw

theorem injective_collarSheetDerivative {p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ}
    (hp : p ∈ A.tubeHeightCoordinates.source) : Injective (A.collarSheetDerivative p) := by
  let D : ((Vector d × Vector (7 - d)) × ℝ) →L[ℝ] (Vector 7 × ℝ) :=
    mfderiv (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ)) ((𝓡 7).prod 𝓘(ℝ, ℝ))
      A.tubeHeightCoordinates p
  have hl : IsLocalDiffeomorphAt (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ))
      ((𝓡 7).prod 𝓘(ℝ, ℝ)) ∞ A.tubeHeightCoordinates p :=
    ⟨A.tubeHeightCoordinates, hp, Set.eqOn_refl _ _⟩
  have hD : Injective D :=
    (hl.mfderivToContinuousLinearEquiv (by simp)).injective
  have hc : A.collarSheetDerivative p =
      ((LowHeightCylinder.heightCylinderDerivative d e) (A.tubeHeightCoordinates p)).comp D :=
    mfderiv_comp p ((LowHeightCylinder.contMDiff_heightCylinder d e).mdifferentiableAt (by simp))
      (A.tubeHeightCoordinates.mdifferentiableAt (by simp) hp)
  rw [hc]
  exact ((LowHeightCylinder.injective_heightCylinderDerivative d e) _).comp hD

def collarSheetFrame (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :
    Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  boundaryFrameOperator d (a.orthonormal (A.tubeHeightCoordinates p).1).val

theorem contMDiffOn_collarSheetFrame :
    ContMDiffOn (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
        Vector (e.ambientDimension + (1 + (1 + (d + 1))))) ∞
      A.collarSheetFrame A.tubeHeightCoordinates.source :=
  (contMDiff_boundaryFrameOperator d a.contMDiff_orthonormal).comp_contMDiffOn
    (contMDiff_fst.comp_contMDiffOn A.tubeHeightCoordinates.contMDiffOn)

theorem collarSheetFrame_norm (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ)
    (v : Vector ((e.ambientDimension - 7) + (1 + (d + 1)))) : ‖A.collarSheetFrame p v‖ = ‖v‖ :=
  norm_boundaryFrameOperator d (a.orthonormal (A.tubeHeightCoordinates p).1) v

theorem collarSheetFrame_range {p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ}
    (hp : p ∈ A.tubeHeightCoordinates.source) :
    (A.collarSheetFrame p).range = (A.collarSheetDerivative p).rangeᗮ := by
  rw [A.range_collarSheetDerivative hp]
  exact (LowHeightCylinder.heightCylinder_frame_range d e) a (A.tubeHeightCoordinates p)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct
