import Wikipedia.NoExoticSixSphere.RoundedTraceInnerImage

/-!
# Original-manifold cylinder coordinates on an actual open piece of the rounded set

Remove the compact inner handle image. The remaining relatively open subset
lies in the actual cylinder, so the inverse of the cylinder embedding supplies
continuous coordinates in the original manifold times the real line. These
coordinates are a genuine embedding and retain every ambient point exactly.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace

open GLOrthonormalization Stiefel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  {e : EuclideanEmbedding n M}
  {a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def cylinderPart : Opens (ambientSet A) :=
  ⟨{p | p.val ∉ innerImage A}, (isClosed_innerImage A).isOpen_compl.preimage
    continuous_subtype_val⟩

def cylinderLift : C(cylinderPart A, range e.heightCylinder) :=
  ⟨fun p ↦ ⟨p.val.val, outside_inner_in_cylinder A p.val.property p.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def cylinderCoordinates : C(cylinderPart A, M × ℝ) :=
  ⟨fun p ↦ e.isEmbedding_heightCylinder.toHomeomorph.symm (cylinderLift A p),
    e.isEmbedding_heightCylinder.toHomeomorph.symm.continuous.comp (cylinderLift A).continuous⟩

theorem cylinderCoordinates_ambient (p : cylinderPart A) :
    e.heightCylinder (cylinderCoordinates A p) = p.val.val :=
  congrArg Subtype.val
    (e.isEmbedding_heightCylinder.toHomeomorph.apply_symm_apply (cylinderLift A p))

theorem cylinderCoordinates_of_eq (p : cylinderPart A) (q : M × ℝ)
    (hq : p.val.val = e.heightCylinder q) : cylinderCoordinates A p = q :=
  e.injective_heightCylinder ((cylinderCoordinates_ambient A p).trans hq)

theorem isEmbedding_cylinderCoordinates : IsEmbedding (cylinderCoordinates A) := by
  have he : e.heightCylinder ∘ cylinderCoordinates A =
      (fun p : cylinderPart A ↦ p.val.val) := funext (cylinderCoordinates_ambient A)
  apply IsEmbedding.of_comp (cylinderCoordinates A).continuous e.continuous_heightCylinder
  rw [he]
  exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal

def collarTarget : Opens (M × ℝ) :=
  ⟨A.tubeCoordinates.target ×ˢ Ioo (-collarHeight A) (collarHeight A),
    A.tubeCoordinates.open_target.prod isOpen_Ioo⟩

def collarInCylinder : Opens (cylinderPart A) :=
  ⟨cylinderCoordinates A ⁻¹' collarTarget A,
    (collarTarget A).isOpen.preimage (cylinderCoordinates A).continuous⟩

def collarPart : Opens (ambientSet A) :=
  ⟨Subtype.val '' (collarInCylinder A : Set (cylinderPart A)),
    (cylinderPart A).isOpen.isOpenMap_subtype_val _ (collarInCylinder A).isOpen⟩

theorem mem_collarPart_iff (p : ambientSet A) : p ∈ collarPart A ↔
    ∃ hp : p ∈ cylinderPart A, cylinderCoordinates A ⟨p, hp⟩ ∈ collarTarget A := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q.property, hq⟩
  · rintro ⟨hp, hc⟩
    exact ⟨⟨p, hp⟩, hc, rfl⟩

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
