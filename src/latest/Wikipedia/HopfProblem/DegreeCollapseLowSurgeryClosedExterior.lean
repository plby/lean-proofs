import Wikipedia.HopfProblem.DegreeCollapseLowNativeClosedCap
import Wikipedia.HopfProblem.DegreeCollapseLowRetainedExterior

/-!

# The actual common closed exterior and its shared sphere-product face

Remove the open original tube at the constructed outer face radius. This
closed exterior lies strictly inside the smoothly retained region. Its maps
to the old manifold and native new end are closed embeddings, and the new
cap agrees with it on the exact original sphere-product face.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair

open NoExoticSixSphere GLOrthonormalization Stiefel RoundedTrace
open Wikipedia.SmoothSixDPoincare.PuncturedHandle

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)

def closedExterior : Set M :=
  (A.tube '' ((univ : Set (NoExoticSixSphere.Sphere d)) ×ˢ
    ball (0 : Vector (7 - d)) (oldRadius A)))ᶜ

theorem isClosed_closedExterior : IsClosed (closedExterior A) := by
  apply IsOpen.isClosed_compl
  exact A.tubeCoordinates.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_ball)
    (fun p hp ↦ ⟨hp.1, (ball_subset_ball (oldRadius_lt A).le) hp.2⟩)

theorem compactSpace_closedExterior : CompactSpace (closedExterior A) :=
  isCompact_iff_compactSpace.mp (isClosed_closedExterior A).isCompact

theorem closedExterior_subset_retained : closedExterior A ⊆ retainedExterior A := by
  intro m hm ho
  apply hm
  obtain ⟨p, hp, he⟩ := ho
  exact ⟨p, ⟨hp.1, (closedBall_subset_ball (oldRadius_gt_outer A)) hp.2⟩, he⟩

def closedExteriorPoint (p : closedExterior A) : retainedExterior A :=
  ⟨p.val, closedExterior_subset_retained A p.property⟩

theorem continuous_closedExteriorPoint : Continuous (closedExteriorPoint A) :=
  continuous_subtype_val.subtype_mk _

theorem tube_mem_closedExterior_iff (s : NoExoticSixSphere.Sphere d)
    {v : Vector (7 - d)} (hv : v ∈ ball (0 : Vector (7 - d)) A.radius) :
    A.tube (s, v) ∈ closedExterior A ↔ oldRadius A ≤ ‖v‖ := by
  constructor
  · intro hm
    by_contra hn
    apply hm
    exact ⟨(s, v), ⟨mem_univ _, by
      simpa only [mem_ball, dist_zero_right] using lt_of_not_ge hn⟩, rfl⟩
  · intro hn hm
    obtain ⟨q, hq, he⟩ := hm
    have hqA : q ∈ A.openTubeDomain :=
      ⟨hq.1, (ball_subset_ball (oldRadius_lt A).le) hq.2⟩
    have hsA : (s, v) ∈ A.openTubeDomain := ⟨mem_univ _, hv⟩
    have heq : q = (s, v) := A.injOn_tube_openTubeDomain hqA hsA he
    have hnorm : ‖q.2‖ < oldRadius A := by
      simpa only [mem_ball, dist_zero_right] using hq.2
    rw [congrArg Prod.snd heq] at hnorm
    exact (not_lt_of_ge hn) hnorm

theorem commonFace_vector_norm (w : sphere (0 : Vector (7 - d)) 1) :
    ‖oldRadius A • w.val‖ = oldRadius A := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (oldRadius_pos A),
    mem_sphere_zero_iff_norm.mp w.property, mul_one]

def commonFace (q : NoExoticSixSphere.Sphere d × sphere (0 : Vector (7 - d)) 1) :
    closedExterior A :=
  ⟨A.tube (q.1, oldRadius A • q.2.val),
    (tube_mem_closedExterior_iff A q.1 (by
      rw [mem_ball, dist_zero_right, commonFace_vector_norm]
      exact oldRadius_lt A)).mpr (by rw [commonFace_vector_norm])⟩

theorem commonFace_val
    (q : NoExoticSixSphere.Sphere d × sphere (0 : Vector (7 - d)) 1) :
    (commonFace A q).val = A.tube (q.1, oldRadius A • q.2.val) := rfl

def oldExterior (p : closedExterior A) : M := p.val

theorem isClosedEmbedding_oldExterior : IsClosedEmbedding (oldExterior A) :=
  (isClosed_closedExterior A).isClosedEmbedding_subtypeVal

variable [IsManifold (𝓡 7) ∞ M]

def newExterior (p : closedExterior A) : otherBoundaryPart A :=
  (exteriorNativeHomeomorph A (closedExteriorPoint A p)).val

theorem newExterior_ambient (p : closedExterior A) :
    (newExterior A p).val.val.val = LowHeightCylinder.heightCylinder d e (p.val, 0) := rfl

theorem continuous_newExterior : Continuous (newExterior A) :=
  continuous_subtype_val.comp
    ((exteriorNativeHomeomorph A).continuous_toFun.comp (continuous_closedExteriorPoint A))

theorem newExterior_injective : Injective (newExterior A) := by
  intro p q h
  apply Subtype.ext
  have he := congrArg (fun y : otherBoundaryPart A ↦ y.val.val.val) h
  rw [newExterior_ambient, newExterior_ambient] at he
  exact congrArg Prod.fst ((LowHeightCylinder.injective_heightCylinder d e) he)

theorem isClosedEmbedding_newExterior : IsClosedEmbedding (newExterior A) := by
  let := compactSpace_closedExterior A
  exact (continuous_newExterior A).isClosedEmbedding (newExterior_injective A)

theorem newExterior_commonFace (hR : A.radius = 2)
    (q : NoExoticSixSphere.Sphere d × sphere (0 : Vector (7 - d)) 1) :
    newExterior A (commonFace A q) = nativeCapPoint A hR (newBoundary q) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [newExterior_ambient, commonFace_val]
  exact (nativeCapPoint_newBoundary A hR q.1 q.2).symm

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.SurgeryPair
