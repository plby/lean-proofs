import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodyCap
import Wikipedia.SmoothSixDPoincare.CommonBaseAttachmentRealization

/-!
# Transport a whole disk cap through an exact boundary/body equivalence

The original cap disk keeps every parameter. Only old-body coordinates
change. The boundary equivalence is the restriction of the specified
native diffeomorphism to the complements of the matched sphere images.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody

variable {G H : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} {U V : SmoothBoundaryBody J} (e : Equiv U V)
  {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  (j : C(PuncturedHandle.UnitSphere N, U.boundary)) (hj : IsClosedEmbedding j)
  (hopen : IsOpen (range j))
  (j' : C(PuncturedHandle.UnitSphere N, V.boundary)) (hj' : IsClosedEmbedding j')
  (hopen' : IsOpen (range j')) (hface : ∀ u, e.boundary (j u) = j' u)

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
include hface in
theorem capBoundary_mem_iff (x : U.boundary) :
    x ∈ U.capBoundary j hj ↔ e.boundary x ∈ V.capBoundary j' hj' := by
  change x ∉ range j ↔ e.boundary x ∉ range j'
  apply not_congr
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, (hface u).symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, e.boundary.injective ((hface u).trans hu)⟩

def capBoundaryEquiv : Diffeomorph J J (U.capBoundary j hj) (V.capBoundary j' hj') ∞ := by
  let h := e.boundary.toHomeomorph.subtype (capBoundary_mem_iff e j hj j' hj' hface)
  refine {
    toEquiv := h.toEquiv
    contMDiff_toFun := ?_
    contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (V.capBoundary j' hj') _).mp
    exact e.boundary.contMDiff.comp contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff (U.capBoundary j hj) _).mp
    exact e.boundary.symm.contMDiff.comp contMDiff_subtype_val

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
theorem capBoundaryEquiv_point (x : U.capBoundary j hj) :
    (capBoundaryEquiv e j hj j' hj' hface x).val = e.boundary x.val := rfl

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
include hface in
theorem capFaceMap_change : e.body.toHomotopyEquiv.toFun.comp (U.capFaceMap j) =
    V.capFaceMap j' := by
  ext u
  exact (e.boundary_point (j (DiskCap.boundaryCoordinates N u))).trans
    (congrArg V.inclusion (hface (DiskCap.boundaryCoordinates N u)))

def capBodyEquiv : (U.cap j hj hopen).body ≃ₜ (V.cap j' hj' hopen').body :=
  (FaceAttachment.baseCongr (U.capFaceMap j) e.body).trans
    (FaceAttachment.congrFaceMap (capFaceMap_change e j j' hface))

theorem capBodyEquiv_old (x : U.body) :
    capBodyEquiv e j hj hopen j' hj' hopen' hface (FaceAttachment.oldMap (U.capFaceMap j) x) =
      FaceAttachment.oldMap (V.capFaceMap j') (e.body x) := by
  exact (congrArg (FaceAttachment.congrFaceMap (capFaceMap_change e j j' hface))
    (FaceAttachment.baseCongr_old (U.capFaceMap j) e.body x)).trans
      (FaceAttachment.congrFaceMap_old (capFaceMap_change e j j' hface) (e.body x))

theorem capBodyEquiv_disk (u : MorseHandle.UnitDisk N) :
    capBodyEquiv e j hj hopen j' hj' hopen' hface (FaceAttachment.handleMap (U.capFaceMap j) u) =
      FaceAttachment.handleMap (V.capFaceMap j') u := by
  exact (congrArg (FaceAttachment.congrFaceMap (capFaceMap_change e j j' hface))
    (FaceAttachment.baseCongr_handle (U.capFaceMap j) e.body u)).trans
      (FaceAttachment.congrFaceMap_handle (capFaceMap_change e j j' hface) u)

def capEquiv : Equiv (U.cap j hj hopen) (V.cap j' hj' hopen') where
  body := capBodyEquiv e j hj hopen j' hj' hopen' hface
  boundary := capBoundaryEquiv e j hj j' hj' hface
  boundary_point x :=
    (capBodyEquiv_old e j hj hopen j' hj' hopen' hface (U.inclusion x.val)).trans
      (congrArg (FaceAttachment.oldMap (V.capFaceMap j')) (e.boundary_point x.val))

theorem capEquiv_symm_old (x : V.body) :
    (capEquiv e j hj hopen j' hj' hopen' hface).body.symm
        (FaceAttachment.oldMap (V.capFaceMap j') x) =
      FaceAttachment.oldMap (U.capFaceMap j) (e.body.symm x) := by
  apply (capEquiv e j hj hopen j' hj' hopen' hface).body.injective
  exact ((capEquiv e j hj hopen j' hj' hopen' hface).body.apply_symm_apply _).trans
    ((capBodyEquiv_old e j hj hopen j' hj' hopen' hface (e.body.symm x)).trans
      (congrArg (FaceAttachment.oldMap (V.capFaceMap j')) (e.body.apply_symm_apply x))).symm

theorem capEquiv_symm_disk (u : MorseHandle.UnitDisk N) :
    (capEquiv e j hj hopen j' hj' hopen' hface).body.symm
        (FaceAttachment.handleMap (V.capFaceMap j') u) =
      FaceAttachment.handleMap (U.capFaceMap j) u := by
  apply (capEquiv e j hj hopen j' hj' hopen' hface).body.injective
  exact ((capEquiv e j hj hopen j' hj' hopen' hface).body.apply_symm_apply _).trans
    (capBodyEquiv_disk e j hj hopen j' hj' hopen' hface u).symm

def capPostcompose : C(PuncturedHandle.UnitSphere N, V.boundary) :=
  ⟨fun u => e.boundary (j u), e.boundary.continuous.comp j.continuous⟩

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
include hj in
theorem capPostcompose_isClosedEmbedding : IsClosedEmbedding (capPostcompose e j) :=
  e.boundary.toHomeomorph.isClosedEmbedding.comp hj

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
include hopen in
theorem capPostcompose_isOpen : IsOpen (range (capPostcompose e j)) := by
  change IsOpen (range (e.boundary ∘ j))
  rw [range_comp]
  exact e.boundary.toHomeomorph.isOpenMap _ hopen

end Wikipedia.SmoothSixDPoincare.SmoothBoundaryBody
