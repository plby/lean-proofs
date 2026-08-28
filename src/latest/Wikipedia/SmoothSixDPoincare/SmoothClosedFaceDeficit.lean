import Wikipedia.SmoothSixDPoincare.SmoothClosedFaceInterior
import Wikipedia.SmoothSixDPoincare.ClosedCoverHomeomorph

/-!
# A continuous normal deficit for the original full attaching face

On the face this is one minus the original normal radius; on the entire
retained exterior it is zero. The functions agree on the actual corner,
so the resulting function is globally continuous and takes values in `[0,1]`.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SmoothClosedFace

variable {E H F K B N X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [TopologicalSpace X] [ChartedSpace K X]
  (C : SmoothClosedFace I J B N X)

theorem deficit_cover : range C.map ∪ C.interiorImageᶜ = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ C.interiorImage
  · exact Or.inl (C.interiorImage_subset_range hx)
  · exact Or.inr hx

def deficitOnFace : C(range C.map, ℝ) :=
  ⟨fun x => 1 - ‖(C.closedEmbedding.isEmbedding.toHomeomorph.symm x).2.val‖,
    continuous_const.sub (continuous_subtype_val.comp (continuous_snd.comp
      C.closedEmbedding.isEmbedding.toHomeomorph.symm.continuous)).norm⟩

theorem deficit_agree (a : range C.map) (b : ↥(C.interiorImageᶜ)) (hab : a.val = b.val) :
    C.deficitOnFace a = 0 := by
  let p := C.closedEmbedding.isEmbedding.toHomeomorph.symm a
  have hp : C.map p = a.val :=
    congrArg Subtype.val (C.closedEmbedding.isEmbedding.toHomeomorph.apply_symm_apply a)
  have hnot : C.map p ∉ C.interiorImage := (hp.trans hab).symm ▸ b.property
  have hn : ‖p.2.val‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp p.2.property)
    (le_of_not_gt (fun h => hnot ((C.map_mem_interiorImage_iff p).mpr h)))
  change 1 - ‖p.2.val‖ = 0
  rw [hn, sub_self]

def normalDeficit : C(X, ℝ) :=
  ⟨ClosedCover.glue C.deficit_cover C.deficitOnFace (fun _ => 0),
    ClosedCover.continuous_glue C.deficit_cover C.closedEmbedding.isClosed_range
      C.isOpen_interiorImage.isClosed_compl C.deficitOnFace (fun _ => 0)
      C.deficitOnFace.continuous continuous_const C.deficit_agree⟩

theorem normalDeficit_face (p : B × MorseHandle.UnitDisk N) :
    C.normalDeficit (C.map p) = 1 - ‖p.2.val‖ := by
  have h := ClosedCover.glue_left C.deficit_cover C.deficitOnFace (fun _ => (0 : ℝ))
    (C.closedEmbedding.isEmbedding.toHomeomorph p)
  exact h.trans (congrArg (fun q : B × MorseHandle.UnitDisk N => 1 - ‖q.2.val‖)
    (C.closedEmbedding.isEmbedding.toHomeomorph.symm_apply_apply p))

theorem normalDeficit_exterior (x : X) (hx : x ∉ C.interiorImage) : C.normalDeficit x = 0 :=
  ClosedCover.glue_right C.deficit_cover C.deficitOnFace (fun _ => (0 : ℝ))
    C.deficit_agree ⟨x, hx⟩

theorem normalDeficit_bounds (x : X) : 0 ≤ C.normalDeficit x ∧ C.normalDeficit x ≤ 1 := by
  by_cases hx : x ∈ range C.map
  · obtain ⟨p, rfl⟩ := hx
    rw [C.normalDeficit_face]
    exact ⟨sub_nonneg.mpr (mem_closedBall_zero_iff.mp p.2.property),
      sub_le_self _ (norm_nonneg _)⟩
  · rw [C.normalDeficit_exterior x (fun h => hx (C.interiorImage_subset_range h))]
    norm_num

theorem normalDeficit_pos_iff (x : X) : 0 < C.normalDeficit x ↔ x ∈ C.interiorImage := by
  by_cases hx : x ∈ range C.map
  · obtain ⟨p, rfl⟩ := hx
    rw [C.normalDeficit_face, C.map_mem_interiorImage_iff]
    exact sub_pos
  · have hnot : x ∉ C.interiorImage := fun h => hx (C.interiorImage_subset_range h)
    rw [C.normalDeficit_exterior x hnot]
    exact iff_of_false (lt_irrefl _) hnot

end Wikipedia.SmoothSixDPoincare.SmoothClosedFace
