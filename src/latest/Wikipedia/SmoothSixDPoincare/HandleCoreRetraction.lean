import Wikipedia.SmoothSixDPoincare.HandleCoreDeformation
import Wikipedia.SmoothSixDPoincare.ClosedPieceMaps

/-! # Retraction of an actual handle attachment onto the old space and core -/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HandleCoreAttachment

open MorseHandle HandleCoreDeformation

variable {N P R X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R] [TopologicalSpace X]
  (r : R → X) (h : C(UnitDisk N × UnitDisk P, X))

def core : C(UnitDisk N, X) :=
  ⟨fun x => h (x, ⟨0, by simp⟩), h.continuous.comp (continuous_id.prodMk continuous_const)⟩

def coreSpace : Set X := range r ∪ range (core h)

variable (hr : IsClosedEmbedding r) (hh : IsClosedEmbedding h)
  (hcover : range r ∪ range h = univ)
  (hface : ∀ z, h z ∈ range r ↔ ‖(z.1 : N)‖ = 1)

include hface in
omit [TopologicalSpace R] in
theorem collapse_lands (z : UnitDisk N × UnitDisk P) : h (collapse z) ∈ coreSpace r h := by
  rcases collapse_mem z with hz | hz
  · exact Or.inl ((hface (collapse z)).mpr hz)
  · right
    refine ⟨(collapse z).1, ?_⟩
    apply congrArg h
    exact Prod.ext rfl (Subtype.ext hz.symm)

def oldToCore : C(R, coreSpace r h) :=
  ⟨fun a => ⟨r a, Or.inl (mem_range_self a)⟩, hr.continuous.subtype_mk _⟩

def handleToCore : C(UnitDisk N × UnitDisk P, coreSpace r h) :=
  ⟨fun z => ⟨h (collapse z), collapse_lands r h hface z⟩,
    (h.continuous.comp collapse.continuous).subtype_mk _⟩

include hface in
theorem coreMaps_agree (a : R) (z : UnitDisk N × UnitDisk P) (haz : r a = h z) :
    oldToCore r h hr a = handleToCore r h hface z := by
  have hz : ‖(z.1 : N)‖ = 1 := (hface z).mp ⟨a, haz⟩
  apply Subtype.ext
  change r a = h (collapse z)
  rw [collapse_face z hz]
  exact haz

/-- Collapse the full attached handle, leaving every point of the original space unchanged. -/
def retraction : C(X, coreSpace r h) :=
  ClosedCover.mapOfClosedPieces r h hr hh hcover (oldToCore r h hr)
    (handleToCore r h hface) (coreMaps_agree r h hr hface)

theorem retraction_old (a : R) :
    (retraction r h hr hh hcover hface (r a) : X) = r a :=
  congrArg Subtype.val (ClosedCover.mapOfClosedPieces_left r h hr hh hcover
    (oldToCore r h hr) (handleToCore r h hface) (coreMaps_agree r h hr hface) a)

theorem retraction_handle (z : UnitDisk N × UnitDisk P) :
    (retraction r h hr hh hcover hface (h z) : X) = h (collapse z) :=
  congrArg Subtype.val (ClosedCover.mapOfClosedPieces_right r h hr hh hcover
    (oldToCore r h hr) (handleToCore r h hface) (coreMaps_agree r h hr hface) z)

theorem retraction_fixed (x : X) (hx : x ∈ coreSpace r h) :
    (retraction r h hr hh hcover hface x : X) = x := by
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact retraction_old r h hr hh hcover hface a
  · change (retraction r h hr hh hcover hface (h (z, ⟨0, by simp⟩)) : X) =
      h (z, ⟨0, by simp⟩)
    rw [retraction_handle, collapse_core _ rfl]

end Wikipedia.SmoothSixDPoincare.HandleCoreAttachment
