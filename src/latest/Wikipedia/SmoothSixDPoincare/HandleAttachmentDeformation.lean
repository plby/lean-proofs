import Wikipedia.SmoothSixDPoincare.HandleCoreRetraction
import Mathlib.Topology.Homotopy.Equiv

/-!
# The actual handle attachment deforms onto the old space and core

Glue the entire relative model deformation to the stationary old space.
The time-dependent maps agree on the actual attaching face, so closed-piece
gluing gives a continuous homotopy of the whole attachment. The resulting
homotopy equivalence is the original inclusion of the old space plus core.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.HandleCoreAttachment

open MorseHandle

variable {N P R X : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [TopologicalSpace R] [TopologicalSpace X]
  (r : R → X) (h : C(UnitDisk N × UnitDisk P, X))
  (hr : IsClosedEmbedding r) (hh : IsClosedEmbedding h)
  (hcover : range r ∪ range h = univ)
  (hface : ∀ z, h z ∈ range r ↔ ‖(z.1 : N)‖ = 1)

include hcover in
omit [NormedSpace ℝ N] [NormedSpace ℝ P] [TopologicalSpace R] in
theorem time_cover : range (Prod.map (id : I → I) r) ∪
    range (Prod.map (id : I → I) h) = univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨t, x⟩
  have hx : x ∈ range r ∪ range h := by rw [hcover]; trivial
  rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
  · exact Or.inl ⟨(t, a), rfl⟩
  · exact Or.inr ⟨(t, z), rfl⟩

def oldMotion : C(I × R, X) :=
  ⟨fun q => r q.2, hr.continuous.comp continuous_snd⟩

def handleMotion : C(I × (UnitDisk N × UnitDisk P), X) :=
  h.comp HandleCoreDeformation.deformation.toHomotopy.toContinuousMap

include hface in
theorem motions_agree (a : I × R) (z : I × (UnitDisk N × UnitDisk P))
    (haz : Prod.map id r a = Prod.map id h z) :
    oldMotion r hr a = handleMotion h z := by
  have ha : r a.2 = h z.2 := congrArg Prod.snd haz
  have hz : z.2 ∈ HandleCoreDeformation.faceCore := Or.inl ((hface z.2).mp ⟨a.2, ha⟩)
  change r a.2 = h (HandleCoreDeformation.deformation (z.1, z.2))
  rw [HandleCoreDeformation.deformation.eq_fst z.1 hz]
  exact ha

def motion : C(I × X, X) :=
  ClosedCover.mapOfClosedPieces (Prod.map id r) (Prod.map id h)
    (IsClosedEmbedding.id.prodMap hr) (IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h) (motions_agree r h hr hface)

theorem motion_old (t : I) (a : R) :
    motion r h hr hh hcover hface (t, r a) = r a :=
  ClosedCover.mapOfClosedPieces_left (Prod.map id r) (Prod.map id h)
    (IsClosedEmbedding.id.prodMap hr) (IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h)
    (motions_agree r h hr hface) (t, a)

theorem motion_handle (t : I) (z : UnitDisk N × UnitDisk P) :
    motion r h hr hh hcover hface (t, h z) = h (HandleCoreDeformation.deformation (t, z)) :=
  ClosedCover.mapOfClosedPieces_right (Prod.map id r) (Prod.map id h)
    (IsClosedEmbedding.id.prodMap hr) (IsClosedEmbedding.id.prodMap hh)
    (time_cover r h hcover) (oldMotion r hr) (handleMotion h)
    (motions_agree r h hr hface) (t, z)

def coreInclusion : C(coreSpace r h, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- A strong deformation of the entire attachment, fixed on the old space and full core. -/
def deformation : (ContinuousMap.id X).HomotopyRel
    ((coreInclusion r h).comp (retraction r h hr hh hcover hface)) (coreSpace r h) where
  toFun := motion r h hr hh hcover hface
  continuous_toFun := (motion r h hr hh hcover hface).continuous
  map_zero_left x := by
    have hx : x ∈ range r ∪ range h := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact motion_old r h hr hh hcover hface 0 a
    · rw [motion_handle]
      exact congrArg h (HandleCoreDeformation.deformation.toHomotopy.map_zero_left z)
  map_one_left x := by
    change motion r h hr hh hcover hface (1, x) = (retraction r h hr hh hcover hface x : X)
    have hx : x ∈ range r ∪ range h := by rw [hcover]; trivial
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · rw [motion_old, retraction_old]
    · rw [motion_handle, retraction_handle]
      exact congrArg h (HandleCoreDeformation.deformation.toHomotopy.map_one_left z)
  prop' t x hx := by
    change motion r h hr hh hcover hface (t, x) = x
    rcases hx with ⟨a, rfl⟩ | ⟨z, rfl⟩
    · exact motion_old r h hr hh hcover hface t a
    · change motion r h hr hh hcover hface (t, h (z, ⟨0, by simp⟩)) = h (z, ⟨0, by simp⟩)
      rw [motion_handle]
      exact congrArg h (HandleCoreDeformation.deformation.eq_fst t (Or.inr rfl))

/-- The original inclusion of the old space and core is a homotopy equivalence. -/
def homotopyEquiv : coreSpace r h ≃ₕ X where
  toFun := coreInclusion r h
  invFun := retraction r h hr hh hcover hface
  left_inv := by
    have heq : (retraction r h hr hh hcover hface).comp (coreInclusion r h) =
        ContinuousMap.id (coreSpace r h) := by
      apply ContinuousMap.ext
      intro x
      exact Subtype.ext (retraction_fixed r h hr hh hcover hface x.val x.property)
    rw [heq]
  right_inv := ⟨(deformation r h hr hh hcover hface).toHomotopy.symm⟩

theorem homotopyEquiv_apply (x : coreSpace r h) :
    homotopyEquiv r h hr hh hcover hface x = (x : X) := rfl

end Wikipedia.SmoothSixDPoincare.HandleCoreAttachment
