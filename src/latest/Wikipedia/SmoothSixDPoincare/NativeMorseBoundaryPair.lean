import Wikipedia.SmoothSixDPoincare.NativeMorseAttachmentFrontier
import Wikipedia.SmoothSixDPoincare.MorseHandleAttachment
import Wikipedia.SmoothSixDPoincare.AttachmentBoundaryPair

/-! # The surgery presentation constructed from the actual native Morse handle -/

noncomputable section

open Set Metric Topology

namespace Wikipedia.SmoothSixDPoincare

namespace MorseHandle

/-- The two standard presentations of the closed unit ball, with identical underlying points. -/
def unitBallHomeomorph (N : Type*) [NormedAddCommGroup N] :
    PuncturedHandle.UnitBall N ≃ₜ UnitDisk N where
  toFun z := ⟨z, mem_closedBall_zero_iff.mpr z.property⟩
  invFun z := ⟨z, mem_closedBall_zero_iff.mp z.property⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

end MorseHandle

namespace ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
def handleBallCoordinates :
    (PuncturedHandle.UnitBall c.NegativeCoordinates ×
      PuncturedHandle.UnitBall c.PositiveCoordinates) ≃ₜ
      (MorseHandle.UnitDisk c.NegativeCoordinates × MorseHandle.UnitDisk c.PositiveCoordinates) :=
  (MorseHandle.unitBallHomeomorph c.NegativeCoordinates).prodCongr
    (MorseHandle.unitBallHomeomorph c.PositiveCoordinates)

open Classical in
/-- The same native handle map, in the norm-ball parametrization used for surgery. -/
def normHandleMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    C(PuncturedHandle.UnitBall c.NegativeCoordinates ×
      PuncturedHandle.UnitBall c.PositiveCoordinates, M) :=
  ⟨fun z => c.attachingHandleMap ρ hρ hblock (c.handleBallCoordinates z),
    (c.attachingHandleMap ρ hρ hblock).continuous.comp c.handleBallCoordinates.continuous⟩

open Classical in
theorem range_normHandleMap (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target) :
    range (c.normHandleMap ρ hρ hblock) = range (c.attachingHandleMap ρ hρ hblock) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨c.handleBallCoordinates z, rfl⟩
  · rintro ⟨z, rfl⟩
    refine ⟨c.handleBallCoordinates.symm z, ?_⟩
    change c.attachingHandleMap ρ hρ hblock
      (c.handleBallCoordinates (c.handleBallCoordinates.symm z)) = _
    rw [c.handleBallCoordinates.apply_symm_apply]

variable [T2Space M]

open Classical in
/-- Every input face identity is proved for the genuine Morse chart and its actual image. -/
def attachmentBoundaryData (hf : Continuous f) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock : closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
      closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆ c.splitChart.target)
    (hlevel : frontier {x | f x ≤ f p - ρ ^ 2} = {x | f x = f p - ρ ^ 2}) :
    AttachmentBoundaryData c.NegativeCoordinates c.PositiveCoordinates M f (f p - ρ ^ 2) where
  handle := c.normHandleMap ρ hρ hblock
  handle_closed := (c.attachingHandleMap_isClosedEmbedding ρ hρ hblock).comp
    c.handleBallCoordinates.isClosedEmbedding
  height_continuous := hf
  lower_frontier := hlevel
  lower_face := fun z => by
    constructor
    · intro hz
      exact (c.attachingHandleMap_lower_iff ρ hρ hblock (c.handleBallCoordinates z)).mp hz.le
    · intro hz
      exact c.attachingHandleMap_boundary_height ρ hρ hblock (c.handleBallCoordinates z) hz
  upper_face := fun z => by
    rw [c.range_normHandleMap ρ hρ hblock]
    exact c.attachingHandleMap_mem_frontier_iff hf ρ hρ hblock (c.handleBallCoordinates z)

end ManifoldMorse.SignedMorseChart

end Wikipedia.SmoothSixDPoincare
