import Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
import Mathlib.Topology.Sets.Opens

/-! # An open part of the boundary has an open inward collar image -/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {i : C(X, Y)}
  (C : InwardBoundaryCollar i)

theorem inner_image_open (V : TopologicalSpace.Opens X) :
    IsOpen (C.map '' {q : X × unitInterval | q.1 ∈ V ∧ q.2 < 1}) := by
  obtain ⟨O, hO, hpre⟩ := C.closedEmbedding.isEmbedding.isInducing.isOpen_iff.mp
    (V.isOpen.preimage (continuous_fst : Continuous (Prod.fst : X × unitInterval → X)))
  have heq : C.map '' {q : X × unitInterval | q.1 ∈ V ∧ q.2 < 1} =
      O ∩ (C.map '' {q : X × unitInterval | q.2 < 1}) := by
    ext y
    constructor
    · rintro ⟨q, ⟨hV, ht⟩, rfl⟩
      refine ⟨?_, ⟨q, ht, rfl⟩⟩
      exact show q ∈ C.map ⁻¹' O from hpre.symm ▸ hV
    · rintro ⟨hO, q, ht, rfl⟩
      exact ⟨q, ⟨show q ∈ Prod.fst ⁻¹' (V : Set X) from hpre ▸ hO, ht⟩, rfl⟩
  exact heq.symm ▸ hO.inter C.inner_open

end Wikipedia.SmoothSixDPoincare.InwardBoundaryCollar
