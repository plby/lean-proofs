import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

/-! # Transporting an actual surgery boundary along a boundary homeomorphism -/

noncomputable section

open Set Topology

namespace Wikipedia.SmoothSixDPoincare

namespace SurgeryBoundaryPair

variable {N P R X Y Z : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (d : SurgeryBoundaryPair N P R X Y)

/-- Move the new boundary by a genuine homeomorphism, preserving the common exterior and face. -/
def changeNewBoundary (e : Y ≃ₜ Z) : SurgeryBoundaryPair N P R X Z where
  oldExterior := d.oldExterior
  newExterior := e ∘ d.newExterior
  oldPiece := d.oldPiece
  newPiece := e ∘ d.newPiece
  oldExterior_closed := d.oldExterior_closed
  newExterior_closed := e.isClosedEmbedding.comp d.newExterior_closed
  oldPiece_closed := d.oldPiece_closed
  newPiece_closed := e.isClosedEmbedding.comp d.newPiece_closed
  old_cover := d.old_cover
  new_cover := by
    apply eq_univ_of_forall
    intro z
    have hz : e.symm z ∈ range d.newExterior ∪ range d.newPiece := by rw [d.new_cover]; trivial
    rcases hz with ⟨r, hr⟩ | ⟨p, hp⟩
    · exact Or.inl ⟨r, (congrArg e hr).trans (e.apply_symm_apply z)⟩
    · exact Or.inr ⟨p, (congrArg e hp).trans (e.apply_symm_apply z)⟩
  boundary := d.boundary
  old_overlap := d.old_overlap
  new_overlap := fun r p => e.injective.eq_iff.trans (d.new_overlap r p)

end SurgeryBoundaryPair

namespace ClosedCover

variable {M : Type*} [TopologicalSpace M] {f : M → ℝ} {b : ℝ} {A : Set M}

/-- Restrict the proved frontier/level correspondence of a sublevel homeomorphism. -/
def frontierLevelHomeomorph (hA : IsClosed A) (e : A ≃ₜ {x : M // f x ≤ b})
    (he : ∀ x, f (e x) = b ↔ (x : M) ∈ frontier A) :
    frontier A ≃ₜ {x : M // f x = b} := by
  have hsub : frontier A ⊆ A := by
    intro x hx
    have hc := frontier_subset_closure hx
    rwa [hA.closure_eq] at hc
  let toA : frontier A → A := Set.inclusion hsub
  let toB : {x : M // f x = b} → {x : M // f x ≤ b} := fun x => ⟨x, x.property.le⟩
  refine
    { toFun := fun x => ⟨e (toA x), (he (toA x)).mpr x.property⟩
      invFun := fun y => ⟨e.symm (toB y), ?_⟩
      left_inv := ?_
      right_inv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (he (e.symm (toB y))).mp
    rw [e.apply_symm_apply]
    exact y.property
  · intro x
    apply Subtype.ext
    exact congrArg (fun z : A => (z : M)) (e.symm_apply_apply (toA x))
  · intro y
    apply Subtype.ext
    exact congrArg (fun z : {x : M // f x ≤ b} => (z : M)) (e.apply_symm_apply (toB y))
  · exact (continuous_subtype_val.comp (e.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _
  · exact (continuous_subtype_val.comp (e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _

end ClosedCover

end Wikipedia.SmoothSixDPoincare
