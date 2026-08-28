import Wikipedia.SmoothSixDPoincare.OpenGluingSeparation
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! # Gluing two patches using their actual common overlap parametrization -/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.OpenGluing

variable {O X Y : Type*} [TopologicalSpace O] [Nonempty O]
  [TopologicalSpace X] [TopologicalSpace Y]
  {i : O → X} {j : O → Y} (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)

def overlapTransition : OpenPartialHomeomorph X Y :=
  hi.toOpenPartialHomeomorph.symm.trans hj.toOpenPartialHomeomorph

theorem overlapTransition_source : (overlapTransition hi hj).source = range i := by
  simp only [overlapTransition, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]

theorem overlapTransition_target : (overlapTransition hi hj).target = range j := by
  simp only [overlapTransition, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target, IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]

theorem overlapTransition_apply (o : O) : overlapTransition hi hj (i o) = j o := by
  change j (hi.toOpenPartialHomeomorph.symm (i o)) = j o
  rw [hi.toOpenPartialHomeomorph_left_inv]

theorem overlapTransition_symm_apply (o : O) : (overlapTransition hi hj).symm (j o) = i o := by
  change i (hj.toOpenPartialHomeomorph.symm (j o)) = i o
  rw [hj.toOpenPartialHomeomorph_left_inv]

theorem overlapTransition_graph (x : X) (y : Y) :
    (x ∈ (overlapTransition hi hj).source ∧ overlapTransition hi hj x = y) ↔
      ∃ o : O, i o = x ∧ j o = y := by
  rw [overlapTransition_source]
  constructor
  · rintro ⟨⟨o, rfl⟩, hy⟩
    exact ⟨o, rfl, (overlapTransition_apply hi hj o).symm.trans hy⟩
  · rintro ⟨o, rfl, rfl⟩
    exact ⟨⟨o, rfl⟩, overlapTransition_apply hi hj o⟩

theorem overlapTransition_t2Space [T2Space X] [T2Space Y]
    (hclosed : IsClosed (range (fun o : O => (i o, j o)))) :
    T2Space (Space (overlapTransition hi hj)) := by
  apply (t2Space_iff_closed_graph (overlapTransition hi hj)).mpr
  have heq : {p : X × Y | p.1 ∈ (overlapTransition hi hj).source ∧
      overlapTransition hi hj p.1 = p.2} = range (fun o : O => (i o, j o)) := by
    ext ⟨x, y⟩
    rw [mem_ofPred_eq, overlapTransition_graph]
    simp only [mem_range, Prod.mk.injEq]
  rw [heq]
  exact hclosed

end Wikipedia.SmoothSixDPoincare.OpenGluing
