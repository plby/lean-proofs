import ErdosProblems.Erdos73.ParityPendantGraph
import ErdosProblems.Erdos73.FiniteSequencePath

/-! Project paths whose vertices all belong to the original graph. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {T : Finset V} {c : V → Bool}

theorem project_original_pendant_path (P : GraphPath (parityPendantGraph G T c))
    (horig : ∀ x ∈ P.vertexSet, x = Sum.inl (pendantProjection x)) :
    ∃ Q : GraphPath G, Q.source = pendantProjection P.source ∧
      Q.target = pendantProjection P.target ∧ Q.walk.length = P.walk.length ∧
      Q.vertexSet ⊆ P.vertexSet.image pendantProjection := by
  let f : Fin (P.walk.length + 1) → V := fun i => pendantProjection (P.walk.getVert i.val)
  have hget (i : ℕ) : P.walk.getVert i = Sum.inl (pendantProjection (P.walk.getVert i)) :=
    horig _ (List.mem_toFinset.mpr (P.walk.getVert_mem_support i))
  have hf : Function.Injective f := by
    intro i j hij
    have he : P.walk.getVert i.val = P.walk.getVert j.val := by
      rw [hget i.val, hget j.val]
      exact congrArg Sum.inl hij
    exact Fin.ext (P.isPath.getVert_injOn (Nat.le_of_lt_succ i.isLt)
      (Nat.le_of_lt_succ j.isLt) he)
  have ha : ∀ i (hi : i + 1 < P.walk.length + 1),
      G.Adj (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) := by
    intro i hi
    have hh := P.walk.adj_getVert_succ (show i < P.walk.length by omega)
    rw [hget i, hget (i + 1)] at hh
    exact hh
  refine ⟨GraphPath.ofSequence f hf ha, ?_, ?_, GraphPath.ofSequence_length f hf ha, ?_⟩
  · simp only [GraphPath.ofSequence_source, f, Fin.val_zero, Walk.getVert_zero]
  · simp only [GraphPath.ofSequence_target, f, Fin.val_last, Walk.getVert_length]
  · intro v hv
    obtain ⟨i, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hf ha v).mp hv
    exact mem_image.mpr ⟨P.walk.getVert i.val,
      List.mem_toFinset.mpr (P.walk.getVert_mem_support _), rfl⟩

end
end Erdos73
