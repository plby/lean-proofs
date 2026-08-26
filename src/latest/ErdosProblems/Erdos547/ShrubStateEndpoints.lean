import ErdosProblems.Erdos547.ShrubState

/-!
# Initial and completed partial shrub embeddings
-/

namespace Erdos547.ShrubState

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [DecidableEq U] [DecidableEq V]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} {C : I → Finset V} {head : ↥P.shrubs → I}
  {seed : (T.induce (P.seeds : Set U)).Copy G}

theorem exists_initial : ∃ E : ShrubState P G C head seed,
    E.placed = ∅ ∧ E.occupied = Finset.univ.image seed := by
  classical
  let f : (T.induce ((P.shrubDomain ∅ : Finset U) : Set U)).Copy G := {
    toHom := {
      toFun := fun v ↦ seed ⟨v.val, by simpa only [P.shrubDomain_empty] using v.property⟩
      map_rel' := fun h ↦ seed.toHom.map_adj h
    }
    injective' := by
      intro v w h
      exact Subtype.ext (congrArg (fun z : ↥P.seeds ↦ z.val) (seed.injective h))
  }
  let E : ShrubState P G C head seed := {
    placed := ∅
    tail := head
    copy := f
    seed_eq := fun _ ↦ rfl
    near_mem := fun _ h ↦ (Finset.notMem_empty _ h).elim
    far_mem := fun _ h ↦ (Finset.notMem_empty _ h).elim
  }
  refine ⟨E, rfl, ?_⟩
  ext v
  rw [E.mem_occupied_iff]
  simp only [E, Finset.notMem_empty, IsEmpty.exists_iff, exists_false, or_false,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨x, hx⟩ <;> exact ⟨x, hx⟩

theorem isContained_of_all_placed (E : ShrubState P G C head seed)
    (hfull : E.placed = Finset.univ) : T ⊑ G := by
  have hdomain : P.shrubDomain E.placed = Finset.univ := by
    rw [hfull, P.shrubDomain_univ]
  refine ⟨{
    toHom := {
      toFun := fun u ↦ E.copy ⟨u, by rw [hdomain]; exact Finset.mem_univ _⟩
      map_rel' := fun h ↦ E.copy.toHom.map_adj h
    }
    injective' := ?_
  }⟩
  intro u v h
  exact congrArg (fun z : ↥(P.shrubDomain E.placed) ↦ z.val) (E.copy.injective h)

end Erdos547.ShrubState

#print axioms Erdos547.ShrubState.exists_initial
#print axioms Erdos547.ShrubState.isContained_of_all_placed
