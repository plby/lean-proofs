import ErdosProblems.Erdos547.ShrubPrivatePhase
import ErdosProblems.Erdos547.ShrubReservoirPhase

/-!
# Embedding the whole tree from the explicit regular-pair setup
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]

theorem isContained (H : ShrubHostSetup P G I) (hT : T.IsTree) : T ⊑ G := by
  classical
  obtain ⟨E, hplaced, hcap, hbound, hreserved⟩ := H.exists_initial_state
  have hEF : Disjoint E.placed Finset.univ := by rw [hplaced]; simp
  obtain ⟨E', B, _, hplaced', hcap', hbound', hsmall⟩ := H.process_heads hT Finset.univ E
    Finset.univ (fun _ _ ↦ Finset.mem_univ _) hEF hcap hbound hreserved
  have heq : E'.placed = Finset.univ \ B := by
    simpa only [hplaced, Finset.empty_union] using hplaced'
  have hEB : Disjoint E'.placed B := by
    rw [heq]
    exact Finset.sdiff_disjoint
  have hcover : E'.placed ∪ B = Finset.univ := by
    rw [heq, Finset.sdiff_union_of_subset (Finset.subset_univ _)]
  have hboundB : H.ReservoirBound E' B := by
    intro i
    have hh := hbound' i
    have hz : H.primaryCount E'.placed ∅ i = 0 := by simp [primaryCount]
    rw [hz, Nat.add_zero] at hh
    exact hh.trans (Nat.le_add_right _ _)
  exact H.complete_reservoir_phase hT E' B hEB hcover hcap' hboundB hsmall

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.isContained
