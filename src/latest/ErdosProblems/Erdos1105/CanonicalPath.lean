import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

/-- The increasing walk through a path graph, in the vertex convention used
by the statement of Problem 1105. -/
def canonicalPath (n : ℕ) : (pathGraph (n + 1)).Walk 0 (Fin.last n) :=
  (Walk.ofSupport (G := pathGraph (n + 1)) (List.ofFn (fun i : Fin (n + 1) ↦ i))
    (by simp) (List.isChain_ofFn.mpr (by
      intro i hi
      simp [pathGraph_adj]))).copy
        (by simp [List.ofFn_succ]) (List.getLast_ofFn_succ (fun i : Fin (n + 1) ↦ i))

@[simp] theorem canonicalPath_support (n : ℕ) :
    (canonicalPath n).support = List.ofFn (fun i : Fin (n + 1) ↦ i) := by
  simp [canonicalPath]

@[simp] theorem canonicalPath_length (n : ℕ) : (canonicalPath n).length = n := by
  simp [canonicalPath]

theorem canonicalPath_isPath (n : ℕ) : (canonicalPath n).IsPath := by
  apply Walk.IsPath.mk'
  rw [canonicalPath_support]
  exact List.nodup_ofFn.mpr Function.injective_id

theorem canonicalPath_getVert (n i : ℕ) (hi : i ≤ n) :
    (canonicalPath n).getVert i = ⟨i, by omega⟩ := by
  have hi' : i < (canonicalPath n).support.length := by simp; omega
  have h := (canonicalPath n).support_getElem_eq_getVert hi'
  simpa only [canonicalPath_support, List.getElem_ofFn] using h.symm

theorem canonicalPath_isHamiltonian (n : ℕ) : (canonicalPath n).IsHamiltonian := by
  apply (canonicalPath_isPath n).isHamiltonian_of_mem
  intro i
  rw [canonicalPath_support]
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

end Erdos1105
