import ErdosProblems.Erdos547.AttachLeaves

/-!
# Extending the bipartition when leaves are attached
-/

namespace Erdos547

open SimpleGraph

def flipTreeColour (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem flipTreeColour_ne (i : Fin 2) : flipTreeColour i ≠ i := by
  fin_cases i <;> decide

theorem flipTreeColour_involutive (i : Fin 2) : flipTreeColour (flipTreeColour i) = i := by
  fin_cases i <;> decide

def attachLeavesColour {U L : Type*} {T : SimpleGraph U} (parent : L → U)
    (col : T.Coloring (Fin 2)) : (attachLeaves T parent).Coloring (Fin 2) where
  toFun := Sum.elim col (fun l ↦ flipTreeColour (col (parent l)))
  map_rel' := by
    intro x y h
    cases x with
    | inl u =>
        cases y with
        | inl v => exact col.valid h
        | inr l =>
            change u = parent l at h
            subst u
            exact (flipTreeColour_ne _).symm
    | inr l =>
        cases y with
        | inl u =>
            change parent l = u at h
            subst u
            exact flipTreeColour_ne _
        | inr m => exact False.elim h

@[simp] theorem attachLeavesColour_inl {U L : Type*} {T : SimpleGraph U} (parent : L → U)
    (col : T.Coloring (Fin 2)) (u : U) : attachLeavesColour parent col (Sum.inl u) = col u := rfl

@[simp] theorem attachLeavesColour_inr {U L : Type*} {T : SimpleGraph U} (parent : L → U)
    (col : T.Coloring (Fin 2)) (l : L) :
    attachLeavesColour parent col (Sum.inr l) = flipTreeColour (col (parent l)) := rfl

end Erdos547

#print axioms Erdos547.attachLeavesColour
