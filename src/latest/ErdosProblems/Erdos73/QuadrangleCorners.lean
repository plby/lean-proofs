import ErdosProblems.Erdos73.QuadrangularFaceSwitch
import Mathlib.Data.Fin.VecNotation

/-! The four-corner permutations used in the explicit quadrangulation. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

def quadrangleOpposite : Perm (Fin 4) := swap 0 2 * swap 1 3

def quadranglePair (odd : Bool) : Perm (Fin 4) :=
  if odd then swap 0 3 * swap 1 2 else swap 0 1 * swap 2 3

def quadrangleSelected (flipped : Bool) (i : Fin 4) : Bool :=
  if flipped then decide (i.val % 2 = 1) else decide (i.val % 2 = 0)

theorem quadrangleOpposite_involutive : Function.Involutive quadrangleOpposite := by
  intro i
  fin_cases i <;> simp [quadrangleOpposite, swap_apply_def, Fin.ext_iff]

theorem quadrangleOpposite_free (i : Fin 4) : quadrangleOpposite i ≠ i := by
  fin_cases i <;> simp [quadrangleOpposite, swap_apply_def, Fin.ext_iff]

theorem quadranglePair_involutive (b : Bool) : Function.Involutive (quadranglePair b) := by
  intro i
  cases b <;> fin_cases i <;> simp [quadranglePair, swap_apply_def, Fin.ext_iff]

theorem quadranglePair_free (b : Bool) (i : Fin 4) : quadranglePair b i ≠ i := by
  cases b <;> fin_cases i <;> simp [quadranglePair, swap_apply_def, Fin.ext_iff]

theorem quadranglePair_commute (b : Bool) :
    Function.Commute (quadranglePair b) quadrangleOpposite := by
  intro i
  cases b <;> fin_cases i <;> simp [quadranglePair, quadrangleOpposite, swap_apply_def, Fin.ext_iff]

theorem quadrangleOpposite_pair (b : Bool) (i : Fin 4) :
    quadrangleOpposite (quadranglePair b i) = quadranglePair (!b) i := by
  cases b <;> fin_cases i <;>
    simp [quadranglePair, quadrangleOpposite, swap_apply_def, Fin.ext_iff]

theorem quadrangleSelected_opposite (b : Bool) (i : Fin 4) :
    quadrangleSelected b (quadrangleOpposite i) = quadrangleSelected b i := by
  cases b <;> fin_cases i <;> simp [quadrangleSelected, quadrangleOpposite, swap_apply_def, Fin.ext_iff]

theorem quadrangleSelected_pair (b f : Bool) (i : Fin 4) :
    quadrangleSelected f (quadranglePair b i) = !(quadrangleSelected f i) := by
  cases b <;> cases f <;> fin_cases i <;>
    simp [quadrangleSelected, quadranglePair, swap_apply_def, Fin.ext_iff]

def fiberPermutation {F I : Type*} (p : F → Perm I) : Perm (F × I) where
  toFun d := (d.1, p d.1 d.2)
  invFun d := (d.1, (p d.1).symm d.2)
  left_inv d := Prod.ext rfl ((p d.1).symm_apply_apply d.2)
  right_inv d := Prod.ext rfl ((p d.1).apply_symm_apply d.2)

theorem fiberPermutation_involutive {F I : Type*} (p : F → Perm I)
    (hp : ∀ f, Function.Involutive (p f)) : Function.Involutive (fiberPermutation p) := by
  intro d
  exact Prod.ext rfl (hp d.1 d.2)

theorem quadrangleSelected_iff (b : Bool) (i : Fin 4) :
    quadrangleSelected b i = true ↔
      i = (if b then 1 else 0) ∨ i = quadrangleOpposite (if b then 1 else 0) := by
  cases b <;> fin_cases i <;> simp [quadrangleSelected, quadrangleOpposite, swap_apply_def, Fin.ext_iff]

theorem quadranglePair_side_zero_one (b : Bool) :
    quadranglePair b 0 = 1 ∨ quadranglePair (!b) 0 = 1 := by
  cases b <;> simp [quadranglePair, swap_apply_def, Fin.ext_iff]

theorem quadranglePair_side_zero_three (b : Bool) :
    quadranglePair b 0 = 3 ∨ quadranglePair (!b) 0 = 3 := by
  cases b <;> simp [quadranglePair, swap_apply_def, Fin.ext_iff]

theorem quadranglePair_side_one_two (b : Bool) :
    quadranglePair b 1 = 2 ∨ quadranglePair (!b) 1 = 2 := by
  cases b <;> simp [quadranglePair, swap_apply_def, Fin.ext_iff]

end
end Erdos73
