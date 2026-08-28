import Mathlib.Data.Fin.SuccPred
import Lean.Elab.Tactic.Omega

/-!
# Coordinate thresholds for an inserted shuffle step

Duplicating the prism vertex at `k` is dual to inserting a coordinate
switch at `k`. This elementary inequality is valid also at both endpoints.
-/

namespace Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision

theorem lt_predAbove_iff_succAbove_lt {n : ℕ} (k : Fin (n + 1))
    (j : Fin n) (r : Fin (n + 2)) :
    j.val < (k.predAbove r).val ↔ (k.succAbove j).val < r.val := by
  simp only [Fin.succAbove, Fin.predAbove, Fin.lt_def, Fin.val_castSucc,
    apply_dite Fin.val, Fin.val_pred, Fin.coe_castPred, dite_eq_ite,
    apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

end Wikipedia.HopfProblem.FourthHurewicz.CubeSubdivision
