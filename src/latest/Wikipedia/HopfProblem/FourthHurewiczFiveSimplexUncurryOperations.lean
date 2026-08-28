import Wikipedia.HopfProblem.FourthHurewiczFiveSimplexUncurryBasic

/-!
# Native coordinate operations commute with uncurrying

Uncurrying puts the innermost loop coordinate first and shifts every
outer coordinate by one. Concatenation and reversal therefore commute
with uncurrying as literal equalities of generalized loops, before
passing to any homotopy quotient.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

variable {n : ℕ} {X : Type*} [TopologicalSpace X] {x : X}

/-- Updating an outer coordinate commutes with deleting the leading coordinate. -/
theorem uncurryTail_update_succ (u : Fin (n + 1) → I) (i : Fin n) (t : I) :
    (fun j : Fin n => Function.update u i.succ t j.succ) =
      Function.update (fun j : Fin n => u j.succ) i t := by
  funext j
  simp only [Function.update_apply, Fin.succ_inj]

/-- Updating a shifted outer coordinate leaves the leading coordinate unchanged. -/
@[simp] theorem uncurryHead_update_succ (u : Fin (n + 1) → I) (i : Fin n) (t : I) :
    Function.update u i.succ t 0 = u 0 := by
  simp only [Function.update_apply, (Fin.succ_ne_zero i).symm, if_false]

/-- Native concatenation in an outer coordinate becomes concatenation in its successor. -/
theorem uncurryLoop_transAt (i : Fin n)
    (p q : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.transAt i p q) =
      GenLoop.transAt i.succ (uncurryLoop p) (uncurryLoop q) := by
  apply GenLoop.ext
  intro u
  change ((if (u i.succ : ℝ) ≤ 1 / 2 then _ else _) : GenLoop (Fin 1) X x)
      (fun _ => u 0) =
    if (u i.succ : ℝ) ≤ 1 / 2 then _ else _
  split_ifs <;>
    simp only [uncurryLoop_apply, uncurryTail_update_succ, uncurryHead_update_succ]

/-- Native reversal in an outer coordinate becomes reversal in its successor. -/
theorem uncurryLoop_symmAt (i : Fin n)
    (p : GenLoop (Fin n) (GenLoop (Fin 1) X x) GenLoop.const) :
    uncurryLoop (GenLoop.symmAt i p) = GenLoop.symmAt i.succ (uncurryLoop p) := by
  apply GenLoop.ext
  intro u
  change p (fun j => if j = i then σ (u i.succ) else u j.succ) (fun _ => u 0) =
    p (fun j => if j.succ = i.succ then σ (u i.succ) else u j.succ)
      (fun _ => if (0 : Fin (n + 1)) = i.succ then σ (u i.succ) else u 0)
  simp only [Fin.succ_inj, (Fin.succ_ne_zero i).symm, if_false]

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
