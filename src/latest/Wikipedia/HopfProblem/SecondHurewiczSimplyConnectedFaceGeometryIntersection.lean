import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedFaceGeometry
import Wikipedia.HopfProblem.PeriodTorusLineBundleChernCocycleFaces

/-!
# Intersections of actual barycentric faces

An equality in the intersection of two distinct geometric faces comes
from their common lower-dimensional face. This identifies geometric
overlap compatibility with the usual ordered coface compatibility.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz

/-- Two points of ordered faces with the same image arise from their
common barycentric face. -/
theorem simplexFace_intersection {n : ℕ} {i j : Fin (n + 2)} (hij : i ≤ j)
    {s t : Simplex (n + 1)}
    (h : simplexFace (n + 1) j.succ s = simplexFace (n + 1) i.castSucc t) :
    ∃ u : Simplex n, simplexFace n i u = s ∧ simplexFace n j u = t := by
  have hs : s i = 0 := by
    calc
      s i = simplexFace (n + 1) j.succ s (j.succ.succAbove i) :=
        (simplexFace_apply_succAbove (n + 1) j.succ s i).symm
      _ = simplexFace (n + 1) j.succ s i.castSucc := by
        rw [Fin.succAbove_succ_of_le j i hij]
      _ = simplexFace (n + 1) i.castSucc t i.castSucc :=
        congrArg (fun v : Simplex (n + 2) => v i.castSucc) h
      _ = 0 := simplexFace_apply_self (n + 1) i.castSucc t
  let u := simplexFaceInverse n i ⟨s, hs⟩
  have hu : simplexFace n i u = s := simplexFace_inverse n i ⟨s, hs⟩
  refine ⟨u, hu, simplexFace_injective (n + 1) i.castSucc ?_⟩
  calc
    simplexFace (n + 1) i.castSucc (simplexFace n j u) =
        simplexFace (n + 1) j.succ (simplexFace n i u) :=
      (congrArg (fun f : C(Simplex n, Simplex (n + 2)) => f u)
        (PeriodTorusLineBundle.ChernCocycle.simplexFace_comp hij)).symm
    _ = simplexFace (n + 1) j.succ s := congrArg (simplexFace (n + 1) j.succ) hu
    _ = simplexFace (n + 1) i.castSucc t := h

/-- The common lower-dimensional face point is unique. -/
theorem simplexFace_intersection_unique {n : ℕ} {i j : Fin (n + 2)} (hij : i ≤ j)
    {s t : Simplex (n + 1)}
    (h : simplexFace (n + 1) j.succ s = simplexFace (n + 1) i.castSucc t) :
    ∃! u : Simplex n, simplexFace n i u = s ∧ simplexFace n j u = t := by
  obtain ⟨u, hu, hv⟩ := simplexFace_intersection hij h
  exact ⟨u, ⟨hu, hv⟩, fun v hv => simplexFace_injective n i (hv.1.trans hu.symm)⟩

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
