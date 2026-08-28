import Wikipedia.HopfProblem.HigherHurewiczCubeTriangulationGeometryBoundary
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedExtensionBasic

/-!
# Images of the complete simplex boundary in a permutation cube cell

An outside simplex face maps to the original cube boundary. Every other
simplex face maps to an equality of two distinct adjacent cube coordinates.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation

open FirstHurewicz SecondHurewicz.SimplyConnected

/-- The whole simplex boundary maps to outside cube faces or internal coordinate ties. -/
theorem cubeSimplex_simplexBoundary {n : ℕ}
    (e : Equiv.Perm (Fin (n + 1))) (s : Simplex (n + 1))
    (hs : s ∈ simplexBoundary (n + 1)) :
    cubeSimplex e s ∈ Cube.boundary (Fin (n + 1)) ∨
      ∃ i j : Fin (n + 1), i ≠ j ∧ cubeSimplex e s i = cubeSimplex e s j := by
  obtain ⟨k, hk⟩ := hs
  cases k using Fin.cases with
  | zero => exact Or.inl ((cubeSimplex_mem_boundary_iff e s).mpr (Or.inl hk))
  | succ k =>
    cases k using Fin.lastCases with
    | last =>
      apply Or.inl
      apply (cubeSimplex_mem_boundary_iff e s).mpr
      exact Or.inr (by simpa only [Fin.succ_last] using hk)
    | cast i =>
      apply Or.inr
      refine ⟨e i.castSucc, e i.succ, ?_, ?_⟩
      · intro h
        have hval := congrArg Fin.val (e.injective h)
        simp only [Fin.val_castSucc, Fin.val_succ] at hval
        omega
      · apply (cubeSimplex_tie_iff e s i).mpr
        simpa only [Fin.castSucc_succ] using hk

end Wikipedia.HopfProblem.HigherHurewicz.CubeTriangulation
