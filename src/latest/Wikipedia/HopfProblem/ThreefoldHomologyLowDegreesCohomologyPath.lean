import Wikipedia.HopfProblem.FirstHurewiczPathChains
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationClosed

/-!
# Evaluation of closed integral one-cochains on actual paths

The explicit singular two-chains for path homotopies, concatenations and
constant paths imply the corresponding identities for any closed integral
functional on singular one-chains. These identities do not require a
homology comparison theorem or any assumption on the space.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldCohomologyPath

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]
    (φ : Chains X 1 →ₗ[ℤ] ℤ)
    (hφ : SingularCohomologyFree.IsClosedFunctional (singularComplex X) 1 φ)
    {x y z : X}

include hφ

/-- Closed integral one-cochains have the same value on endpoint-homotopic paths. -/
theorem closed_path_homotopic {p q : Path x y} (h : Path.Homotopic p q) :
    φ (pathChain p) = φ (pathChain q) := by
  obtain ⟨H⟩ := h
  have hb : φ (boundaryTwo X (correctedHomotopyChain H)) = 0 := hφ _
  rw [boundaryTwo_correctedHomotopyChain, map_sub, sub_eq_zero] at hb
  exact hb

/-- A closed integral one-cochain evaluates additively under path concatenation. -/
theorem closed_path_trans (p : Path x y) (q : Path y z) :
    φ (pathChain (p.trans q)) = φ (pathChain p) + φ (pathChain q) := by
  have hb : φ (boundaryTwo X (concatChain p q)) = 0 := hφ _
  rw [boundaryTwo_concatChain, map_add, map_sub] at hb
  apply sub_eq_zero.mp
  calc
    φ (pathChain (p.trans q)) - (φ (pathChain p) + φ (pathChain q)) =
        -(φ (pathChain q) - φ (pathChain (p.trans q)) + φ (pathChain p)) := by abel
    _ = 0 := by rw [hb, neg_zero]

/-- A constant path is the boundary of a constant singular triangle, hence
every closed integral one-cochain evaluates to zero on it. -/
theorem closed_path_refl (x : X) : φ (pathChain (Path.refl x)) = 0 := by
  have hb : φ (boundaryTwo X (constantTriangleChain x)) = 0 := hφ _
  rwa [boundaryTwo_constantTriangleChain, ← pathChain_refl] at hb

end Wikipedia.HopfProblem.ThreefoldCohomologyPath
