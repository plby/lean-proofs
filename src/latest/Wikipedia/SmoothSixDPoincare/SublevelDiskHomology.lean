import Wikipedia.SmoothSixDPoincare.SublevelDisk
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint
import Mathlib.Analysis.Convex.Contractible

/-!
# Actual homology vanishing for a constructed sublevel disk

Contract the genuine closed Euclidean disk and transport through the
retained homeomorphism. No homology property of the sublevel is assumed.
-/

noncomputable section

open Set Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.SublevelDisk

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M] {f : M → ℝ} {a : ℝ} {n : ℕ}
  (d : SublevelDisk n f a)

include d

theorem contractibleSpace : ContractibleSpace {x : M // f x ≤ a} := by
  let : ContractibleSpace (Hemisphere.Ball n) :=
    (convex_closedBall (0 : Hemisphere.Ambient n) 1).contractibleSpace ⟨0, by simp⟩
  exact d.homeomorph.symm.contractibleSpace

theorem homology_subsingleton (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (SingularHomology {x : M // f x ≤ a} k) := by
  let := d.contractibleSpace
  exact contractible_homology_subsingleton _ k hk

end Wikipedia.SmoothSixDPoincare.SublevelDisk
