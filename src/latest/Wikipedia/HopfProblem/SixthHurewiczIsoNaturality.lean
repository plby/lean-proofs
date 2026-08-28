import Wikipedia.HopfProblem.SixthHurewiczIso
import Wikipedia.HopfProblem.SixthHurewiczNaturality

/-!
# Naturality of the actual sixth Hurewicz equivalence and its constructed inverse

The forward square is the naturality of the original cubical map. Its
proved injectivity gives the inverse square, so the chosen geometric
normalization does not introduce a dependence on choices at homology
level.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
variable (f : C(X, Y)) (x : X)
  [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]
  [Subsingleton (π_ 2 Y (f x))] [Subsingleton (π_ 3 Y (f x))]
  [Subsingleton (π_ 4 Y (f x))] [Subsingleton (π_ 5 Y (f x))]

/-- Naturality retains the original native homotopy and actual singular homology maps. -/
theorem hurewiczLinearEquiv_natural (a : Additive (π_ 6 X x)) :
    singularHomologyMap f 6 (hurewiczLinearEquiv x a) =
      hurewiczLinearEquiv (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczMap_natural f x a

/-- The actual descended inverse commutes with the original induced maps. -/
theorem hurewiczInverse_natural (c : SingularHomology X 6) :
    (homotopyMap f x).toAdditive (hurewiczInverse x c) =
      hurewiczInverse (f x) (singularHomologyMap f 6 c) := by
  apply hurewiczMap_injective (f x)
  simpa only [hurewiczMap_hurewiczInverse] using
    (hurewiczMap_natural f x (hurewiczInverse x c)).symm

/-- Naturality of the inverse equivalence is the literal constructed inverse square. -/
theorem hurewiczLinearEquiv_symm_natural (c : SingularHomology X 6) :
    (homotopyMap f x).toAdditive ((hurewiczLinearEquiv x).symm c) =
      (hurewiczLinearEquiv (f x)).symm (singularHomologyMap f 6 c) :=
  hurewiczInverse_natural f x c

end Wikipedia.HopfProblem.SixthHurewicz
