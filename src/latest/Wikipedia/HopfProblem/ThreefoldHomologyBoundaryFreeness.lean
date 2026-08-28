import Wikipedia.HopfProblem.ThreefoldHomologyCuspKernel
import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibreKernel
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessPieces
import Wikipedia.HopfProblem.ThreefoldHomologyFreeProducts
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Integral freeness of every original positive-degree boundary group

The actual cap projection and actual Wang boundary jointly detect a
class, for the original cusp as well as both original elliptic fillings.
Their targets are the proved free homology groups of the full cap and
the genuine fibre four-torus. The resulting injection proves integral
torsion-freeness. Actual finite generation then gives freeness over the
integers, with no choice of a boundary marking or additional hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFreeness

open SingularMayerVietoris MappingTorusHomology PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus ThreefoldHomologyFreeProducts Finiteness

/-- The genuine homology of each of the three full filling pieces is free. -/
theorem fillingHomology_free (i : Puncture) (n : ℕ) :
    Module.Free ℤ (SingularHomology (localPiece (some i)) n) := by
  cases i with
  | none => exact cuspPieceHomology_free n
  | some j => exact ellipticPieceHomology_free j n

/-- Jointly record the two original homology maps, with their original codomains. -/
def capWangMap (i : Puncture) (n : ℕ) :
    SingularHomology (Boundary i) (n + 1) →ₗ[ℤ]
      (SingularHomology (localPiece (some i)) (n + 1) × SingularHomology RealTorus₄ n) :=
  intLinearMapOfAddHom ((boundaryFillingHomologyMap i (n + 1)).toAddMonoidHom.prod
    (wangBoundary (monodromy i) n).toAddMonoidHom)

@[simp] theorem capWangMap_apply (i : Puncture) (n : ℕ)
    (a : SingularHomology (Boundary i) (n + 1)) :
    capWangMap i n a =
      (boundaryFillingHomologyMap i (n + 1) a, wangBoundary (monodromy i) n a) := rfl

/-- Both actual maps together are injective for each original boundary, in every positive degree. -/
theorem capWangMap_injective (i : Puncture) (n : ℕ) :
    Function.Injective (capWangMap i n) := by
  cases i with
  | none => exact ThreefoldHomologyCuspFibre.cuspCap_wang_joint_injective n
  | some j => exact EllipticFibre.boundaryFilling_wang_injective j n

/-- The full original positive-degree boundary homology has no integral torsion. -/
theorem boundaryHomology_positive_torsionFree (i : Puncture) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (Boundary i) (n + 1)) := by
  have := fillingHomology_free i (n + 1)
  have := realTorus_homology_free n
  have := free_prod_int
    (SingularHomology (localPiece (some i)) (n + 1)) (SingularHomology RealTorus₄ n)
  exact Function.Injective.moduleIsTorsionFree
    (capWangMap i n) (capWangMap_injective i n) (fun r a => (capWangMap i n).map_smul r a)

theorem boundaryHomology_positive_free (i : Puncture) (n : ℕ) :
    Module.Free ℤ (SingularHomology (Boundary i) (n + 1)) := by
  have := boundaryHomology_positive_torsionFree i n
  have := ThreefoldHomologyFinitenessMappingTorus.homology_finite (monodromy i) (n + 1)
  infer_instance

/-- Transport through the actual overlap homotopy equivalence preserves integral freeness. -/
theorem overlapHomology_positive_free (i : Puncture) (n : ℕ) :
    Module.Free ℤ (SingularHomology (RegularOverlap i) (n + 1)) := by
  have := boundaryHomology_positive_free i n
  exact Module.Free.of_equiv (overlapHomologyEquiv i (n + 1)).symm

theorem overlapHomology_positive_torsionFree (i : Puncture) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (RegularOverlap i) (n + 1)) := by
  have := overlapHomology_positive_free i n
  infer_instance

/-- The original star-sequence overlap product is free in every positive degree. -/
theorem starOverlapHomology_positive_free (n : ℕ) :
    Module.Free ℤ (StarOverlapHomology (n + 1)) := by
  have (i : Puncture) := overlapHomology_positive_free i n
  exact free_pi_int (fun i : Puncture => SingularHomology (RegularOverlap i) (n + 1))

theorem starOverlapHomology_positive_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (StarOverlapHomology (n + 1)) := by
  have := starOverlapHomology_positive_free n
  infer_instance

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.BoundaryFreeness
