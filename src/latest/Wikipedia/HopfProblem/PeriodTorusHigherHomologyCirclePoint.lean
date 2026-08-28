import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Topology.Homotopy.Contractible

/-!
# Actual singular homology of points and contractible spaces

The degree-zero equivalence is Mathlib's actual augmentation map. The
higher-degree vanishing follows first from the actual alternating chain
complex of a point and then from actual singular homotopy invariance.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris
open scoped ContinuousMap

/-- The actual augmentation identifies degree-zero homology of a
path-connected space with the integral coefficient module. -/
def connectedHomologyZeroEquiv (X : Type) [TopologicalSpace X] [PathConnectedSpace X] :
    SingularHomology X 0 ≃ₗ[ℤ] ℤ :=
  (asIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ))).toLinearEquiv

@[simp] theorem connectedHomologyZeroEquiv_toLinearMap (X : Type)
    [TopologicalSpace X] [PathConnectedSpace X] :
    (connectedHomologyZeroEquiv X).toLinearMap =
      ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)).hom := rfl

/-- Actual positive-degree integral singular homology of a totally
disconnected space is the zero object. -/
theorem totallyDisconnected_homology_isZero (X : Type) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularHomology X n) :=
  AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat ℤ) n (ModuleCat.of ℤ ℤ) (TopCat.of X) hn

theorem totallyDisconnected_homology_subsingleton (X : Type) [TopologicalSpace X]
    [TotallyDisconnectedSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularHomology X n) :=
  ModuleCat.subsingleton_of_isZero (totallyDisconnected_homology_isZero X n hn)

/-- The actual degree-zero homology equivalence for a point. -/
abbrev pointHomologyZeroEquiv : SingularHomology Unit 0 ≃ₗ[ℤ] ℤ :=
  connectedHomologyZeroEquiv Unit

/-- Actual positive-degree singular homology of a point vanishes. -/
theorem point_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularHomology Unit n) :=
  totallyDisconnected_homology_subsingleton Unit n hn

/-- A contractible space has the actual singular homology of a point,
via a genuine homotopy equivalence. -/
def contractibleHomologyEquivPoint (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) :
    SingularHomology X n ≃ₗ[ℤ] SingularHomology Unit n :=
  homotopyEquivHomologyEquiv (Classical.choice (ContractibleSpace.hequiv_unit X)) n

/-- Actual positive-degree integral singular homology of a contractible
space vanishes, without assuming homology invariance as a hypothesis. -/
theorem contractible_homology_subsingleton (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularHomology X n) := by
  let := point_homology_subsingleton n hn
  exact (contractibleHomologyEquivPoint X n).injective.subsingleton

theorem contractible_homology_isZero (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (SingularHomology X n) := by
  let := contractible_homology_subsingleton X n hn
  exact ModuleCat.isZero_of_subsingleton _

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
