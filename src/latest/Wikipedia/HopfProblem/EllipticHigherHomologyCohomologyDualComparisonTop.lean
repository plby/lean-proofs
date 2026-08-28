import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariants
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualAlgebra
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDualComparisonCore

/-!
# The actual top-degree deck-comparison dual cokernel

The established positive integral markings identify the genuine covering
map from degree-four deck coinvariants with multiplication by the sheet
count.  Transporting its actual integer dual therefore gives cokernel
`ZMod j.order`.  The residue is evaluation on the marked positive
coinvariant generator; the formulas below retain that actual generator.

No covering-coordinate or cohomological comparison hypothesis is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris CohomologyDualAlgebra CohomologyDualComparison

/-- The established degree-four coinvariant marking, written as one finite coordinate. -/
def periodDeckCoinvariantsH4FunEquiv (j : Kind) (p : FixedPeriod j) :
    PeriodDeckCoinvariants j p 4 ≃ₗ[ℤ] rankOneLattice :=
  (periodDeckCoinvariantsH4Equiv j p).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm

/-- The established positive surface marking in the same finite-coordinate convention. -/
def surfaceH4FunEquiv (j : Kind) (p : FixedPeriod j) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 4 ≃ₗ[ℤ]
      rankOneLattice :=
  (surfaceH4Equiv j p).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm

@[simp] theorem periodDeckCoinvariantsH4FunEquiv_apply
    (j : Kind) (p : FixedPeriod j) (a : PeriodDeckCoinvariants j p 4) (i : Fin 1) :
    periodDeckCoinvariantsH4FunEquiv j p a i = periodDeckCoinvariantsH4Equiv j p a := rfl

@[simp] theorem periodDeckCoinvariantsH4FunEquiv_symm_apply
    (j : Kind) (p : FixedPeriod j) (x : rankOneLattice) :
    (periodDeckCoinvariantsH4FunEquiv j p).symm x =
      (periodDeckCoinvariantsH4Equiv j p).symm (x 0) := rfl

@[simp] theorem surfaceH4FunEquiv_apply (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 4) (i : Fin 1) :
    surfaceH4FunEquiv j p a i = surfaceH4Equiv j p a := rfl

@[simp] theorem surfaceH4FunEquiv_symm_apply
    (j : Kind) (p : FixedPeriod j) (x : rankOneLattice) :
    (surfaceH4FunEquiv j p).symm x = (surfaceH4Equiv j p).symm (x 0) := rfl

/-- The actual covering map conjugated by the two positive degree-four markings. -/
def periodCoverCoinvariantH4FunMap (j : Kind) (p : FixedPeriod j) :
    rankOneLattice →ₗ[ℤ] rankOneLattice :=
  (surfaceH4FunEquiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 4).comp
      (periodDeckCoinvariantsH4FunEquiv j p).symm.toLinearMap)

theorem periodCoverCoinvariantH4FunMap_coordinates
    (j : Kind) (p : FixedPeriod j) (x : rankOneLattice) :
    periodCoverCoinvariantH4FunMap j p x =
      surfaceH4FunEquiv j p (periodCoverFromDeckCoinvariants j p 4
        ((periodDeckCoinvariantsH4FunEquiv j p).symm x)) := rfl

/-- Its scalar is proved from the actual covering map, not supplied as a hypothesis. -/
@[simp] theorem periodCoverCoinvariantH4FunMap_apply
    (j : Kind) (p : FixedPeriod j) (x : rankOneLattice) :
    periodCoverCoinvariantH4FunMap j p x = j.order • x := by
  rw [periodCoverCoinvariantH4FunMap_coordinates]
  funext i
  rw [surfaceH4FunEquiv_apply, periodDeckCoinvariantsH4FunEquiv_symm_apply,
    periodCoverFromDeckCoinvariants_h4_coordinate, LinearEquiv.apply_symm_apply]
  change (j.order : ℤ) * x 0 = j.order • x i
  rw [Subsingleton.elim i 0, nsmul_eq_mul]

/-- The cokernel of the genuine dual of the top-degree deck-coinvariant comparison. -/
def periodCoverDeckDualH4CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    ((PeriodDeckCoinvariants j p 4 →ₗ[ℤ] ℤ) ⧸
      LinearMap.range (periodCoverFromDeckCoinvariants j p 4).dualMap) ≃ₗ[ℤ]
        ZMod j.order :=
  (dualCokernelEquivOfCoordinates (periodCoverFromDeckCoinvariants j p 4)
    (periodDeckCoinvariantsH4FunEquiv j p) (surfaceH4FunEquiv j p)
    (periodCoverCoinvariantH4FunMap j p)
    (periodCoverCoinvariantH4FunMap_coordinates j p)).trans
    (rankOneDualCokernelEquivZMod j.order (periodCoverCoinvariantH4FunMap j p)
      (periodCoverCoinvariantH4FunMap_apply j p))

/-- A quotient class is sent to its evaluation on the marked positive generator modulo the order. -/
@[simp] theorem periodCoverDeckDualH4CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j) (φ : PeriodDeckCoinvariants j p 4 →ₗ[ℤ] ℤ) :
    periodCoverDeckDualH4CokernelEquivZMod j p (Submodule.Quotient.mk φ) =
      (φ ((periodDeckCoinvariantsH4Equiv j p).symm 1) : ZMod j.order) := by
  change rankOneDualCokernelEquivZMod j.order (periodCoverCoinvariantH4FunMap j p)
    (periodCoverCoinvariantH4FunMap_apply j p)
      (dualCokernelEquivOfCoordinates (periodCoverFromDeckCoinvariants j p 4)
        (periodDeckCoinvariantsH4FunEquiv j p) (surfaceH4FunEquiv j p)
        (periodCoverCoinvariantH4FunMap j p)
        (periodCoverCoinvariantH4FunMap_coordinates j p)
        (Submodule.Quotient.mk φ)) = _
  rw [dualCokernelEquivOfCoordinates_apply_mk, rankOneDualCokernelEquivZMod_apply_mk]
  simp only [LinearEquiv.dualMap_apply, periodDeckCoinvariantsH4FunEquiv_symm_apply,
    Pi.single_eq_same]

/-- Multiples of the marked coordinate give explicit representatives of every residue class. -/
@[simp] theorem periodCoverDeckDualH4CokernelEquivZMod_symm_apply_intCast
    (j : Kind) (p : FixedPeriod j) (k : ℤ) :
    (periodCoverDeckDualH4CokernelEquivZMod j p).symm (k : ZMod j.order) =
      Submodule.Quotient.mk (k • (periodDeckCoinvariantsH4Equiv j p).toLinearMap) := by
  apply (periodCoverDeckDualH4CokernelEquivZMod j p).injective
  rw [LinearEquiv.apply_symm_apply, periodCoverDeckDualH4CokernelEquivZMod_apply_mk]
  simp

/-- Exact divisibility criterion for the actual top-degree dual image. -/
theorem periodCoverDeckDual_h4_mem_range_iff
    (j : Kind) (p : FixedPeriod j) (φ : PeriodDeckCoinvariants j p 4 →ₗ[ℤ] ℤ) :
    φ ∈ LinearMap.range (periodCoverFromDeckCoinvariants j p 4).dualMap ↔
      (j.order : ℤ) ∣ φ ((periodDeckCoinvariantsH4Equiv j p).symm 1) := by
  rw [← Submodule.Quotient.mk_eq_zero,
    ← (periodCoverDeckDualH4CokernelEquivZMod j p).map_eq_zero_iff,
    periodCoverDeckDualH4CokernelEquivZMod_apply_mk,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The exact additive image index of the actual top-degree dual map. -/
theorem periodCoverDeckDual_h4_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (periodCoverFromDeckCoinvariants j p 4).dualMap).toAddSubgroup.index =
      j.order := by
  rw [dualRange_index_of_coordinates (periodCoverFromDeckCoinvariants j p 4)
    (periodDeckCoinvariantsH4FunEquiv j p) (surfaceH4FunEquiv j p)
    (periodCoverCoinvariantH4FunMap j p) (periodCoverCoinvariantH4FunMap_coordinates j p)]
  exact rankOneDualMap_range_index j.order (periodCoverCoinvariantH4FunMap j p)
    (periodCoverCoinvariantH4FunMap_apply j p)

theorem periodCoverDeckDual_h4_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range
      (periodCoverFromDeckCoinvariants j p 4).dualMap).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [periodCoverDeckDual_h4_range_index]
  exact j.order_pos.ne'

end Wikipedia.HopfProblem.Elliptic.HigherHomology
