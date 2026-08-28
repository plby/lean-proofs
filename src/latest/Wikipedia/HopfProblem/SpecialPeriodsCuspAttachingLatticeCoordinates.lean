import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLatticeBasic
import Wikipedia.HopfProblem.PeriodTorusFirstHomologyComparison

/-!
# Exact source lattice coordinates in the actual cusp fibre

The regular period columns are ordered `[Z | I]`, while the native cusp
torus is marked by `[I | Z]`.  Their explicit block swap preserves every
complex period vector.  Source vectors with zero cusp projection become
integer-period loops, which contract in the actual cusp piece.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open CuspFamily CuspUniformization TrianglePeriodFamily

/-- Actual period agreement identifies the native matrix with the regular
period matrix's nonconstant left block. -/
theorem nativePeriodData_matrix_eq_regular_leftBlock (s : LogBase radius) :
    (nativePeriodData s).matrix =
      (regularData.periods.point (cuspLift s)).val.leftBlock := by
  exact ((congrArg (fun p : PeriodDomain => p.val.leftBlock) (period_agreement s)).trans
    (data.point_leftBlock s)).symm

/-- Every source lattice vector gives exactly the same complex vector in
the regular and native cusp markings, with their original signs. -/
theorem native_periodVector_sourceCoordinates (s : LogBase radius) (v : Lattice) :
    (nativePeriodData s).periodVector (sourcePeriodCoordinates v) =
      regularData.periods.periodEquiv (cuspLift s) (Elliptic.realCast v) := by
  calc
    _ = (regularData.periods.point (cuspLift s)).periodVector v :=
      (regularData.periods.point (cuspLift s)).fullPeriod_periodVector
        (nativePeriodData s) (nativePeriodData_matrix_eq_regular_leftBlock s) v
    _ = _ := (regularData.periodEquiv_realCast (cuspLift s) v).symm

/-- Killing the first two source coordinates leaves precisely the two
integer periods, in the original order `(v₂,v₃)`. -/
theorem sourcePeriodCoordinates_eq_integer_of_projection_zero (v : Lattice)
    (hv : cuspLatticeProjection v = 0) :
    sourcePeriodCoordinates v = (![v 2, v 3], 0) := by
  change (![v 2, v 3], cuspLatticeProjection v) = _
  rw [hv]

/-- The actual marked loop of any source vector with zero cusp projection
is based null-homotopic in the genuine small cusp piece. -/
theorem nativeFibre_periodLoop_nullhomotopic_of_projection_zero
    (s : LogBase radius) (v : Lattice) (hv : cuspLatticeProjection v = 0) :
    Path.Homotopic
      (((nativePeriodData s).periodLoop (sourcePeriodCoordinates v)).map
        (nativeFibreMap_continuous s))
      (Path.refl (nativeFibreMap s 0)) := by
  rw [sourcePeriodCoordinates_eq_integer_of_projection_zero v hv]
  exact fibre_integerPeriod_loop_nullhomotopic data.correction radius s
    (cuspParameter_norm_lt s) (cuspParameter_log_neg s) (cuspParameter_drift_bound s)
    data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift ![v 2, v 3]

/-- Equivalently, every vector in the exact source kernel of `M₀ - 1`
has a based null-homotopic native fibre loop. -/
theorem nativeFibre_periodLoop_nullhomotopic_of_monodromy_kernel
    (s : LogBase radius) (v : Lattice) (hv : (M₀ - 1) *ᵥ v = 0) :
    Path.Homotopic
      (((nativePeriodData s).periodLoop (sourcePeriodCoordinates v)).map
        (nativeFibreMap_continuous s))
      (Path.refl (nativeFibreMap s 0)) :=
  nativeFibre_periodLoop_nullhomotopic_of_projection_zero s v
    ((cuspLatticeProjection_eq_zero_iff v).mpr hv)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
