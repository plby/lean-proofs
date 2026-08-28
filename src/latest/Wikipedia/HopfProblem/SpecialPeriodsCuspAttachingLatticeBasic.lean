import Wikipedia.HopfProblem.SpecialPeriodsCuspAttaching
import Wikipedia.HopfProblem.TrianglePeriodFamilyFundamentalGroupData
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMarking
import Wikipedia.HopfProblem.CuspFibreFundamentalGroup

/-!
# The actual marked fibre above a logarithmic cusp basepoint

The source period coordinates and the native cusp-period coordinates are
kept separate.  All radii, period points, and small-drift estimates are
the already constructed ones used in the genuine cusp attachment.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open CuspFamily CuspUniformization TrianglePeriodFamily ToricCharts ToricSpace

/-- A genuine regular upper-half-plane representative in the small cusp patch. -/
abbrev cuspLift (s : LogBase radius) : TriangleRegularPoint :=
  logBaseToRegular radius radius_le_cuspChart s

theorem cuspParameter_norm_lt (s : LogBase radius) : ‖exponential s‖ < radius :=
  (mem_logBase radius s).mp s.property

theorem cuspParameter_log_neg (s : LogBase radius) : Real.log ‖exponential s‖ < 0 :=
  Real.log_neg (norm_pos_iff.mpr (exponential_ne_zero s))
    ((cuspParameter_norm_lt s).trans data.radius_lt_one)

theorem cuspParameter_drift_bound (s : LogBase radius) :
    ToricSpace.entryNorm (driftMatrix data.correction (exponential s)) ≤
      -Real.log ‖exponential s‖ / 4 :=
  data.smallDrift _ (norm_pos_iff.mpr (exponential_ne_zero s)) (cuspParameter_norm_lt s)

/-- The actual native full-period torus at this nonzero cusp parameter. -/
abbrev nativePeriodData (s : LogBase radius) : FullPeriodMatrix :=
  periodData data.correction s (cuspParameter_log_neg s) (cuspParameter_drift_bound s)

/-- The actual exponential inclusion of this native period torus into the small cusp piece. -/
def nativeFibreMap (s : LogBase radius) : (nativePeriodData s).Torus → SpecialCuspPiece :=
  fibreMap data.correction radius s (cuspParameter_norm_lt s)
    (cuspParameter_log_neg s) (cuspParameter_drift_bound s)

theorem nativeFibreMap_continuous (s : LogBase radius) : Continuous (nativeFibreMap s) :=
  fibreMap_continuous data.correction radius s (cuspParameter_norm_lt s)
    (cuspParameter_log_neg s) (cuspParameter_drift_bound s)

@[simp] theorem nativeFibreMap_mkQ (s : LogBase radius) (z : ComplexPlane₂) :
    nativeFibreMap s ((nativePeriodData s).lattice.mkQ z) =
      fibreCover data.correction radius s (cuspParameter_norm_lt s) z := rfl

/-- The fixed-base logarithmic lift of an arbitrary complex fibre vector. -/
def logVector (s : LogBase radius) (z : ComplexPlane₂) : LogCover radius :=
  ⟨((s : ℂ), z), s.property⟩

@[simp] theorem totalCuspCover_logVector (s : LogBase radius) (z : ComplexPlane₂) :
    totalCuspCover data.correction radius (logVector s z) =
      fibreCover data.correction radius s (cuspParameter_norm_lt s) z := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
