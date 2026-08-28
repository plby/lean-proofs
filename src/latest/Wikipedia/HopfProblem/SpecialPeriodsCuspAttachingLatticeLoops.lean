import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLatticeMaps
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLatticeCoordinates
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLatticeOverlap

/-!
# The same marked loops on both sides of the actual cusp attachment

The full-vector overlap formula identifies the native exponential loop
with the regular source-column loop point by point.  The only endpoint
cast is the equality of their images under the genuine gluing maps.
Consequently the two integer cusp periods die in the constructed space.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open TrianglePeriodFamily CuspFamily CuspUniformization

theorem nativeGlobalPeriodLoop_apply (s : LogBase radius) (v : Lattice) (t : I) :
    nativeGlobalPeriodLoop s v t = inclusion (some none)
      (fibreCover data.correction radius s (cuspParameter_norm_lt s)
        ((t : ℝ) • (nativePeriodData s).periodVector (sourcePeriodCoordinates v))) := by
  exact (congrArg (fun x : (nativePeriodData s).Torus =>
      inclusion (some none) (nativeFibreMap s x))
      ((nativePeriodData s).periodLoop_apply (sourcePeriodCoordinates v) t)).trans
    (congrArg (inclusion (some none)) (nativeFibreMap_mkQ s _))

/-- The original regular quotient retains the source real coordinates of
every point of the native marked straight path. -/
theorem quotientMap_nativePeriodVector (s : LogBase radius) (v : Lattice) (t : I) :
    regularData.periods.quotientMap
        (cuspLift s, (t : ℝ) • (nativePeriodData s).periodVector (sourcePeriodCoordinates v)) =
      (cuspLift s, standardLattice.mkQ ((t : ℝ) • Elliptic.realCast v)) := by
  have hs : (t : ℝ) • (nativePeriodData s).periodVector (sourcePeriodCoordinates v) =
      regularData.periods.periodEquiv (cuspLift s) ((t : ℝ) • Elliptic.realCast v) :=
    (congrArg (fun z : ComplexPlane₂ => (t : ℝ) • z)
      (native_periodVector_sourceCoordinates s v)).trans
        ((regularData.periods.periodEquiv (cuspLift s)).map_smul (t : ℝ)
          (Elliptic.realCast v)).symm
  change (cuspLift s, standardLattice.mkQ
    ((regularData.periods.periodEquiv (cuspLift s)).symm
      ((t : ℝ) • (nativePeriodData s).periodVector (sourcePeriodCoordinates v)))) = _
  apply congrArg (fun x : RealTorus₄ => (cuspLift s, x))
  apply congrArg standardLattice.mkQ
  exact (congrArg (regularData.periods.periodEquiv (cuspLift s)).symm hs).trans
    ((regularData.periods.periodEquiv (cuspLift s)).symm_apply_apply _)

/-- The actual two marked loops agree after the equality of their global
basepoints, with the original source signs and column order unchanged. -/
theorem nativeGlobalPeriodLoop_cast (s : LogBase radius) (v : Lattice) :
    (nativeGlobalPeriodLoop s v).cast
        (inclusion_nativeFibreMap_zero s).symm (inclusion_nativeFibreMap_zero s).symm =
      globalLatticeLoop (cuspLift s) v := by
  apply Path.ext
  funext t
  change nativeGlobalPeriodLoop s v t = globalLatticeLoop (cuspLift s) v t
  exact (nativeGlobalPeriodLoop_apply s v t).trans
    ((inclusion_fibreCover s _).trans
      ((congrArg (fun x => inclusion none (regularData.quotient x))
        (quotientMap_nativePeriodVector s v t)).trans
          (globalLatticeLoop_apply (cuspLift s) v t).symm))

/-- The cusp filling supplies a based contraction of the literal global
source loop whenever its two logarithmic cusp periods vanish. -/
theorem globalLatticeLoop_nullhomotopic_at_cusp (s : LogBase radius) (v : Lattice)
    (hv : cuspLatticeProjection v = 0) :
    Path.Homotopic (globalLatticeLoop (cuspLift s) v)
      (Path.refl (inclusion none (regularData.fundamentalGroupBasepoint (cuspLift s)))) := by
  have h := (nativeFibre_periodLoop_nullhomotopic_of_projection_zero s v hv).map
    (⟨inclusion (some none), (inclusion_openEmbedding (some none)).continuous⟩ :
      C(SpecialCuspPiece, Space))
  change Path.Homotopic (nativeGlobalPeriodLoop s v)
    (Path.refl (inclusion (some none) (nativeFibreMap s 0))) at h
  have hc := h.pathCast (inclusion_nativeFibreMap_zero s).symm
    (inclusion_nativeFibreMap_zero s).symm
  have hr : (Path.refl (inclusion (some none) (nativeFibreMap s 0))).cast
        (inclusion_nativeFibreMap_zero s).symm (inclusion_nativeFibreMap_zero s).symm =
      Path.refl (inclusion none (regularData.fundamentalGroupBasepoint (cuspLift s))) := by
    apply Path.ext
    funext _
    exact inclusion_nativeFibreMap_zero s
  rw [nativeGlobalPeriodLoop_cast, hr] at hc
  exact hc

/-- The rank-two source cusp-toric kernel is killed by the genuine
regular-family inclusion, at every actual logarithmic cusp lift. -/
theorem globalLatticeHom_eq_one_at_cusp (s : LogBase radius) (v : Lattice)
    (hv : cuspLatticeProjection v = 0) :
    globalLatticeHom (cuspLift s) (Multiplicative.ofAdd v) = 1 := by
  rw [globalLatticeHom_periodLoop]
  exact Quotient.sound (globalLatticeLoop_nullhomotopic_at_cusp s v hv)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
