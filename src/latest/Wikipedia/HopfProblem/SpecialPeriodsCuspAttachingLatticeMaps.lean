import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLatticeBasic

/-!
# Actual source-marked lattice loops in the constructed threefold

The regular fibre loops are the source-column straight loops in the
fixed real coordinate torus.  The native cusp loops use the explicit
`[Z | I]` to `[I | Z]` shuffle.  Both are included into the unchanged
constructed threefold by its actual gluing maps.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching

open TrianglePeriodFamily CuspFamily CuspUniformization

/-- The actual regular-family inclusion, bundled as a continuous map. -/
def regularFamilyInclusionMap : C(SpecialRegularFamily, Space) :=
  ⟨inclusion none, (inclusion_openEmbedding none).continuous⟩

/-- The source-column lattice map followed by the actual regular inclusion. -/
def globalLatticeHom (b : TriangleRegularPoint) : Multiplicative Lattice →*
    FundamentalGroup Space (inclusion none (regularData.fundamentalGroupBasepoint b)) :=
  (FundamentalGroup.map regularFamilyInclusionMap (regularData.fundamentalGroupBasepoint b)).comp
    (regularData.latticeFundamentalGroupHom b)

/-- The fixed real torus is included into the actual quotient family. -/
def regularFibreMap (b : TriangleRegularPoint) : C(RealTorus₄, SpecialRegularFamily) :=
  ⟨fun x => regularData.quotient (b, x),
    regularData.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- The actual straight source-column loop in the regular family. -/
def regularLatticeLoop (b : TriangleRegularPoint) (v : Lattice) :
    Path (regularData.fundamentalGroupBasepoint b) (regularData.fundamentalGroupBasepoint b) :=
  (FlatTorus.periodLoop v).map (regularFibreMap b).continuous

/-- The same actual marked loop included in the threefold. -/
def globalLatticeLoop (b : TriangleRegularPoint) (v : Lattice) :
    Path (inclusion none (regularData.fundamentalGroupBasepoint b))
      (inclusion none (regularData.fundamentalGroupBasepoint b)) :=
  (regularLatticeLoop b v).map regularFamilyInclusionMap.continuous

theorem globalLatticeLoop_apply (b : TriangleRegularPoint) (v : Lattice) (t : I) :
    globalLatticeLoop b v t = inclusion none
      (regularData.quotient (b, standardLattice.mkQ ((t : ℝ) • Elliptic.realCast v))) :=
  congrArg (fun x : RealTorus₄ => inclusion none (regularData.quotient (b, x)))
    (FlatTorus.periodLoop_apply v t)

/-- The lattice homomorphism is represented by this literal straight loop. -/
theorem globalLatticeHom_periodLoop (b : TriangleRegularPoint) (v : Lattice) :
    globalLatticeHom b (Multiplicative.ofAdd v) =
      Path.Homotopic.Quotient.mk (globalLatticeLoop b v) := by
  change FundamentalGroup.map regularFamilyInclusionMap (regularData.fundamentalGroupBasepoint b)
    (regularData.latticeFundamentalGroupHom b (Multiplicative.ofAdd v)) = _
  rw [regularData.latticeFundamentalGroupHom_periodLoop]
  rfl

/-- The native full-period loop in the cusp filling, with the exact source shuffle. -/
def nativeGlobalPeriodLoop (s : LogBase radius) (v : Lattice) :
    Path (inclusion (some none) (nativeFibreMap s 0))
      (inclusion (some none) (nativeFibreMap s 0)) :=
  (((nativePeriodData s).periodLoop (sourcePeriodCoordinates v)).map
    (nativeFibreMap_continuous s)).map (inclusion_openEmbedding (some none)).continuous

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspAttaching
