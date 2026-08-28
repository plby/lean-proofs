import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspGeometry
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAlternating

/-!
# Native cusp coordinates in the actual glued canonical atlas

The chart of the genuine cusp piece, expressed in its original three toric
coordinates, gives a chart in the actual glued threefold atlas.  The
coordinate expression of the actual cusp inclusion is exactly the fixed
complex-linear model equivalence.  Its derivative and the pullback of the
standard top covector are computed without any replacement atlas.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open ToricCharts CuspGeometry

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace
  specialCuspPieceChartedSpace localPieceChartedSpace localPiece_nonempty

/-- The common-model chart is the native cusp chart followed by the
already constructed complex-linear model change. -/
@[simp] theorem commonChart_apply (i x : LocalSpace) :
    chartAt (ℂ × ComplexPlane₂) i x =
      cuspModelEquiv (chartAt (CoordinateSpace 3) i x) := rfl

@[simp] theorem commonChart_source (i : LocalSpace) :
    (chartAt (ℂ × ComplexPlane₂) i).source =
      (chartAt (CoordinateSpace 3) i).source :=
  ModelChange.chartAt_source cuspModelEquiv LocalSpace i

@[simp] theorem commonChart_symm_apply (i : LocalSpace) (z : ℂ × ComplexPlane₂) :
    (chartAt (ℂ × ComplexPlane₂) i).symm z =
      (chartAt (CoordinateSpace 3) i).symm (cuspModelEquiv.symm z) := rfl

@[simp] theorem commonChart_target (i : LocalSpace) :
    (chartAt (ℂ × ComplexPlane₂) i).target =
      cuspModelEquiv.symm ⁻¹' (chartAt (CoordinateSpace 3) i).target :=
  ModelChange.chartAt_target cuspModelEquiv LocalSpace i

/-- The actual glued chart indexed by a point of the full native cusp piece. -/
def gluedCuspChart (i : LocalSpace) : atlas (ℂ × ComplexPlane₂) Threefold.Space :=
  ⟨gluingData.gluedChart (some none) i,
    gluingData.gluedChart_mem_atlas (some none) i⟩

@[simp] theorem gluedCuspChart_inclusion (i x : LocalSpace) :
    (gluedCuspChart i).val (CuspGeometry.inclusion x) =
      cuspModelEquiv (chartAt (CoordinateSpace 3) i x) :=
  gluingData.gluedChart_inclusion (some none) i x

private theorem gluedChart_source_inclusion_iff (j : Index)
    (a x : gluingData.piece j) :
    gluingData.inclusion j x ∈
      (gluingData.gluedChart (E := ℂ × ComplexPlane₂) j a).source ↔
      x ∈ (chartAt (ℂ × ComplexPlane₂) a).source := by
  change gluingData.inclusion j x ∈ (gluingData.parametrization j).target ∧
    (gluingData.parametrization j).symm (gluingData.inclusion j x) ∈
      (chartAt (ℂ × ComplexPlane₂) a).source ↔ _
  rw [gluingData.parametrization_symm_inclusion, gluingData.parametrization_target]
  exact and_iff_right (mem_range_self x)

/-- Membership in the source is exactly native chart-source membership. -/
theorem inclusion_mem_gluedCuspChart_source_iff (i x : LocalSpace) :
    CuspGeometry.inclusion x ∈ (gluedCuspChart i).val.source ↔
      x ∈ (chartAt (CoordinateSpace 3) i).source := by
  have hs : x ∈ (chartAt (ℂ × ComplexPlane₂) i).source ↔
      x ∈ (chartAt (CoordinateSpace 3) i).source := by
    rw [commonChart_source]
  exact (gluedChart_source_inclusion_iff (some none) i x).trans hs

theorem inclusion_mem_gluedCuspChart_source (i x : LocalSpace)
    (hx : x ∈ (chartAt (CoordinateSpace 3) i).source) :
    CuspGeometry.inclusion x ∈ (gluedCuspChart i).val.source :=
  (inclusion_mem_gluedCuspChart_source_iff i x).mpr hx

@[simp] theorem gluedCuspChart_symm_apply (i : LocalSpace) (z : ℂ × ComplexPlane₂) :
    (gluedCuspChart i).val.symm z =
      CuspGeometry.inclusion
        ((chartAt (CoordinateSpace 3) i).symm (cuspModelEquiv.symm z)) := rfl

/-- The genuine inclusion is exactly the model equivalence in matching
native and glued coordinates near every point of the native chart target. -/
theorem gluedCuspChart_inclusionCoordinate_eventually (i : LocalSpace)
    {z : CoordinateSpace 3} (hz : z ∈ (chartAt (CoordinateSpace 3) i).target) :
    ((gluedCuspChart i).val ∘ CuspGeometry.inclusion ∘
      (chartAt (CoordinateSpace 3) i).symm) =ᶠ[𝓝 z] cuspModelEquiv := by
  filter_upwards [(chartAt (CoordinateSpace 3) i).open_target.mem_nhds hz] with w hw
  change (gluedCuspChart i).val
    (CuspGeometry.inclusion ((chartAt (CoordinateSpace 3) i).symm w)) = cuspModelEquiv w
  rw [gluedCuspChart_inclusion, (chartAt (CoordinateSpace 3) i).right_inv hw]

/-- The derivative is the exact native-to-product linear map, not only
an unspecified invertible derivative. -/
theorem gluedCuspChart_inclusion_fderiv (i : LocalSpace)
    {z : CoordinateSpace 3} (hz : z ∈ (chartAt (CoordinateSpace 3) i).target) :
    fderiv ℂ ((gluedCuspChart i).val ∘ CuspGeometry.inclusion ∘
      (chartAt (CoordinateSpace 3) i).symm) z = cuspModelEquiv.toContinuousLinearMap := by
  rw [(gluedCuspChart_inclusionCoordinate_eventually i hz).fderiv_eq]
  exact cuspModelEquiv.hasFDerivAt.fderiv

@[simp] theorem coordinateEquiv_cuspModelEquiv (x : CoordinateSpace 3) :
    TrianglePeriodFamily.Canonical.coordinateEquiv (cuspModelEquiv x) = x := by
  ext j
  fin_cases j <;> rfl

@[simp] theorem cuspModelEquiv_coordinateEquiv (x : ℂ × ComplexPlane₂) :
    cuspModelEquiv (TrianglePeriodFamily.Canonical.coordinateEquiv x) = x := by
  apply Prod.ext
  · rfl
  · ext j
    fin_cases j <;> rfl

/-- The model change pulls the product-coordinate volume back to the
original native toric volume with coefficient exactly one. -/
theorem volume_cuspModelEquiv_pullback :
    TrianglePeriodFamily.Canonical.volume.compContinuousLinearMap
      cuspModelEquiv.toContinuousLinearMap = CanonicalBundle.volume := by
  ext v
  change CanonicalBundle.volume
    (fun j => TrianglePeriodFamily.Canonical.coordinateEquiv (cuspModelEquiv (v j))) =
      CanonicalBundle.volume v
  simp only [coordinateEquiv_cuspModelEquiv]

/-- The inverse model change returns exactly the product-coordinate volume. -/
theorem volume_cuspModelEquiv_symm_pullback :
    CanonicalBundle.volume.compContinuousLinearMap
      cuspModelEquiv.symm.toContinuousLinearMap = TrianglePeriodFamily.Canonical.volume := by
  ext v
  change CanonicalBundle.volume (fun j => cuspModelEquiv.symm (v j)) =
    CanonicalBundle.volume (fun j => TrianglePeriodFamily.Canonical.coordinateEquiv (v j))
  congr 1
  funext j
  apply cuspModelEquiv.injective
  rw [cuspModelEquiv.apply_symm_apply, cuspModelEquiv_coordinateEquiv]

/-- In actual native and glued coordinates, derivative pullback of the
global product volume is precisely the native toric top covector. -/
theorem gluedCuspChart_volume_pullback (i : LocalSpace)
    {z : CoordinateSpace 3} (hz : z ∈ (chartAt (CoordinateSpace 3) i).target) :
    TrianglePeriodFamily.Canonical.volume.compContinuousLinearMap
      (fderiv ℂ ((gluedCuspChart i).val ∘ CuspGeometry.inclusion ∘
        (chartAt (CoordinateSpace 3) i).symm) z) = CanonicalBundle.volume := by
  rw [gluedCuspChart_inclusion_fderiv i hz]
  exact volume_cuspModelEquiv_pullback

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
