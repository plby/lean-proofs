import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspCriticalTransport
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspDifferential
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspFibreGeometryStrata

/-!
# The exact critical locus of the global projection on the cusp patch

The actual global sphere differential vanishes precisely at the points
where at least two native cusp branches meet.  Equivalently it fails to
be surjective precisely there.  In the existing glued threefold these
points form exactly the three compact double curves, all in the literal
fibre at infinity.  Both assertions use the actual global projection,
not a replacement local function or an assumed derivative formula.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry

open ToricCharts

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] nativeChartedSpace Threefold.chartedSpace

/-- Every actual point of the full cusp piece is critical for the
global sphere map exactly when at least two central branches meet. -/
theorem projectionSphere_mfderiv_eq_zero_iff (x : LocalSpace) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x) = 0 ↔
      2 ≤ CuspQuotient.branchCount data.correction data.radius x :=
  (parameter_mfderiv_eq_zero_iff x).symm.trans
    (CuspQuotient.projection_mfderiv_eq_zero_iff_branchCount data.correction data.radius
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift x)

/-- Differential surjectivity is an exact global statement on the
entire cusp patch, including all noncentral points. -/
theorem projectionSphere_mfderiv_surjective_iff (x : LocalSpace) :
    Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x)) ↔
      CuspQuotient.branchCount data.correction data.radius x ≤ 1 :=
  (parameter_mfderiv_surjective_iff x).symm.trans
    (CuspQuotient.projection_mfderiv_surjective_iff_branchCount data.correction data.radius
      data.radius_pos data.radius_lt_one data.holomorphic data.smallDrift x)

theorem projectionSphere_mfderiv_not_surjective_iff (x : LocalSpace) :
    ¬Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x)) ↔
      2 ≤ CuspQuotient.branchCount data.correction data.radius x := by
  rw [projectionSphere_mfderiv_surjective_iff]
  omega

theorem projectionSphere_critical_iff_not_surjective (x : LocalSpace) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x) = 0 ↔
      ¬Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x)) :=
  (projectionSphere_mfderiv_eq_zero_iff x).trans
    (projectionSphere_mfderiv_not_surjective_iff x).symm

/-- A critical point anywhere on this full patch necessarily lies in
the original central fibre, hence maps to the actual sphere infinity. -/
theorem projectionSphere_eq_infty_of_critical (x : LocalSpace)
    (hx : mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (inclusion x) = 0) :
    Threefold.projectionSphere (inclusion x) = (∞ : RiemannSphere) := by
  apply (projectionSphere_inclusion_eq_infty_iff x).mpr
  apply (CuspQuotient.branchCount_pos_iff data.correction data.radius x).mp
  have hcount := (projectionSphere_mfderiv_eq_zero_iff x).mp hx
  omega

/-- On the literal infinity fibre the same criterion uses its
intrinsic branch count, defined by the proved inclusion homeomorphism. -/
theorem fibre_mfderiv_eq_zero_iff (x : sphereCuspFibre) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (x : Threefold.Space) = 0 ↔
      2 ≤ fibreBranchCount x := by
  have h := projectionSphere_mfderiv_eq_zero_iff
    (centralFibreHomeomorph.symm x : LocalSpace)
  rw [centralFibreHomeomorph_symm_inclusion] at h
  exact h

theorem fibre_mfderiv_surjective_iff (x : sphereCuspFibre) :
    Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (x : Threefold.Space)) ↔
      fibreBranchCount x = 1 := by
  have h := projectionSphere_mfderiv_surjective_iff
    (centralFibreHomeomorph.symm x : LocalSpace)
  rw [centralFibreHomeomorph_symm_inclusion] at h
  have hp := fibreBranchCount_pos x
  exact h.trans (by change fibreBranchCount x ≤ 1 ↔ fibreBranchCount x = 1; omega)

theorem fibre_critical_iff_mem_doubleStratum (x : sphereCuspFibre) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere (x : Threefold.Space) = 0 ↔
      (x : Threefold.Space) ∈ doubleStratum :=
  (fibre_mfderiv_eq_zero_iff x).trans (mem_doubleStratum_iff x).symm

/-- The literal critical subset of the actual global cusp patch. -/
def cuspCriticalLocus : Set Threefold.Space :=
  {y | y ∈ Threefold.liftedPatch (some none) ∧
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0}

/-- No additional critical points arise from gluing or changing from
the toric parameter to the actual sphere coordinate. -/
theorem cuspCriticalLocus_eq_doubleStratum : cuspCriticalLocus = doubleStratum := by
  ext y
  constructor
  · rintro ⟨hy, hcritical⟩
    have himage : y ∈ range inclusion := by
      rw [inclusion_range]
      exact hy
    obtain ⟨x, rfl⟩ := himage
    exact ⟨x, (projectionSphere_mfderiv_eq_zero_iff x).mp hcritical, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(nativePatchBiholomorph x).property,
      (projectionSphere_mfderiv_eq_zero_iff x).mpr hx⟩

theorem cuspCriticalLocus_eq_doubleCurves :
    cuspCriticalLocus = ⋃ i : Fin 3, doubleCurve i := by
  rw [cuspCriticalLocus_eq_doubleStratum, doubleStratum_eq_union]

theorem cuspCriticalLocus_compact : IsCompact cuspCriticalLocus := by
  rw [cuspCriticalLocus_eq_doubleStratum]
  exact doubleStratum_compact

theorem cuspCriticalLocus_isClosed : IsClosed cuspCriticalLocus := by
  rw [cuspCriticalLocus_eq_doubleStratum]
  exact doubleStratum_isClosed

theorem cuspCriticalLocus_subset_sphereCuspFibre : cuspCriticalLocus ⊆ sphereCuspFibre := by
  rw [cuspCriticalLocus_eq_doubleStratum]
  exact doubleStratum_subset_sphereCuspFibre

/-- The actual critical locus restricted to the literal infinity fibre
is the same union of three compact double curves. -/
theorem sphereCuspFibre_critical_eq_doubleStratum :
    {y : Threefold.Space | Threefold.projectionSphere y = (∞ : RiemannSphere) ∧
      mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0} = doubleStratum := by
  ext y
  constructor
  · rintro ⟨hy, hcritical⟩
    exact (fibre_critical_iff_mem_doubleStratum ⟨y, hy⟩).mp hcritical
  · intro hy
    have hcentral := doubleStratum_subset_sphereCuspFibre hy
    exact ⟨hcentral, (fibre_critical_iff_mem_doubleStratum ⟨y, hcentral⟩).mpr hy⟩

/-- The critical value set of the full actual cusp patch is exactly
the original marked sphere infinity, not merely a subset of it. -/
theorem projectionSphere_image_cuspCriticalLocus :
    Threefold.projectionSphere '' cuspCriticalLocus = {(∞ : RiemannSphere)} := by
  ext b
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact cuspCriticalLocus_subset_sphereCuspFibre hy
  · intro hb
    have hcrit : lowerTriplePoint ∈ cuspCriticalLocus := by
      rw [cuspCriticalLocus_eq_doubleCurves]
      exact mem_iUnion.mpr ⟨0, lowerTriplePoint_mem_doubleCurve 0⟩
    exact ⟨lowerTriplePoint, hcrit, lowerTriplePoint_mem_sphereCuspFibre.trans hb.symm⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspGeometry
