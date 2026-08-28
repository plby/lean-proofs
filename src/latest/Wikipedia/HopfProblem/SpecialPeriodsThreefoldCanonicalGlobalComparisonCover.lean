import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalFiniteRegularSectionGeometry
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalPrescribedDivisorOrders

/-!
# The actual three-open cover for the canonical comparison

The generic divisor open, the full second elliptic patch, and the full
cusp patch cover the original compact threefold.  The two filling patches
are disjoint; each meets the generic open only in the genuine regular
locus.  These facts are derived from the original disjoint base filling
discs and the actual sphere projection.
-/

noncomputable section

open Set Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison

attribute [local instance] Threefold.chartedSpace CuspGeometry.nativeChartedSpace

inductive Patch where
  | generic
  | elliptic
  | cusp
  deriving DecidableEq

/-- All three opens retain their original subspace topologies and atlases. -/
def cover : Patch → TopologicalSpace.Opens Threefold.Space
  | .generic => GlobalFiniteRegularSection.domain
  | .elliptic => GlobalEllipticDivisor.patch
  | .cusp => Threefold.liftedPatch (some none)

theorem generic_dense : Dense (cover .generic : Set Threefold.Space) :=
  GlobalPrescribedDivisor.genericSet_dense

theorem point_over_infty_mem_cusp {y : Threefold.Space}
    (hy : Threefold.projectionSphere y = (∞ : RiemannSphere)) : y ∈ cover .cusp := by
  obtain ⟨x, _, rfl⟩ := CuspGeometry.exists_cusp_representative_of_projectionSphere_eq_infty y hy
  exact (CuspGeometry.nativePatchBiholomorph x).property

theorem point_over_one_mem_elliptic {y : Threefold.Space}
    (hy : Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere)) :
    y ∈ cover .elliptic := GlobalEllipticDivisor.support_subset_patch hy

/-- No point of the actual threefold is omitted by the comparison cover. -/
theorem exists_cover (y : Threefold.Space) : ∃ i : Patch, y ∈ cover i := by
  by_cases hinf : Threefold.projectionSphere y = (∞ : RiemannSphere)
  · exact ⟨.cusp, point_over_infty_mem_cusp hinf⟩
  · by_cases hone : Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere)
    · exact ⟨.elliptic, point_over_one_mem_elliptic hone⟩
    · exact ⟨.generic, (GlobalFiniteRegularSection.mem_domain y).mpr ⟨hinf, hone⟩⟩

def indexAt (y : Threefold.Space) : Patch := (exists_cover y).choose

theorem mem_cover_at (y : Threefold.Space) : y ∈ cover (indexAt y) :=
  (exists_cover y).choose_spec

/-- The two original filling patches do not meet even at regular points. -/
theorem elliptic_cusp_disjoint :
    Disjoint (cover .elliptic : Set Threefold.Space) (cover .cusp : Set Threefold.Space) := by
  apply Set.disjoint_left.mpr
  intro y he hc
  have he' : Threefold.projection y ∈ specialBaseCover.fillingPatch (some .four) := he
  have hc' : Threefold.projection y ∈ specialBaseCover.fillingPatch none := hc
  have hbad := specialBaseCover.filling_indices_eq_of_mem he' hc'
  cases hbad

theorem regular_le_generic : Threefold.regularLocus ≤ cover .generic :=
  GlobalFiniteRegularSection.regularLocus_le_domain

/-- On the elliptic overlap the comparison is the previously constructed
regular canonical comparison, on exactly the original regular locus. -/
theorem generic_elliptic_mem_regular {y : Threefold.Space}
    (hg : y ∈ cover .generic) (he : y ∈ cover .elliptic) : y ∈ Threefold.regularLocus :=
  GlobalFiniteRegularSection.mem_regular_of_mem_domain_of_mem_fourPatch hg he

/-- Removing infinity inside the cusp patch leaves only original regular points. -/
theorem generic_cusp_mem_regular {y : Threefold.Space}
    (hg : y ∈ cover .generic) (hc : y ∈ cover .cusp) : y ∈ Threefold.regularLocus := by
  change Threefold.projection y ∈ Threefold.regularPatch
  exact (specialBaseCover.fillingPatch_regular_iff none hc).mpr
    ((GlobalFiniteRegularSection.mem_domain_iff_projection y).mp hg).1

theorem generic_inf_elliptic_eq :
    cover .generic ⊓ cover .elliptic = Threefold.regularLocus ⊓ cover .elliptic :=
  GlobalFiniteRegularSection.domain_inf_fourPatch_eq

theorem generic_inf_cusp_eq :
    cover .generic ⊓ cover .cusp = Threefold.regularLocus ⊓ cover .cusp := by
  apply le_antisymm
  · intro y hy
    exact ⟨generic_cusp_mem_regular hy.1 hy.2, hy.2⟩
  · intro y hy
    exact ⟨regular_le_generic hy.1, hy.2⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalComparison
