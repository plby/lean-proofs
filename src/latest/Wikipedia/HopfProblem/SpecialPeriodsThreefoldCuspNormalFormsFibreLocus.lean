import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspNormalFormsFibre

/-!
# The literal cusp fibre is a union of coordinate planes

On the actual full cusp patch, vanishing of the original cusp coordinate
is equivalent to lying in the literal sphere fibre over infinity.  The
proved product normal forms therefore identify that fibre, as a subset
of each existing ambient chart, with the union of its coordinate planes.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms

open ToricCharts CuspGeometry

local notation "E₃" => CoordinateSpace 3
local notation "I₃" => modelWithCornersSelf ℂ E₃
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

/-- On the full actual cusp patch, the zero set of the original cusp
coordinate is precisely the literal global fibre over infinity. -/
theorem mem_sphereCuspFibre_iff_cuspCoordinate_eq_zero {z : Threefold.Space}
    (hz : z ∈ (Threefold.liftedPatch (some none) : Set Threefold.Space)) :
    z ∈ sphereCuspFibre ↔ cuspCoordinate z = 0 := by
  have hzt : z ∈ nativeParametrization.target := by
    simpa only [nativeParametrization_target] using hz
  have he : CuspGeometry.inclusion (nativeParametrization.symm z) = z :=
    nativeParametrization.right_inv' hzt
  rw [← he, inclusion_mem_sphereCuspFibre_iff, mem_localCentralFibre,
    cuspCoordinate_inclusion]

/-- The inverse of an actual normal-form chart lies on the literal
global cusp fibre exactly when one of its branch coordinates vanishes. -/
theorem normalForm_fibre_mem_iff
    (J : Finset (Fin 3)) (e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω)
    (hsource : e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space))
    (hprod : ∀ w ∈ e.target,
      sphereChart (Threefold.projectionSphere (e.symm w)) = ∏ j ∈ J, w j)
    (w : E₃) (hw : w ∈ e.target) :
    e.symm w ∈ sphereCuspFibre ↔ ∃ j ∈ J, w j = 0 := by
  have hws : e.symm w ∈ e.source := e.map_target' hw
  rw [mem_sphereCuspFibre_iff_cuspCoordinate_eq_zero (hsource hws),
    ← sphereChart_projectionSphere, hprod w hw, Finset.prod_eq_zero_iff]

/-- The image of the literal fibre inside an actual normal-form chart
is exactly the union of the indicated coordinate planes in its target. -/
theorem normalForm_fibre_image
    (J : Finset (Fin 3)) (e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω)
    (hsource : e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space))
    (hprod : ∀ w ∈ e.target,
      sphereChart (Threefold.projectionSphere (e.symm w)) = ∏ j ∈ J, w j) :
    e '' (sphereCuspFibre ∩ e.source) = e.target ∩ {w : E₃ | ∃ j ∈ J, w j = 0} := by
  ext w
  constructor
  · rintro ⟨z, ⟨hzf, hzs⟩, rfl⟩
    have hw : e z ∈ e.target := e.map_source' hzs
    refine ⟨hw, (normalForm_fibre_mem_iff J e hsource hprod (e z) hw).mp ?_⟩
    have hleft : e.symm (e z) = z := e.left_inv' hzs
    simpa only [hleft] using hzf
  · rintro ⟨hw, hzero⟩
    exact ⟨e.symm w,
      ⟨(normalForm_fibre_mem_iff J e hsource hprod w hw).mpr hzero, e.map_target' hw⟩,
      e.right_inv' hw⟩

/-- At every point of the literal cusp fibre, the existing ambient
complex atlas identifies that fibre with exactly as many coordinate
planes as its actual branch count.  The centered product equation and
the exact subset image are both retained. -/
theorem fibre_coordinate_plane_chart (y : sphereCuspFibre) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      J.card = fibreBranchCount y ∧ J.Nonempty ∧
      (y : Threefold.Space) ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      (∀ w ∈ e.target,
        sphereChart (Threefold.projectionSphere (e.symm w)) = ∏ j ∈ J, w j) ∧
      (∀ w ∈ e.target, e.symm w ∈ sphereCuspFibre ↔ ∃ j ∈ J, w j = 0) ∧
      e '' (sphereCuspFibre ∩ e.source) =
        e.target ∩ {w : E₃ | ∃ j ∈ J, w j = 0} := by
  obtain ⟨J, e, hcard, hJ, hys, hzero, hsource, hprod⟩ :=
    fibre_normalCrossingChart_with_branchCount y
  exact ⟨J, e, hcard, hJ, hys, hzero, hsource, hprod,
    normalForm_fibre_mem_iff J e hsource hprod, normalForm_fibre_image J e hsource hprod⟩

/-- The coordinate-plane description stated for an arbitrary ambient
point whose actual sphere projection is infinity. -/
theorem sphereInfinity_coordinate_plane_chart (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = (∞ : RiemannSphere)) :
    ∃ J : Finset (Fin 3), ∃ e : PartialDiffeomorph IF I₃ Threefold.Space E₃ ω,
      J.card = fibreBranchCount ⟨y, hy⟩ ∧ J.Nonempty ∧
      y ∈ e.source ∧ e y = 0 ∧
      e.source ⊆ (Threefold.liftedPatch (some none) : Set Threefold.Space) ∧
      (∀ w ∈ e.target,
        sphereChart (Threefold.projectionSphere (e.symm w)) = ∏ j ∈ J, w j) ∧
      (∀ w ∈ e.target, e.symm w ∈ sphereCuspFibre ↔ ∃ j ∈ J, w j = 0) ∧
      e '' (sphereCuspFibre ∩ e.source) =
        e.target ∩ {w : E₃ | ∃ j ∈ J, w j = 0} :=
  fibre_coordinate_plane_chart ⟨y, hy⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.CuspNormalForms
