import Wikipedia.SmoothSixDPoincare.MorseCollapseNeighborhoods
import Wikipedia.SmoothSixDPoincare.OnePointCollapseCover
import Wikipedia.SmoothSixDPoincare.ConnectingLocalSum

/-!
# The original Morse collapse maps the constructed separated open cover

Its exact zero fiber gives the old-cover map, and every constructed local
neighborhood lies in the original finite surgery interior. On each actual
overlap, the same collapse is the compactification inclusion of the original
punctured finite representative, with the same inner boundary values.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : Continuous f)

open Classical in
def attachingCollapse (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) :
    C(Hemisphere.Sphere m, OnePoint d.chart.NegativeCoordinates) :=
  (d.levelCollapseMap hf).comp g

open Classical in
theorem attachingCollapse_zero_iff (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel))
    (x : Hemisphere.Sphere m) :
    d.attachingCollapse hf m g x = ((0 : d.chart.NegativeCoordinates) : OnePoint _) ↔
      x ∈ d.beltIntersectionPoints m g := d.levelCollapse_zero_iff hf (g x)

open Classical in
theorem attachingCollapse_maps_old (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel)) :
    MapsTo (d.attachingCollapse hf m g) (d.beltIntersectionPoints m g)ᶜ OnePointCover.oldPatch := by
  intro x hx hzero
  exact hx ((d.attachingCollapse_zero_iff hf m g x).mp hzero)

open Classical in
theorem attachingCollapse_maps_neighborhood (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel))
    (D : d.CollapseNeighborhoods m g) (i : d.beltIntersectionPoints m g) :
    MapsTo (d.attachingCollapse hf m g) (D.neighborhood i) OnePointCover.finitePatch := by
  intro x hx
  have hnew : g x ∈ d.surgery.NewInterior := D.neighborhood_subset i hx
  change d.levelCollapseMap hf (g x) ≠ OnePoint.infty
  rw [d.levelCollapse_eq_coe_collapseNormal hf hnew]
  exact OnePoint.coe_ne_infty _

open Classical in
def collapseOverlapMap (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel))
    (D : d.CollapseNeighborhoods m g) (i : d.beltIntersectionPoints m g) :
    C(↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i),
      ↥(OnePointCover.oldPatch (N := d.chart.NegativeCoordinates) ∩ OnePointCover.finitePatch)) :=
  CoverNaturality.mapOn (d.attachingCollapse hf m g) _ _
    (fun _ hx => ⟨d.attachingCollapse_maps_old hf m g hx.1,
      d.attachingCollapse_maps_neighborhood hf m g D i hx.2⟩)

open Classical in
theorem collapseOverlapMap_eq (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel))
    (D : d.CollapseNeighborhoods m g) (i : d.beltIntersectionPoints m g) :
    d.collapseOverlapMap hf m g D i =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.overlapMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change d.levelCollapseMap hf (g x.val) =
    (OnePointCover.overlapHomeomorph (D.overlapMap i x)).val
  rw [OnePointCover.overlapHomeomorph_apply, LocalDegree.SeparatedNeighborhoods.overlapMap_coe]
  exact d.levelCollapse_eq_coe_collapseNormal hf (D.neighborhood_subset i x.property.2)

open Classical in
theorem collapseOverlapMap_sphereEquiv (m : ℕ) (g : C(Hemisphere.Sphere m, d.UpperLevel))
    (D : d.CollapseNeighborhoods m g) (i : d.beltIntersectionPoints m g) :
    (d.collapseOverlapMap hf m g D i).comp (D.overlapSphereEquiv i).toFun =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.data i).innerBoundary.map := by
  rw [d.collapseOverlapMap_eq hf m g D i, ContinuousMap.comp_assoc, D.overlapMap_sphereEquiv]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
