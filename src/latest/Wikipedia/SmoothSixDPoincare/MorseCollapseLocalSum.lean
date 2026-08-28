import Wikipedia.SmoothSixDPoincare.MorseCollapseCoverMap
import Wikipedia.SmoothSixDPoincare.OnePointCollapseHomology

/-!
# The original Morse collapse is a sum of its constructed local boundary maps

The separated cover is now the original cover at the actual belt crossings.
Each source connecting class is transported through its actual inner-sphere
equivalence. The target connecting map is the sum of the original normalized
boundary maps on these classes. No claim that those source classes equal a
fixed oriented generator is made here; that is the remaining comparison.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

namespace OnePointCover

variable {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]

theorem overlapHomologyEquiv_symm_include (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularHomology (PuncturedRadial.Space N) k) :
    (overlapHomologyEquiv r hr k).symm
      (singularHomologyMap overlapHomeomorph.toHomotopyEquiv.toFun k a) =
        singularHomologyMap PuncturedRadial.toSphere k a := by
  change (homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k).symm _ = _
  rw [homotopyEquivHomologyEquiv_symm_apply]
  have heq : (overlapSphereEquiv (N := N) r hr).symm.toFun.comp
      overlapHomeomorph.toHomotopyEquiv.toFun = PuncturedRadial.toSphere := by
    apply ContinuousMap.ext
    intro x
    change PuncturedRadial.toSphere (overlapHomeomorph.symm (overlapHomeomorph x)) = _
    rw [Homeomorph.symm_apply_apply]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, heq]

end OnePointCover

namespace ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : Continuous f) (m : ℕ)
  (g : C(Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
  [Fintype (d.beltIntersectionPoints m g)]

open Classical in
def collapseComponentConnecting (k : ℕ) :
    SingularHomology (Hemisphere.Sphere m) (k + 1) →ₗ[ℤ]
      (∀ i : d.beltIntersectionPoints m g,
        SingularHomology (↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i)) k) :=
  CoverLocalContributions.componentConnecting (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover k

open Classical in
/-- Actual source connecting classes in the constructed local boundary-sphere coordinates. -/
def collapseLocalClass (k : ℕ) (a : SingularHomology (Hemisphere.Sphere m) (k + 1))
    (i : d.beltIntersectionPoints m g) :
    SingularHomology (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) k :=
  (homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).symm
    (d.collapseComponentConnecting m g D k a i)

open Classical in
theorem collapseConnecting_sum_overlaps (k : ℕ)
    (a : SingularHomology (Hemisphere.Sphere m) (k + 1)) :
    connectingHomomorphism OnePointCover.oldPatch OnePointCover.finitePatch
      OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k
        (singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i, singularHomologyMap (d.collapseOverlapMap hf m g D i) k
        (d.collapseComponentConnecting m g D k a i) :=
  CoverLocalContributions.connecting_sum (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    OnePointCover.oldPatch OnePointCover.finitePatch (d.attachingCollapse hf m g)
    (d.attachingCollapse_maps_old hf m g) (d.attachingCollapse_maps_neighborhood hf m g D)
    OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k a

open Classical in
theorem collapseConnecting_sum_boundaries (k : ℕ)
    (a : SingularHomology (Hemisphere.Sphere m) (k + 1)) :
    connectingHomomorphism OnePointCover.oldPatch OnePointCover.finitePatch
      OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k
        (singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i, singularHomologyMap
        (OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.data i).innerBoundary.map) k
        (d.collapseLocalClass m g D k a i) := by
  rw [d.collapseConnecting_sum_overlaps hf m g D k a]
  apply Finset.sum_congr rfl
  intro i _
  have h : singularHomologyMap (D.overlapSphereEquiv i).toFun k
      (d.collapseLocalClass m g D k a i) = d.collapseComponentConnecting m g D k a i :=
    (homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).apply_symm_apply _
  rw [← h, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    d.collapseOverlapMap_sphereEquiv hf m g D i]

open Classical in
/-- The original collapse homology is the sum of the actual normalized local boundary actions. -/
theorem collapseSphereConnecting_sum (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularHomology (Hemisphere.Sphere m) (k + 1)) :
    OnePointCover.sphereConnecting r hr k
      (singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
        ∑ i, singularHomologyMap (D.data i).innerBoundary.normalizedMap k
          (d.collapseLocalClass m g D k a i) := by
  change (OnePointCover.overlapHomologyEquiv (N := d.chart.NegativeCoordinates) r hr k).symm
    (connectingHomomorphism OnePointCover.oldPatch OnePointCover.finitePatch
      OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k
      (singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a)) = _
  rw [d.collapseConnecting_sum_boundaries hf m g D k a, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [singularHomologyMap_comp, LinearMap.comp_apply,
    OnePointCover.overlapHomologyEquiv_symm_include]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end ManifoldMorse.MorseSurgeryData

end Wikipedia.SmoothSixDPoincare
