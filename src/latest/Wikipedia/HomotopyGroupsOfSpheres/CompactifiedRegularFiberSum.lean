import Wikipedia.SmoothSixDPoincare.MorseCollapseLocalSum
import Wikipedia.SmoothSixDPoincare.SeparatedPointConnecting

/-!
# The actual compactified map is a sum over its separated regular fiber

The global map need only agree with a finite coordinate function on the
prescribed neighborhood. The source classes are the actual connecting
classes of the constructed cover and equal the native single-point classes.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HomotopyGroupsOfSpheres.CompactifiedRegularFiberSum

open Wikipedia.SmoothSixDPoincare
open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

section TargetCover

variable {M F : Type} [TopologicalSpace M] [NormedAddCommGroup F]
  {P W : Set M} {f : M → F} (G : C(M, OnePoint F))

theorem maps_old (hzero : ∀ x, G x = ((0 : F) : OnePoint F) ↔ x ∈ P) :
    MapsTo G Pᶜ OnePointCover.oldPatch := by
  intro x hx h0
  exact hx ((hzero x).mp h0)

theorem maps_finite (hfinite : ∀ x ∈ W, G x = (f x : OnePoint F)) :
    MapsTo G W OnePointCover.finitePatch := by
  intro x hx
  change G x ≠ OnePoint.infty
  rw [hfinite x hx]
  exact OnePoint.coe_ne_infty _

end TargetCover

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M]
  {P : Set M} {f : M → F} {W : Set M}
  (D : LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]

def componentConnecting (k : ℕ) :
    SingularHomology M (k + 1) →ₗ[ℤ]
      (∀ i : P, SingularHomology ↥(Pᶜ ∩ D.neighborhood i) k) :=
  CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
    (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood
    D.pairwise_disjoint D.open_cover k

def localClass (k : ℕ) (a : SingularHomology M (k + 1)) (i : P) :
    SingularHomology (sphere (0 : E) 1) k :=
  (homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).symm (componentConnecting D k a i)

theorem localClass_singlePoint (k : ℕ) (a : SingularHomology M (k + 1)) (i : P) :
    localClass D k a i = LocalDegree.NativeNeighborhood.sphereConnecting i.val (D.data i) k a :=
  D.sphereConnecting_component k a i

variable (G : C(M, OnePoint F))
  (hzero : ∀ x, G x = ((0 : F) : OnePoint F) ↔ x ∈ P)
  (hfinite : ∀ x ∈ W, G x = (f x : OnePoint F))

def overlapMap (i : P) :
    C(↥(Pᶜ ∩ D.neighborhood i), ↥(OnePointCover.oldPatch (N := F) ∩ OnePointCover.finitePatch)) :=
  CoverLocalContributions.localMap Pᶜ D.neighborhood
    OnePointCover.oldPatch OnePointCover.finitePatch G (maps_old G hzero)
    (fun i _ hx ↦ maps_finite G hfinite (D.neighborhood_subset i hx)) i

omit [T1Space M] [Fintype P] in
theorem overlapMap_eq (i : P) :
    overlapMap D G hzero hfinite i =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.overlapMap i) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change G x.val = (OnePointCover.overlapHomeomorph (D.overlapMap i x)).val
  rw [OnePointCover.overlapHomeomorph_apply, LocalDegree.SeparatedNeighborhoods.overlapMap_coe]
  exact hfinite x.val (D.neighborhood_subset i x.property.2)

omit [T1Space M] [Fintype P] in
theorem overlapMap_sphereEquiv (i : P) :
    (overlapMap D G hzero hfinite i).comp (D.overlapSphereEquiv i).toFun =
      OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.data i).innerBoundary.map := by
  rw [overlapMap_eq, ContinuousMap.comp_assoc, D.overlapMap_sphereEquiv]

theorem connecting_sum_overlaps (k : ℕ) (a : SingularHomology M (k + 1)) :
    connectingHomomorphism OnePointCover.oldPatch OnePointCover.finitePatch
      OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k
        (singularHomologyMap G (k + 1) a) =
      ∑ i, singularHomologyMap (overlapMap D G hzero hfinite i) k (componentConnecting D k a i) :=
  CoverLocalContributions.connecting_sum Pᶜ D.neighborhood
    (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    OnePointCover.oldPatch OnePointCover.finitePatch G (maps_old G hzero)
    (fun i _ hx ↦ maps_finite G hfinite (D.neighborhood_subset i hx))
    OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k a

include hzero hfinite in
theorem connecting_sum_boundaries (k : ℕ) (a : SingularHomology M (k + 1)) :
    connectingHomomorphism OnePointCover.oldPatch OnePointCover.finitePatch
      OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k
        (singularHomologyMap G (k + 1) a) =
      ∑ i, singularHomologyMap
        (OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp (D.data i).innerBoundary.map) k
          (localClass D k a i) := by
  rw [connecting_sum_overlaps D G hzero hfinite]
  apply Finset.sum_congr rfl
  intro i _
  have h : singularHomologyMap (D.overlapSphereEquiv i).toFun k (localClass D k a i) =
      componentConnecting D k a i :=
    (homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).apply_symm_apply _
  rw [← h, ← LinearMap.comp_apply, ← singularHomologyMap_comp, overlapMap_sphereEquiv]

include hzero hfinite in
theorem sphereConnecting_sum (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularHomology M (k + 1)) :
    OnePointCover.sphereConnecting r hr k (singularHomologyMap G (k + 1) a) =
      ∑ i, singularHomologyMap (D.data i).innerBoundary.normalizedMap k (localClass D k a i) := by
  change (OnePointCover.overlapHomologyEquiv (N := F) r hr k).symm
    (connectingHomomorphism OnePointCover.oldPatch OnePointCover.finitePatch
      OnePointCover.oldPatch_open OnePointCover.finitePatch_open OnePointCover.cover k
        (singularHomologyMap G (k + 1) a)) = _
  rw [connecting_sum_boundaries D G hzero hfinite, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [singularHomologyMap_comp, LinearMap.comp_apply,
    OnePointCover.overlapHomologyEquiv_symm_include]
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.CompactifiedRegularFiberSum
