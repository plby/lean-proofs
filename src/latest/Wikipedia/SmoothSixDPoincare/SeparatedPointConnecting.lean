import Wikipedia.SmoothSixDPoincare.SeparatedDegreeCover
import Wikipedia.SmoothSixDPoincare.CoverComponentConnecting
import Wikipedia.SmoothSixDPoincare.NativePointConnecting

/-!
# The actual many-point local source class is its native single-point class

Enlarge the original point complement to the complement of the selected
point. The component comparison identifies the original connecting class;
the proved pointwise overlap equivalence transfers it to exactly the same
inner-sphere coordinates used by the native single-point connecting map.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree.SeparatedNeighborhoods

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M]
  {P : Set M} {f : M → F} {W : Set M} (D : SeparatedNeighborhoods E P f W) [Fintype P]

def pointComplementInclusion (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), ↥({(x : M)}ᶜ ∩ D.neighborhood x)) :=
  (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

omit [T1Space M] [Fintype P] in
theorem pointComplementInclusion_sphereEquiv (x : P) :
    (D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun =
      (NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun := by
  apply ContinuousMap.ext
  intro u
  rfl

theorem componentConnecting_singlePoint (k : ℕ) (a : SingularHomology M (k + 1)) (x : P) :
    singularHomologyMap (D.pointComplementInclusion x) k
      (CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
        (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood
        D.pairwise_disjoint D.open_cover k a x) =
      connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x) isClosed_singleton.isOpen_compl
        (D.isOpen_neighborhood x)
        (NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a := by
  have hsub : Pᶜ ⊆ {(x : M)}ᶜ := by
    intro y hy hxy
    exact hy (hxy ▸ x.property)
  exact CoverLocalContributions.componentConnecting_enlarge Pᶜ {(x : M)}ᶜ D.neighborhood
    (Set.toFinite P).isClosed.isOpen_compl isClosed_singleton.isOpen_compl
    D.isOpen_neighborhood D.pairwise_disjoint D.open_cover hsub x
    (NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a

/-- Equality of the actual local sphere classes, not only equality up to an unspecified sign. -/
theorem sphereConnecting_component (k : ℕ) (a : SingularHomology M (k + 1)) (x : P) :
    (homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
      (CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
        (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood
        D.pairwise_disjoint D.open_cover k a x) =
      NativeNeighborhood.sphereConnecting (x : M) (D.data x) k a := by
  let c := CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
    (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood
    D.pairwise_disjoint D.open_cover k a x
  apply (homotopyEquivHomologyEquiv
    (NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).injective
  change singularHomologyMap
    (NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun k
    ((homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm c) =
      (homotopyEquivHomologyEquiv
        (NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k)
        ((homotopyEquivHomologyEquiv
          (NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).symm _)
  rw [LinearEquiv.apply_symm_apply, ← D.pointComplementInclusion_sphereEquiv x]
  change singularHomologyMap
    ((D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun) k
    ((homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm c) =
      connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x) isClosed_singleton.isOpen_compl
        (D.isOpen_neighborhood x)
        (NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a
  rw [singularHomologyMap_comp, LinearMap.comp_apply]
  have h : singularHomologyMap (D.overlapSphereEquiv x).toFun k
      ((homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm c) = c :=
    (homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).apply_symm_apply c
  rw [h]
  exact D.componentConnecting_singlePoint k a x

end Wikipedia.SmoothSixDPoincare.LocalDegree.SeparatedNeighborhoods
