import Wikipedia.SmoothSixDPoincare.SeparatedDegreeCover
import Wikipedia.SmoothSixDPoincare.NativeDegreeNeighborhoodMaps

/-!
# Original finite-representative maps on the separated global-cover overlaps

Each global-cover overlap is the corresponding one-center puncture. The
map on it is the original function, and its composition with the actual
overlap-sphere equivalence is exactly the constructed inner boundary map.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree.SeparatedNeighborhoods

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {P : Set M} {f : M → F} {W : Set M} (D : SeparatedNeighborhoods E P f W)

def overlapMap (x : P) : C(↥(Pᶜ ∩ D.neighborhood x), PuncturedRadial.Space F) :=
  (NativeNeighborhood.overlapMap (x : M) (D.data x)).comp
    (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

theorem overlapMap_coe (x : P) (y : ↥(Pᶜ ∩ D.neighborhood x)) :
    (D.overlapMap x y).val = f y.val :=
  NativeNeighborhood.overlapMap_coe (x : M) (D.data x) _

theorem overlapMap_sphereEquiv (x : P) :
    (D.overlapMap x).comp (D.overlapSphereEquiv x).toFun = (D.data x).innerBoundary.map := by
  apply ContinuousMap.ext
  intro u
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, overlapMap_coe, overlapSphereEquiv_apply,
    BoundaryData.map_coe]
  rfl

def normalizedOverlapMap (x : P) : C(↥(Pᶜ ∩ D.neighborhood x), sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp (D.overlapMap x)

theorem normalizedOverlapMap_sphereEquiv (x : P) :
    (D.normalizedOverlapMap x).comp (D.overlapSphereEquiv x).toFun =
      (D.data x).innerBoundary.normalizedMap := by
  change (PuncturedRadial.toSphere.comp (D.overlapMap x)).comp _ = _
  rw [ContinuousMap.comp_assoc, overlapMap_sphereEquiv]
  rfl

end Wikipedia.SmoothSixDPoincare.LocalDegree.SeparatedNeighborhoods
