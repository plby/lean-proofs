import Wikipedia.HopfProblem.DegreeCollapseDualCover
import Wikipedia.SmoothSixDPoincare.SpherePointConnecting
import Wikipedia.SmoothSixDPoincare.NativeDegreeNeighborhoodMaps

/-!
# The dual detector on an actual sphere is its original local normal degree

The source cover consists of the punctured sphere and a constructed native
regular-zero neighborhood. Restrict the original sphere map on its actual
overlap. Naturality of the genuine connecting homomorphism identifies the
ambient detector with the normalized small-boundary map after the native
source connecting isomorphism. Both factors are actual isomorphisms.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.DualCover

open Wikipedia.SmoothSixDPoincare FramedSurgery PuncturedHandle
open SingularMayerVietoris PeriodTorusHigherHomology

local notation "P₃" => EuclideanSpace ℝ (Fin 3)
local notation "S₃" => sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {E F G H X : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (g : C(S₃, X)) (q : S₃)
  (hunique : ∀ x, g x ∈ range (coreMap A) → x = q)
  {L : P₃ ≃L[ℝ] F}
  (d : LocalDegree.NeighborhoodData
    ((normalProjection A ∘ g) ∘ NativeParametrization.centered (D := P₃) q) L
    ((NativeParametrization.centered (D := P₃) q).source ∩
      NativeParametrization.centered (D := P₃) q ⁻¹' (g ⁻¹' A.chart.target)))

include hunique in
theorem map_puncture : MapsTo g ({q}ᶜ : Set S₃) (oldPatch A) :=
  fun x hx h => hx (hunique x h)

theorem map_neighborhood : MapsTo g (LocalDegree.NativeNeighborhood.openSet q d) A.chart.target :=
  LocalDegree.NativeNeighborhood.openSet_subset q d

def restrictedOverlap :
    C(↥({q}ᶜ ∩ LocalDegree.NativeNeighborhood.openSet q d),
      ↥((oldPatch A : Set X) ∩ A.chart.target)) :=
  CoverNaturality.mapOn g _ _
    (CoverNaturality.map_intersection _ _ _ _ g
      (map_puncture A g q hunique) (map_neighborhood A g q d))

theorem overlap_normal_compare :
    (overlapDirection A).comp (restrictedOverlap A g q hunique d) =
      LocalDegree.NativeNeighborhood.normalizedOverlapMap q d := by
  apply ContinuousMap.ext
  intro x
  change PuncturedRadial.toSphere (overlapNormal A (restrictedOverlap A g q hunique d x)) =
    PuncturedRadial.toSphere (LocalDegree.NativeNeighborhood.overlapMap q d x)
  apply congrArg PuncturedRadial.toSphere
  apply Subtype.ext
  exact (LocalDegree.NativeNeighborhood.overlapMap_coe q d x).symm

include hunique in
theorem detector_naturality (k : ℕ) (x : SingularHomology S₃ (k + 1)) :
    detector A k (singularHomologyMap g (k + 1) x) =
      singularHomologyMap d.innerBoundary.normalizedMap k
        (LocalDegree.NativeNeighborhood.sphereConnecting q d k x) := by
  let S := LocalDegree.NativeNeighborhood.overlapSphereEquiv q d
  let C := connectingHomomorphism {q}ᶜ (LocalDegree.NativeNeighborhood.openSet q d)
    isClosed_singleton.isOpen_compl (LocalDegree.NativeNeighborhood.isOpen_openSet q d)
    (LocalDegree.NativeNeighborhood.singlePoint_cover q d) k
  let z := (homotopyEquivHomologyEquiv S k).symm (C x)
  have hz : singularHomologyMap S.toFun k z = C x :=
    (homotopyEquivHomologyEquiv S k).apply_symm_apply _
  have hn := CoverNaturality.connecting_naturality_apply
    {q}ᶜ (LocalDegree.NativeNeighborhood.openSet q d) (oldPatch A) A.chart.target g
    (map_puncture A g q hunique) (map_neighborhood A g q d)
    isClosed_singleton.isOpen_compl (LocalDegree.NativeNeighborhood.isOpen_openSet q d)
    (LocalDegree.NativeNeighborhood.singlePoint_cover q d) (oldPatch A).isOpen
    A.chart.open_target (cover A) k x
  have hmaps : (overlapDirection A).comp ((restrictedOverlap A g q hunique d).comp S.toFun) =
      d.innerBoundary.normalizedMap := by
    rw [← ContinuousMap.comp_assoc, overlap_normal_compare]
    exact LocalDegree.NativeNeighborhood.normalizedOverlapMap_sphereEquiv q d
  have h := DFunLike.congr_fun
    (congrArg (fun f : C(sphere (0 : P₃) 1, sphere (0 : F) 1) =>
      singularHomologyMap f k) hmaps) z
  simp only [singularHomologyMap_comp, LinearMap.comp_apply] at h
  rw [hz] at h
  change singularHomologyMap (restrictedOverlap A g q hunique d) k (C x) = _ at hn
  rw [hn] at h
  exact h

def compositeEquiv : SingularHomology S₃ 3 ≃ₗ[ℤ] SingularHomology (sphere (0 : F) 1) 2 :=
  (SpherePoint.connectingHomologyEquiv q d 1).trans (d.innerBoundary.normalizedHomologyEquiv 2)

include hunique in
theorem compositeEquiv_apply (x : SingularHomology S₃ 3) :
    compositeEquiv A g q d x = detector A 2 (singularHomologyMap g 3 x) := by
  change d.innerBoundary.normalizedHomologyEquiv 2
    (LocalDegree.NativeNeighborhood.sphereConnecting q d 2 x) = _
  rw [LocalDegree.BoundaryData.normalizedHomologyEquiv_apply]
  exact (detector_naturality A g q hunique d 2 x).symm

end Wikipedia.HopfProblem.DegreeCollapse.DualCover
