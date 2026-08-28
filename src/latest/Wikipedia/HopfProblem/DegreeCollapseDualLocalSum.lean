import Wikipedia.HopfProblem.DegreeCollapseDualNeighborhoods
import Wikipedia.SmoothSixDPoincare.ConnectingLocalSum
import Wikipedia.SmoothSixDPoincare.SeparatedPointConnecting

/-!
# The actual framed-core detector is a sum of native local contributions

The source cover is the original crossing complement and the constructed
separated neighborhoods. Restrict the original sphere map on each overlap.
Naturality and disjoint-union homology give the actual finite sum. Every
local source class is then identified with its original one-point sphere
connecting class, retaining the exact inner-boundary parametrization.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold BigOperators

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
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X) (g : C(S₃, X))
  (D : Neighborhoods A g)

theorem map_crossing_complement : MapsTo g (crossings A g)ᶜ (oldPatch A) :=
  fun _ hx => hx

theorem map_separated_neighborhood (i : crossings A g) :
    MapsTo g (D.neighborhood i) A.chart.target := D.neighborhood_subset i

def localOverlap (i : crossings A g) :
    C(↥((crossings A g)ᶜ ∩ D.neighborhood i), ↥((oldPatch A : Set X) ∩ A.chart.target)) :=
  CoverLocalContributions.localMap (crossings A g)ᶜ D.neighborhood
    (oldPatch A) A.chart.target g (map_crossing_complement A g)
      (map_separated_neighborhood A g D) i

theorem localOverlap_normal (i : crossings A g) :
    (overlapDirection A).comp (localOverlap A g D i) = D.normalizedOverlapMap i := by
  apply ContinuousMap.ext
  intro x
  change PuncturedRadial.toSphere (overlapNormal A (localOverlap A g D i x)) =
    PuncturedRadial.toSphere (D.overlapMap i x)
  apply congrArg PuncturedRadial.toSphere
  apply Subtype.ext
  exact (D.overlapMap_coe i x).symm

theorem localOverlap_boundary (i : crossings A g) :
    (overlapDirection A).comp ((localOverlap A g D i).comp (D.overlapSphereEquiv i).toFun) =
      (D.data i).innerBoundary.normalizedMap := by
  rw [← ContinuousMap.comp_assoc, localOverlap_normal]
  exact D.normalizedOverlapMap_sphereEquiv i

theorem localOverlap_homology (i : crossings A g) (k : ℕ)
    (c : SingularHomology (↥((crossings A g)ᶜ ∩ D.neighborhood i)) k) :
    singularHomologyMap (overlapDirection A) k
      (singularHomologyMap (localOverlap A g D i) k c) =
      singularHomologyMap (D.data i).innerBoundary.normalizedMap k
        ((homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).symm c) := by
  let y := (homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).symm c
  have hy : singularHomologyMap (D.overlapSphereEquiv i).toFun k y = c :=
    (homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).apply_symm_apply c
  have h := DFunLike.congr_fun
    (congrArg (fun f : C(sphere (0 : P₃) 1, sphere (0 : F) 1) =>
      singularHomologyMap f k) (localOverlap_boundary A g D i)) y
  simp only [singularHomologyMap_comp, LinearMap.comp_apply] at h
  rw [hy] at h
  exact h

open Classical in
theorem detector_sum [Fintype (crossings A g)] (k : ℕ)
    (a : SingularHomology S₃ (k + 1)) :
    detector A k (singularHomologyMap g (k + 1) a) =
      ∑ i : crossings A g, singularHomologyMap (D.data i).innerBoundary.normalizedMap k
        (LocalDegree.NativeNeighborhood.sphereConnecting i.val (D.data i) k a) := by
  have hsum := CoverLocalContributions.connecting_sum (crossings A g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    (oldPatch A) A.chart.target g (map_crossing_complement A g)
    (map_separated_neighborhood A g D) (oldPatch A).isOpen A.chart.open_target (cover A) k a
  change singularHomologyMap (overlapDirection A) k
    (connectingHomomorphism (oldPatch A) A.chart.target (oldPatch A).isOpen
      A.chart.open_target (cover A) k (singularHomologyMap g (k + 1) a)) = _
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change singularHomologyMap (overlapDirection A) k
    (singularHomologyMap (localOverlap A g D i) k _) = _
  rw [localOverlap_homology, D.sphereConnecting_component]

end Wikipedia.HopfProblem.DegreeCollapse.DualCover
