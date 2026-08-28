import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureHomology
import Wikipedia.NoExoticSixSphere.MayerVietorisVanishingEquiv
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleMayerVietorisNaturality

/-!
# Actual global and one-point connecting maps for the punctured four-sphere

The one-point comparison connecting maps are isomorphisms in every positive
degree by the proved vanishing of all adjacent groups. Naturality relates the
actual global connecting class to each comparison class. Its inclusion into
the original finite-point complement is zero by the actual exact sequence.
The component-coordinate and unit-coefficient calculation remains separate.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

def singleConnectingEquiv (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (Sphere 4) (n + 1) ≃ₗ[ℤ]
      SingularHomology (singlePunctureRegularSet g i ∩ P.coverRegion : Set (Sphere 4)) n := by
  letI := singlePunctureRegularSet_homology_subsingleton g i n hn
  letI := P.coverRegion_homology_subsingleton n hn
  letI := singlePunctureRegularSet_homology_subsingleton g i (n + 1) (Nat.succ_ne_zero n)
  letI := P.coverRegion_homology_subsingleton (n + 1) (Nat.succ_ne_zero n)
  exact MayerVietorisVanishing.connectingEquiv (singlePunctureRegularSet g i) P.coverRegion
    (isOpen_singlePunctureRegularSet g i) P.isOpen_coverRegion (P.single_puncture_cover i) n

theorem singleConnectingEquiv_apply (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (Sphere 4) (n + 1)) :
    P.singleConnectingEquiv i n hn a =
      connectingHomomorphism (singlePunctureRegularSet g i) P.coverRegion
        (isOpen_singlePunctureRegularSet g i) P.isOpen_coverRegion
          (P.single_puncture_cover i) n a :=
  rfl

def globalConnectingMap (n : ℕ) : SingularHomology (Sphere 4) (n + 1) →ₗ[ℤ]
    SingularHomology (sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)) n :=
  connectingHomomorphism (sphereRegularSet g) P.coverRegion
    P.isOpen_sphereRegularSet P.isOpen_coverRegion P.sphere_regular_cover n

def globalToSingleIntersection (i : BoundaryIndex g) :
    C((sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)),
      (singlePunctureRegularSet g i ∩ P.coverRegion : Set (Sphere 4))) :=
  ContinuousMap.inclusion (inter_subset_inter_left _ (sphereRegular_subset_single g i))

theorem globalConnectingMap_to_single (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (Sphere 4) (n + 1)) :
    singularHomologyMap (P.globalToSingleIntersection i) n (P.globalConnectingMap n a) =
      P.singleConnectingEquiv i n hn a := by
  have h := connectingHomomorphism_naturality_apply (ContinuousMap.id (Sphere 4))
    (sphereRegularSet g) P.coverRegion (singlePunctureRegularSet g i) P.coverRegion
    (fun _ hx ↦ sphereRegular_subset_single g i hx) (fun _ hx ↦ hx)
    P.isOpen_sphereRegularSet P.isOpen_coverRegion P.sphere_regular_cover
    (isOpen_singlePunctureRegularSet g i) P.isOpen_coverRegion (P.single_puncture_cover i) n a
  rw [singularHomologyMap_id, LinearMap.id_apply] at h
  exact h

theorem globalConnectingMap_inclusion_zero (n : ℕ) (a : SingularHomology (Sphere 4) (n + 1)) :
    singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_left :
        sphereRegularSet g ∩ P.coverRegion ⊆ sphereRegularSet g)) n
      (P.globalConnectingMap n a) = 0 := by
  have h := LinearMap.congr_fun (connectingHomomorphism_comp_left (sphereRegularSet g)
    P.coverRegion P.isOpen_sphereRegularSet P.isOpen_coverRegion P.sphere_regular_cover n) a
  change leftHomologyMap (sphereRegularSet g) P.coverRegion n (P.globalConnectingMap n a) = 0 at h
  rw [leftHomologyMap_apply] at h
  exact congrArg (fun p : SingularHomology (sphereRegularSet g) n ×
    SingularHomology P.coverRegion n ↦ p.1) h

end NoExoticSixSphere.SphereFamily.ParityBallSystem
