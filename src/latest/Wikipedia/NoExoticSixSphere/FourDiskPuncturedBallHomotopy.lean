import Wikipedia.NoExoticSixSphere.FourDiskPuncturedBall
import Wikipedia.NoExoticSixSphere.FourDiskPuncturedRetraction
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBallHomotopy

/-!
# The original local sphere and linking sphere agree in complement homology

An actual annulus in the retained chart expands the half-radius sphere
to its original linking sphere while avoiding every closed-disk native
singularity. The induced integral homology maps are therefore equal.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBall

open GLOrthonormalization PuncturedUnitBall DiskDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} {x : Vector 4} (B : ParityBall g x)

theorem puncturedOpenRegion_not_singular (y : B.puncturedOpenRegion) : y.val ∉ singularSet g := by
  intro hs
  have hm : y.val ∈ B.closedRegion ∩
      {z | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g z)} :=
    ⟨B.openRegion_subset_closedRegion y.property.1, hs.2⟩
  rw [B.closedRegion_inter_singular] at hm
  exact y.property.2 hm

def complementPuncturedInclusion : C(B.puncturedOpenRegion, SingularComplement g) where
  toFun y := ⟨y.val, B.puncturedOpenRegion_not_singular y⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def complementSmallLink : C(Sphere 3, SingularComplement g) :=
  B.complementPuncturedInclusion.comp B.puncturedSphereEquiv.symm.toFun

def complementLink : C(Sphere 3, SingularComplement g) where
  toFun s := ⟨B.chart s.val, fun hs ↦ disjoint_left.mp B.boundaryRegion_disjoint_singular
    (show B.chart s.val ∈ B.boundaryRegion from ⟨s.val, s.property, rfl⟩) hs.2⟩
  continuous_toFun :=
    (B.chart.contMDiffOn_toFun.continuousOn.mono
      (sphere_subset_closedBall.trans B.ball_source)).domRestrict.subtype_mk _

def smallLinkHomotopy : B.complementSmallLink.Homotopy B.complementLink where
  toFun p := ⟨B.chart (boundaryAnnulus p), fun hs ↦ boundaryAnnulus_ne_zero p
    ((B.singular_iff _ (boundaryAnnulus_mem_closedBall p)).mp hs.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact B.chart.contMDiffOn_toFun.continuousOn.comp_continuous boundaryAnnulus.continuous
      (fun p ↦ B.ball_source (boundaryAnnulus_mem_closedBall p))
  map_zero_left s := by
    apply Subtype.ext
    change B.chart (boundaryAnnulus (0, s)) = (B.puncturedSphereEquiv.symm s).val
    rw [B.puncturedSphereEquiv_symm_apply]
    simp [boundaryAnnulus]
  map_one_left s := by
    apply Subtype.ext
    change B.chart (boundaryAnnulus (1, s)) = B.chart s.val
    simp [boundaryAnnulus]

theorem complementSmallLink_homologyMap (n : ℕ) :
    singularHomologyMap B.complementSmallLink n = singularHomologyMap B.complementLink n :=
  homotopy_homologyMap B.smallLinkHomotopy n

end NoExoticSixSphere.GenericFourDisk.ParityBall
