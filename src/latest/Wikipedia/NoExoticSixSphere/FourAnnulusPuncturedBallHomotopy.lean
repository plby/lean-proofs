import Wikipedia.NoExoticSixSphere.FourDiskPuncturedBall
import Wikipedia.NoExoticSixSphere.FourAnnulusPuncturedRetraction
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBallHomotopy

/-!
# Original small sphere and linking sphere in the annulus singular complement

The retained chart expands its actual half-radius sphere to the original
linking sphere. The entire homotopy stays in the original annulus and
avoids both the origin and every actual annulus singularity. Thus the
induced native homology maps agree in the correct nonzero complement.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBall

open GLOrthonormalization PuncturedUnitBall SphereAnnulus
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} {x : Vector 4} (B : GenericFourAnnulus.ParityBall g x)

theorem annulus_closedRegion_nonzero {y : Vector 4} (hy : y ∈ B.closedRegion) : y ≠ 0 :=
  SphereAnnulus.ne_zero ⟨y, openDomain_subset_domain 3 (B.closedRegion_subset_interior hy)⟩

theorem annulus_puncturedOpenRegion_not_singular (y : B.puncturedOpenRegion) :
    y.val ∉ AnnulusDoublePoints.singularSet g := by
  intro hs
  have hm : y.val ∈ B.closedRegion ∩
      {z | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g z)} :=
    ⟨B.openRegion_subset_closedRegion y.property.1, hs.2⟩
  rw [B.closedRegion_inter_singular] at hm
  exact y.property.2 hm

def annulusComplementPuncturedInclusion :
    C(B.puncturedOpenRegion, GenericFourAnnulus.SingularComplement g) where
  toFun y := ⟨y.val, B.annulus_closedRegion_nonzero
    (B.openRegion_subset_closedRegion y.property.1), B.annulus_puncturedOpenRegion_not_singular y⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def annulusComplementSmallLink : C(Sphere 3, GenericFourAnnulus.SingularComplement g) :=
  B.annulusComplementPuncturedInclusion.comp B.puncturedSphereEquiv.symm.toFun

def annulusComplementLink : C(Sphere 3, GenericFourAnnulus.SingularComplement g) where
  toFun q := ⟨B.chart q.val,
    B.annulus_closedRegion_nonzero ⟨q.val, sphere_subset_closedBall q.property, rfl⟩,
    fun hs ↦ disjoint_left.mp B.boundaryRegion_disjoint_singular
      (show B.chart q.val ∈ B.boundaryRegion from ⟨q.val, q.property, rfl⟩) hs.2⟩
  continuous_toFun :=
    (B.chart.contMDiffOn_toFun.continuousOn.mono
      (sphere_subset_closedBall.trans B.ball_source)).domRestrict.subtype_mk _

def annulusSmallLinkHomotopy : B.annulusComplementSmallLink.Homotopy B.annulusComplementLink where
  toFun v := ⟨B.chart (boundaryAnnulus v),
    B.annulus_closedRegion_nonzero ⟨boundaryAnnulus v, boundaryAnnulus_mem_closedBall v, rfl⟩,
    fun hs ↦ boundaryAnnulus_ne_zero v
      ((B.singular_iff _ (boundaryAnnulus_mem_closedBall v)).mp hs.2)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact B.chart.contMDiffOn_toFun.continuousOn.comp_continuous boundaryAnnulus.continuous
      (fun v ↦ B.ball_source (boundaryAnnulus_mem_closedBall v))
  map_zero_left q := by
    apply Subtype.ext
    change B.chart (boundaryAnnulus (0, q)) = (B.puncturedSphereEquiv.symm q).val
    rw [B.puncturedSphereEquiv_symm_apply]
    simp [boundaryAnnulus]
  map_one_left q := by
    apply Subtype.ext
    change B.chart (boundaryAnnulus (1, q)) = B.chart q.val
    simp [boundaryAnnulus]

theorem annulusComplementSmallLink_homologyMap (n : ℕ) :
    singularHomologyMap B.annulusComplementSmallLink n =
      singularHomologyMap B.annulusComplementLink n :=
  homotopy_homologyMap B.annulusSmallLinkHomotopy n

end NoExoticSixSphere.GenericFourDisk.ParityBall
