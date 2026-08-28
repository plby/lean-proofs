import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBall
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedRetraction

/-!
# The local sphere and the actual linking sphere have the same homology image

The homotopy expands the half-radius sphere to the unit sphere in the original
ball chart. Its whole image avoids every intrinsic singularity. Consequently
the local sphere map and the actual linking-sphere map agree in
the integral homology of the actual regular parameter space.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.PuncturedUnitBall

open GLOrthonormalization

def boundaryAnnulus : C(unitInterval × Sphere 3, Vector 4) where
  toFun p := ((1 + (p.1 : ℝ)) / 2) • p.2.val
  continuous_toFun := ((continuous_const.add
    (continuous_subtype_val.comp continuous_fst)).div_const 2).smul
      (continuous_subtype_val.comp continuous_snd)

theorem norm_boundaryAnnulus (p : unitInterval × Sphere 3) :
    ‖boundaryAnnulus p‖ = (1 + (p.1 : ℝ)) / 2 := by
  have hs : ‖p.2.val‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using p.2.property
  have ht : 0 < (1 + (p.1 : ℝ)) / 2 := by linarith [p.1.property.1]
  change ‖((1 + (p.1 : ℝ)) / 2) • p.2.val‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hs, mul_one]

theorem boundaryAnnulus_mem_closedBall (p : unitInterval × Sphere 3) :
    boundaryAnnulus p ∈ closedBall (0 : Vector 4) 1 := by
  rw [mem_closedBall, dist_zero_right, norm_boundaryAnnulus]
  linarith [p.1.property.2]

theorem boundaryAnnulus_ne_zero (p : unitInterval × Sphere 3) : boundaryAnnulus p ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_boundaryAnnulus]
  linarith [p.1.property.1]

end NoExoticSixSphere.PuncturedUnitBall

namespace NoExoticSixSphere.SphereFamily.ParityBall

open GLOrthonormalization PuncturedUnitBall
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} {q : ℝ × Sphere 3} (B : ParityBall g q)

theorem puncturedOpenRegion_not_singular (y : B.puncturedOpenRegion) :
    y.val ∉ singularParameters (n := 6) g := by
  intro hs
  have hm : y.val ∈ B.closedRegion ∩ singularParameters (n := 6) g :=
    ⟨B.openRegion_subset_closedRegion y.property.1, hs⟩
  rw [B.closedRegion_inter_singular] at hm
  exact y.property.2 hm

def regularPuncturedInclusion : C(B.puncturedOpenRegion, RegularParameters g) where
  toFun y := ⟨y.val, B.puncturedOpenRegion_not_singular y⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val

def regularSmallLink : C(Sphere 3, RegularParameters g) :=
  B.regularPuncturedInclusion.comp B.puncturedSphereEquiv.symm.toFun

def regularLink : C(Sphere 3, RegularParameters g) where
  toFun s := ⟨B.boundaryMap s, disjoint_left.mp B.boundaryRegion_disjoint_singular
    (show B.boundaryMap s ∈ B.boundaryRegion from ⟨s.val, s.property, rfl⟩)⟩
  continuous_toFun := B.boundaryMap.continuous.subtype_mk _

def smallLinkHomotopy : B.regularSmallLink.Homotopy B.regularLink where
  toFun p := ⟨B.chart (boundaryAnnulus p), fun hs ↦ boundaryAnnulus_ne_zero p
    ((B.singular_iff _ (boundaryAnnulus_mem_closedBall p)).mp hs)⟩
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

theorem regularSmallLink_homologyMap (n : ℕ) :
    singularHomologyMap B.regularSmallLink n = singularHomologyMap B.regularLink n :=
  homotopy_homologyMap B.smallLinkHomotopy n

end NoExoticSixSphere.SphereFamily.ParityBall
