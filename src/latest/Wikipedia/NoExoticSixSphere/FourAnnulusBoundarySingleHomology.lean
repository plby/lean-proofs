import Wikipedia.NoExoticSixSphere.FourAnnulusSinglePunctureHomology
import Wikipedia.NoExoticSixSphere.EnclosingSphereShift

/-!
# The actual two boundary spheres in each one-point comparison

Every original annulus singularity is strictly inside the radius-two
sphere and strictly outside the unit ball. The ORIGINAL outer sphere
therefore generates its one-point complement, whereas the ORIGINAL inner
sphere extends across the unit disk there and has zero positive homology.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

def outerToSingle (x : singularSet g) : C(Sphere 3, singleComplementSet g x) :=
  (complementToSingle g x).comp P.complementOuterBoundary

def innerToSingle (x : singularSet g) : C(Sphere 3, singleComplementSet g x) :=
  (complementToSingle g x).comp P.complementInnerBoundary

theorem outerToSingle_value (x : singularSet g) (q : Sphere 3) :
    (P.outerToSingle x q).val = (2 : ℝ) • q.val := rfl

theorem innerToSingle_value (x : singularSet g) (q : Sphere 3) :
    (P.innerToSingle x q).val = q.val := rfl

theorem outerToSingle_homology_bijective (x : singularSet g) (n : ℕ) :
    Bijective (singularHomologyMap (P.outerToSingle x) n) := by
  have hx : ‖x.val‖ < 2 := (P.singular_subset_interior x.property).2
  let L := BallExterior.puncturedTranslate x.val
  let LC : C(singleComplementSet g x,
      Wikipedia.SmoothSixDPoincare.PuncturedRadial.Space (Vector 4)) := L
  have he : LC.comp (P.outerToSingle x) =
      BallExterior.shiftedSphereMap 2 (by norm_num) x.val hx := by
    apply ContinuousMap.ext
    intro q
    rfl
  have hcomp : Bijective ((singularHomologyMap LC n).comp
      (singularHomologyMap (P.outerToSingle x) n)) := by
    rw [← singularHomologyMap_comp, he]
    exact BallExterior.shiftedSphereMap_homology_bijective 2 (by norm_num) x.val hx n
  constructor
  · intro a b hab
    exact hcomp.injective (congrArg (singularHomologyMap LC n) hab)
  · intro b
    obtain ⟨a, ha⟩ := hcomp.surjective (singularHomologyMap LC n b)
    exact ⟨a, (homeomorphHomologyEquiv L n).injective ha⟩

def outerSingleEquiv (x : singularSet g) (n : ℕ) :
    SingularHomology (Sphere 3) n ≃ₗ[ℤ] SingularHomology (singleComplementSet g x) n :=
  LinearEquiv.ofBijective (singularHomologyMap (P.outerToSingle x) n)
    (P.outerToSingle_homology_bijective x n)

theorem outerSingleEquiv_apply (x : singularSet g) (n : ℕ) (a : SingularHomology (Sphere 3) n) :
    P.outerSingleEquiv x n a = singularHomologyMap (P.outerToSingle x) n a := rfl

include P in
theorem innerDisk_point_ne (x : singularSet g) (y : closedBall (0 : Vector 4) 1) :
    y.val ≠ x.val := by
  intro he
  have hy : ‖y.val‖ ≤ (1 : ℝ) := mem_closedBall_zero_iff.mp y.property
  have hxy : ‖x.val‖ ≤ 1 := (congrArg norm he).symm.trans_le hy
  exact (not_le_of_gt (P.singular_subset_interior x.property).1) hxy

def innerDiskToSingle (x : singularSet g) :
    C(closedBall (0 : Vector 4) 1, singleComplementSet g x) where
  toFun y := ⟨y.val, P.innerDisk_point_ne x y⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

theorem innerToSingle_homologyMap_zero (x : singularSet g) (n : ℕ) (hn : n ≠ 0) :
    singularHomologyMap (P.innerToSingle x) n = 0 := by
  let : ContractibleSpace (closedBall (0 : Vector 4) 1) :=
    (convex_closedBall (0 : Vector 4) 1).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩
  let := contractible_homology_subsingleton (closedBall (0 : Vector 4) 1) n hn
  let b : C(Sphere 3, closedBall (0 : Vector 4) 1) := {
    toFun q := ⟨q.val, sphere_subset_closedBall q.property⟩
    continuous_toFun := continuous_subtype_val.subtype_mk _ }
  have he : P.innerToSingle x = (P.innerDiskToSingle x).comp b :=
    ContinuousMap.ext (fun _ ↦ rfl)
  have hb : singularHomologyMap b n = 0 := LinearMap.ext (fun _ ↦ Subsingleton.elim _ _)
  rw [he, singularHomologyMap_comp, hb, LinearMap.comp_zero]

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
