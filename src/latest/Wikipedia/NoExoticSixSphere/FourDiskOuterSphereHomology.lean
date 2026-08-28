import Wikipedia.NoExoticSixSphere.FourDiskPunctureHomology
import Wikipedia.NoExoticSixSphere.EnclosingSphereShift

/-!
# The original outer sphere generates every one-point complement

Every original native singular point lies strictly inside the unit disk.
Translation of that point to zero turns the original outer inclusion into
the checked enclosing-sphere map. Its actual homotopy proves that this
inclusion induces an isomorphism on integral homology in every degree.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBallSystem

open GLOrthonormalization DiskDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

def outerToSingle (x : singularSet g) : C(Sphere 3, singleComplementSet g x) :=
  (complementToSingle g x).comp P.complementOuterBoundary

theorem outerToSingle_value (x : singularSet g) (s : Sphere 3) :
    (P.outerToSingle x s).val = s.val := rfl

theorem outerToSingle_homology_bijective (x : singularSet g) (n : ℕ) :
    Bijective (singularHomologyMap (P.outerToSingle x) n) := by
  have hx : ‖x.val‖ < 1 := mem_ball_zero_iff.mp (P.singular_subset_interior x.property)
  let L := BallExterior.puncturedTranslate x.val
  let LC : C(singleComplementSet g x,
      Wikipedia.SmoothSixDPoincare.PuncturedRadial.Space (Vector 4)) := L
  have he : LC.comp (P.outerToSingle x) =
      BallExterior.shiftedSphereMap 1 zero_lt_one x.val hx := by
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    change s.val - x.val = (1 : ℝ) • s.val - x.val
    rw [one_smul]
  have hcomp : Bijective ((singularHomologyMap LC n).comp
      (singularHomologyMap (P.outerToSingle x) n)) := by
    rw [← singularHomologyMap_comp, he]
    exact BallExterior.shiftedSphereMap_homology_bijective 1 zero_lt_one x.val hx n
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

end NoExoticSixSphere.GenericFourDisk.ParityBallSystem
