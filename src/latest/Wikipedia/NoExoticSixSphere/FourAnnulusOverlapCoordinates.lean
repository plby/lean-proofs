import Wikipedia.NoExoticSixSphere.FourAnnulusBoundarySingleHomology
import Wikipedia.NoExoticSixSphere.AnnulusBoundaryDifferenceLift
import Wikipedia.NoExoticSixSphere.PiSingleCoordinate

/-!
# Actual linking coordinates of an original annulus boundary-difference lift

The retained disjoint overlap gives native homology coordinates. In each
one-point comparison only the selected component contributes. Any actual
Mayer--Vietoris lift of outer-minus-inner has that component equal to the
original outer-sphere generator. No coordinates for the entire singular
complement are asserted or required.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

theorem singlePiece_homology_subsingleton (x y : singularSet g) (hne : x ≠ y)
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (SingularHomology (P.singlePiece x y) n) := by
  rw [P.singlePiece_other x y hne]
  let := (P.ball y).openRegion_contractible
  exact contractible_homology_subsingleton _ n hn

theorem overlap_comparison_map (x : singularSet g) :
    ((P.singleOverlapHomeomorph x).symm : C(_, _)).comp
      ((P.globalToSingleIntersection x).comp (P.overlapHomeomorph : C(_, _))) =
        sigmaMap (P.overlapComponentMap x) := by
  apply ContinuousMap.ext
  intro y
  apply (P.singleOverlapHomeomorph x).injective
  change P.singleOverlapHomeomorph x
    ((P.singleOverlapHomeomorph x).symm
      (P.globalToSingleIntersection x (P.overlapHomeomorph y))) = _
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext rfl

theorem boundaryDifference_toSingle (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (Sphere 3) n) :
    singularHomologyMap (complementToSingle g x) n (P.boundaryDifference n a) =
      P.outerSingleEquiv x n a := by
  rw [boundaryDifference, map_sub, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, ← singularHomologyMap_comp]
  change singularHomologyMap (P.outerToSingle x) n a -
    singularHomologyMap (P.innerToSingle x) n a = P.outerSingleEquiv x n a
  rw [P.innerToSingle_homologyMap_zero x n hn, LinearMap.zero_apply, sub_zero]
  rfl

variable [Fintype (singularSet g)]

def overlapHomologyEquiv (n : ℕ) :
    SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n ≃ₗ[ℤ]
      (∀ x, SingularHomology (P.puncturedPiece x) n) :=
  (homeomorphHomologyEquiv P.overlapHomeomorph.symm n).trans
    (sigmaHomologyEquiv (fun x ↦ P.puncturedPiece x) n)

def singleOverlapHomologyEquiv (x : singularSet g) (n : ℕ) :
    SingularHomology (singleComplementSet g x ∩ P.openHoles : Set (Vector 4)) n ≃ₗ[ℤ]
      (∀ y, SingularHomology (P.singlePiece x y) n) :=
  (homeomorphHomologyEquiv (P.singleOverlapHomeomorph x).symm n).trans
    (sigmaHomologyEquiv (fun y ↦ P.singlePiece x y) n)

theorem singleOverlapHomologyEquiv_comparison (x : singularSet g) (n : ℕ)
    (a : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n) :
    P.singleOverlapHomologyEquiv x n
      (singularHomologyMap (P.globalToSingleIntersection x) n a) =
        fun y ↦ singularHomologyMap (P.overlapComponentMap x y) n
          (P.overlapHomologyEquiv n a y) := by
  let b := (homeomorphHomologyEquiv P.overlapHomeomorph n).symm a
  have hb : singularHomologyMap (P.overlapHomeomorph : C(_, _)) n b = a :=
    (homeomorphHomologyEquiv P.overlapHomeomorph n).apply_symm_apply a
  have h := congrArg (fun f ↦ singularHomologyMap f n b) (P.overlap_comparison_map x)
  simp only [singularHomologyMap_comp, LinearMap.comp_apply] at h
  rw [hb] at h
  change sigmaHomologyEquiv (fun y ↦ P.singlePiece x y) n
    (singularHomologyMap ((P.singleOverlapHomeomorph x).symm : C(_, _)) n
      (singularHomologyMap (P.globalToSingleIntersection x) n a)) = _
  rw [h, sigmaHomologyEquiv_sigmaMap]
  rfl

def singleOverlapCoordinateEquiv (x : singularSet g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (singleComplementSet g x ∩ P.openHoles : Set (Vector 4)) n ≃ₗ[ℤ]
      SingularHomology (P.puncturedPiece x) n :=
  ((P.singleOverlapHomologyEquiv x n).trans
    (PiSingleCoordinate.equiv (fun y ↦ SingularHomology (P.singlePiece x y) n) x
      (fun y hyx ↦ P.singlePiece_homology_subsingleton x y (Ne.symm hyx) n hn))).trans
        (homeomorphHomologyEquiv (Homeomorph.setCongr (P.singlePiece_same x)) n)

theorem singleOverlapCoordinateEquiv_comparison (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n) :
    P.singleOverlapCoordinateEquiv x n hn
      (singularHomologyMap (P.globalToSingleIntersection x) n a) =
        P.overlapHomologyEquiv n a x := by
  change homeomorphHomologyEquiv (Homeomorph.setCongr (P.singlePiece_same x)) n
    (P.singleOverlapHomologyEquiv x n
      (singularHomologyMap (P.globalToSingleIntersection x) n a) x) = _
  rw [P.singleOverlapHomologyEquiv_comparison]
  dsimp only
  rw [P.overlapComponentMap_self]
  exact (homeomorphHomologyEquiv (Homeomorph.setCongr (P.singlePiece_same x)) n).apply_symm_apply
    (P.overlapHomologyEquiv n a x)

def componentBoundaryDifferenceEquiv (x : singularSet g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (Sphere 3) n ≃ₗ[ℤ] SingularHomology (P.puncturedPiece x) n :=
  (P.outerSingleEquiv x n).trans
    ((P.singleOverlapInclusionEquiv x n hn).symm.trans
      (P.singleOverlapCoordinateEquiv x n hn))

theorem componentBoundaryDifferenceEquiv_of_lift (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (Sphere 3) n)
    (b : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n)
    (hb : singularHomologyMap (ContinuousMap.inclusion (inter_subset_left :
      singularComplementSet g ∩ P.openHoles ⊆ singularComplementSet g)) n b =
        P.boundaryDifference n a) :
    P.componentBoundaryDifferenceEquiv x n hn a = P.overlapHomologyEquiv n b x := by
  have h := P.overlapInclusion_comparison x n hn b
  rw [hb, P.boundaryDifference_toSingle x n hn a] at h
  change P.singleOverlapCoordinateEquiv x n hn
    ((P.singleOverlapInclusionEquiv x n hn).symm (P.outerSingleEquiv x n a)) = _
  rw [h, LinearEquiv.symm_apply_apply]
  exact P.singleOverlapCoordinateEquiv_comparison x n hn b

def puncturedPieceInclusion (x : singularSet g) : C(P.puncturedPiece x, SingularComplement g) :=
  ContinuousMap.inclusion inter_subset_left

theorem overlapHomologyEquiv_inclusion (n : ℕ)
    (a : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n) :
    singularHomologyMap (ContinuousMap.inclusion (inter_subset_left :
      singularComplementSet g ∩ P.openHoles ⊆ singularComplementSet g)) n a =
        ∑ x, singularHomologyMap (P.puncturedPieceInclusion x) n
          (P.overlapHomologyEquiv n a x) := by
  let b := (homeomorphHomologyEquiv P.overlapHomeomorph n).symm a
  let inclusion : C((singularComplementSet g ∩ P.openHoles : Set (Vector 4)),
      SingularComplement g) := ContinuousMap.inclusion inter_subset_left
  have h := sigmaHomologyEquiv_map_out
    (inclusion.comp (P.overlapHomeomorph : C(_, _))) n b
  rw [singularHomologyMap_comp, LinearMap.comp_apply] at h
  have hb : singularHomologyMap (P.overlapHomeomorph : C(_, _)) n b = a :=
    (homeomorphHomologyEquiv P.overlapHomeomorph n).apply_symm_apply a
  rw [hb] at h
  exact h

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
