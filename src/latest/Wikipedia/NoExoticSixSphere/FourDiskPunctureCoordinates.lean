import Wikipedia.NoExoticSixSphere.FourDiskOuterSphereHomology
import Wikipedia.NoExoticSixSphere.PiSingleCoordinate

/-!
# Actual homology coordinates of the finite-point complement

The original overlap coproduct and Mayer--Vietoris inclusion give genuine
coordinates in the homology of the singular complement. In a one-point
comparison only the selected component survives. The original outer
sphere maps isomorphically onto each such coordinate.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBallSystem

open GLOrthonormalization DiskDoublePoints
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

def complementCoordinates (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (SingularComplement g) n ≃ₗ[ℤ]
      (∀ x, SingularHomology (P.puncturedPiece x) n) :=
  (P.overlapInclusionEquiv n hn).symm.trans (P.overlapHomologyEquiv n)

omit [Fintype (singularSet g)] in
theorem overlapInclusionEquiv_symm_comparison (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (SingularComplement g) n) :
    (P.singleOverlapInclusionEquiv x n hn).symm
      (singularHomologyMap (complementToSingle g x) n a) =
        singularHomologyMap (P.globalToSingleIntersection x) n
          ((P.overlapInclusionEquiv n hn).symm a) := by
  apply (P.singleOverlapInclusionEquiv x n hn).injective
  rw [LinearEquiv.apply_symm_apply, ← P.overlapInclusionEquiv_comparison,
    LinearEquiv.apply_symm_apply]

def componentOuterEquiv (x : singularSet g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (Sphere 3) n ≃ₗ[ℤ] SingularHomology (P.puncturedPiece x) n :=
  (P.outerSingleEquiv x n).trans
    ((P.singleOverlapInclusionEquiv x n hn).symm.trans
      (P.singleOverlapCoordinateEquiv x n hn))

theorem componentOuterEquiv_apply (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (Sphere 3) n) :
    P.componentOuterEquiv x n hn a =
      P.complementCoordinates n hn (singularHomologyMap P.complementOuterBoundary n a) x := by
  change P.singleOverlapCoordinateEquiv x n hn
    ((P.singleOverlapInclusionEquiv x n hn).symm (P.outerSingleEquiv x n a)) = _
  rw [P.outerSingleEquiv_apply, outerToSingle, singularHomologyMap_comp, LinearMap.comp_apply,
    P.overlapInclusionEquiv_symm_comparison]
  exact P.singleOverlapCoordinateEquiv_comparison x n hn _

def puncturedPieceInclusion (x : singularSet g) : C(P.puncturedPiece x, SingularComplement g) :=
  ContinuousMap.inclusion inter_subset_left

theorem overlapHomologyEquiv_inclusion (n : ℕ)
    (a : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n) :
    singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_left :
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

theorem sum_complementCoordinates (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (SingularComplement g) n) :
    a = ∑ x, singularHomologyMap (P.puncturedPieceInclusion x) n
      (P.complementCoordinates n hn a x) := by
  have h := P.overlapHomologyEquiv_inclusion n ((P.overlapInclusionEquiv n hn).symm a)
  change P.overlapInclusionEquiv n hn ((P.overlapInclusionEquiv n hn).symm a) =
    ∑ x, singularHomologyMap (P.puncturedPieceInclusion x) n
      (P.complementCoordinates n hn a x) at h
  rwa [LinearEquiv.apply_symm_apply] at h

end NoExoticSixSphere.GenericFourDisk.ParityBallSystem
