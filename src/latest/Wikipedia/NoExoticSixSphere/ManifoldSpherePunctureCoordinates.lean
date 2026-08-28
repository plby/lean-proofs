import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureOverlaps
import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureConnecting
import Wikipedia.NoExoticSixSphere.PiSingleCoordinate

/-!
# Actual homology coordinates of the puncture overlaps

The one-point comparison is the componentwise inclusion of the actual
topological coproducts. Its only nonzero positive-degree coordinate is the
selected puncture. Consequently every coordinate of the global connecting
map is an isomorphism, not merely a nonzero homomorphism.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

theorem singlePiece_homology_subsingleton (i j : BoundaryIndex g) (hne : i ≠ j)
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (SingularHomology (P.singlePiece i j) n) := by
  rw [P.singlePiece_other i j hne]
  let := P.coverPiece_contractible j
  exact contractible_homology_subsingleton _ n hn

theorem overlap_comparison_map (i : BoundaryIndex g) :
    ((P.singleOverlapHomeomorph i).symm : C(_, _)).comp
      ((P.globalToSingleIntersection i).comp (P.overlapHomeomorph : C(_, _))) =
        sigmaMap (P.overlapComponentMap i) := by
  apply ContinuousMap.ext
  intro x
  apply (P.singleOverlapHomeomorph i).injective
  change P.singleOverlapHomeomorph i
    ((P.singleOverlapHomeomorph i).symm
      (P.globalToSingleIntersection i (P.overlapHomeomorph x))) = _
  rw [Homeomorph.apply_symm_apply]
  exact Subtype.ext rfl

variable [Fintype (BoundaryIndex g)]

def overlapHomologyEquiv (n : ℕ) :
    SingularHomology (sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)) n ≃ₗ[ℤ]
      (∀ i, SingularHomology (P.puncturedPiece i) n) :=
  (homeomorphHomologyEquiv P.overlapHomeomorph.symm n).trans
    (sigmaHomologyEquiv (fun i ↦ P.puncturedPiece i) n)

def singleOverlapHomologyEquiv (i : BoundaryIndex g) (n : ℕ) :
    SingularHomology (singlePunctureRegularSet g i ∩ P.coverRegion : Set (Sphere 4)) n ≃ₗ[ℤ]
      (∀ j, SingularHomology (P.singlePiece i j) n) :=
  (homeomorphHomologyEquiv (P.singleOverlapHomeomorph i).symm n).trans
    (sigmaHomologyEquiv (fun j ↦ P.singlePiece i j) n)

theorem singleOverlapHomologyEquiv_comparison (i : BoundaryIndex g) (n : ℕ)
    (a : SingularHomology (sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)) n) :
    P.singleOverlapHomologyEquiv i n
      (singularHomologyMap (P.globalToSingleIntersection i) n a) =
        fun j ↦ singularHomologyMap (P.overlapComponentMap i j) n
          (P.overlapHomologyEquiv n a j) := by
  let b := (homeomorphHomologyEquiv P.overlapHomeomorph n).symm a
  have hb : singularHomologyMap (P.overlapHomeomorph : C(_, _)) n b = a :=
    (homeomorphHomologyEquiv P.overlapHomeomorph n).apply_symm_apply a
  have h := congrArg (fun f ↦ singularHomologyMap f n b) (P.overlap_comparison_map i)
  simp only [singularHomologyMap_comp, LinearMap.comp_apply] at h
  rw [hb] at h
  change sigmaHomologyEquiv (fun j ↦ P.singlePiece i j) n
    (singularHomologyMap ((P.singleOverlapHomeomorph i).symm : C(_, _)) n
      (singularHomologyMap (P.globalToSingleIntersection i) n a)) = _
  rw [h, sigmaHomologyEquiv_sigmaMap]
  rfl

def singleOverlapCoordinateEquiv (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (singlePunctureRegularSet g i ∩ P.coverRegion : Set (Sphere 4)) n ≃ₗ[ℤ]
      SingularHomology (P.puncturedPiece i) n :=
  ((P.singleOverlapHomologyEquiv i n).trans
    (PiSingleCoordinate.equiv (fun j ↦ SingularHomology (P.singlePiece i j) n) i
      (fun j hji ↦ P.singlePiece_homology_subsingleton i j (Ne.symm hji) n hn))).trans
        (homeomorphHomologyEquiv (Homeomorph.setCongr (P.singlePiece_same i)) n)

theorem singleOverlapCoordinateEquiv_comparison (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)) n) :
    P.singleOverlapCoordinateEquiv i n hn
      (singularHomologyMap (P.globalToSingleIntersection i) n a) =
        P.overlapHomologyEquiv n a i := by
  change homeomorphHomologyEquiv (Homeomorph.setCongr (P.singlePiece_same i)) n
    (P.singleOverlapHomologyEquiv i n
      (singularHomologyMap (P.globalToSingleIntersection i) n a) i) = _
  rw [P.singleOverlapHomologyEquiv_comparison]
  dsimp only
  rw [P.overlapComponentMap_self]
  exact (homeomorphHomologyEquiv (Homeomorph.setCongr (P.singlePiece_same i)) n).apply_symm_apply
    (P.overlapHomologyEquiv n a i)

def componentConnectingEquiv (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (Sphere 4) (n + 1) ≃ₗ[ℤ] SingularHomology (P.puncturedPiece i) n :=
  (P.singleConnectingEquiv i n hn).trans (P.singleOverlapCoordinateEquiv i n hn)

theorem componentConnectingEquiv_apply (i : BoundaryIndex g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (Sphere 4) (n + 1)) :
    P.componentConnectingEquiv i n hn a =
      P.overlapHomologyEquiv n (P.globalConnectingMap n a) i := by
  change P.singleOverlapCoordinateEquiv i n hn (P.singleConnectingEquiv i n hn a) = _
  rw [← P.globalConnectingMap_to_single i n hn a]
  exact P.singleOverlapCoordinateEquiv_comparison i n hn _

def puncturedPieceInclusion (i : BoundaryIndex g) :
    C(P.puncturedPiece i, sphereRegularSet g) :=
  ContinuousMap.inclusion inter_subset_left

theorem overlapHomologyEquiv_inclusion (n : ℕ)
    (a : SingularHomology (sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)) n) :
    singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_left :
        sphereRegularSet g ∩ P.coverRegion ⊆ sphereRegularSet g)) n a =
      ∑ i, singularHomologyMap (P.puncturedPieceInclusion i) n
        (P.overlapHomologyEquiv n a i) := by
  let b := (homeomorphHomologyEquiv P.overlapHomeomorph n).symm a
  let inclusion : C((sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)), sphereRegularSet g) :=
    ContinuousMap.inclusion inter_subset_left
  have h := sigmaHomologyEquiv_map_out
    (inclusion.comp (P.overlapHomeomorph : C(_, _))) n b
  rw [singularHomologyMap_comp, LinearMap.comp_apply] at h
  have hb : singularHomologyMap (P.overlapHomeomorph : C(_, _)) n b = a :=
    (homeomorphHomologyEquiv P.overlapHomeomorph n).apply_symm_apply a
  rw [hb] at h
  exact h

/-- The actual component isomorphisms sum to zero after inclusion into the complement. -/
theorem sum_componentConnectingEquiv_inclusion_zero (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (Sphere 4) (n + 1)) :
    ∑ i, singularHomologyMap (P.puncturedPieceInclusion i) n
      (P.componentConnectingEquiv i n hn a) = 0 := by
  simp_rw [P.componentConnectingEquiv_apply]
  rw [← P.overlapHomologyEquiv_inclusion]
  exact P.globalConnectingMap_inclusion_zero n a

end NoExoticSixSphere.SphereFamily.ParityBallSystem
