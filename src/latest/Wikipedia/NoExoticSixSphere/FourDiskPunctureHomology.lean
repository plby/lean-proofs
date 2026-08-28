import Wikipedia.NoExoticSixSphere.FourDiskPunctureCover
import Wikipedia.NoExoticSixSphere.MayerVietorisLeftEquiv
import Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Actual overlap-to-complement homology isomorphisms for the disk punctures

The original open balls are contractible, so their actual disjoint union
has zero positive homology. The ambient Euclidean space is contractible.
Mayer--Vietoris therefore makes the literal global and one-point overlap
inclusions isomorphisms. Their comparison is the original inclusion map.
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

theorem openHoles_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularHomology P.openHoles n) := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (singularSet g)
  let (x : singularSet g) : ContractibleSpace (P.ball x).openRegion :=
    (P.ball x).openRegion_contractible
  let (x : singularSet g) : Subsingleton (SingularHomology (P.ball x).openRegion n) :=
    contractible_homology_subsingleton _ n hn
  let : Subsingleton (SingularHomology (Σ x, (P.ball x).openRegion) n) :=
    (sigmaHomologyEquiv (fun x ↦ (P.ball x).openRegion) n).injective.subsingleton
  exact (homeomorphHomologyEquiv P.openHolesHomeomorph.symm n).injective.subsingleton

def overlapInclusionEquiv (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n ≃ₗ[ℤ]
      SingularHomology (SingularComplement g) n := by
  let := contractible_homology_subsingleton (Vector 4) n hn
  let := contractible_homology_subsingleton (Vector 4) (n + 1) (Nat.succ_ne_zero n)
  let := P.openHoles_homology_subsingleton n hn
  exact MayerVietorisVanishing.leftInclusionEquiv (singularComplementSet g) P.openHoles
    P.isOpen_singularComplementSet P.isOpen_openHoles P.singular_complement_cover n

def singleOverlapInclusionEquiv (x : singularSet g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (singleComplementSet g x ∩ P.openHoles : Set (Vector 4)) n ≃ₗ[ℤ]
      SingularHomology (singleComplementSet g x) n := by
  let := contractible_homology_subsingleton (Vector 4) n hn
  let := contractible_homology_subsingleton (Vector 4) (n + 1) (Nat.succ_ne_zero n)
  let := P.openHoles_homology_subsingleton n hn
  exact MayerVietorisVanishing.leftInclusionEquiv (singleComplementSet g x) P.openHoles
    (isOpen_singleComplementSet g x) P.isOpen_openHoles (P.single_complement_cover x) n

theorem overlapInclusionEquiv_apply (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n) :
    P.overlapInclusionEquiv n hn a =
      singularHomologyMap (ContinuousMap.inclusion
        (inter_subset_left : singularComplementSet g ∩ P.openHoles ⊆ singularComplementSet g))
        n a :=
  rfl

theorem singleOverlapInclusionEquiv_apply (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (singleComplementSet g x ∩ P.openHoles : Set (Vector 4)) n) :
    P.singleOverlapInclusionEquiv x n hn a =
      singularHomologyMap (ContinuousMap.inclusion
        (inter_subset_left : singleComplementSet g x ∩ P.openHoles ⊆ singleComplementSet g x))
        n a :=
  rfl

theorem overlapInclusionEquiv_comparison (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n) :
    singularHomologyMap (complementToSingle g x) n (P.overlapInclusionEquiv n hn a) =
      P.singleOverlapInclusionEquiv x n hn
        (singularHomologyMap (P.globalToSingleIntersection x) n a) := by
  rw [P.overlapInclusionEquiv_apply, P.singleOverlapInclusionEquiv_apply,
    ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, ← singularHomologyMap_comp]
  rfl

end NoExoticSixSphere.GenericFourDisk.ParityBallSystem
