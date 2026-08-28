import Wikipedia.NoExoticSixSphere.FourAnnulusSinglePunctureCover
import Wikipedia.NoExoticSixSphere.MayerVietorisLeftEquiv
import Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Actual one-point overlap homology equivalences for annulus singularities

The original ball union has zero positive homology by its actual disjoint
union of contractible chart balls. In each one-point comparison the ambient
space is all of Euclidean space, so the literal overlap inclusion is an
isomorphism. No such isomorphism is claimed for the whole annulus complement.
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

def singleOverlapInclusionEquiv (x : singularSet g) (n : ℕ) (hn : n ≠ 0) :
    SingularHomology (singleComplementSet g x ∩ P.openHoles : Set (Vector 4)) n ≃ₗ[ℤ]
      SingularHomology (singleComplementSet g x) n := by
  let := contractible_homology_subsingleton (Vector 4) n hn
  let := contractible_homology_subsingleton (Vector 4) (n + 1) (Nat.succ_ne_zero n)
  let := P.openHoles_homology_subsingleton n hn
  exact MayerVietorisVanishing.leftInclusionEquiv (singleComplementSet g x) P.openHoles
    (isOpen_singleComplementSet g x) P.isOpen_openHoles (P.single_complement_cover x) n

theorem singleOverlapInclusionEquiv_apply (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (singleComplementSet g x ∩ P.openHoles : Set (Vector 4)) n) :
    P.singleOverlapInclusionEquiv x n hn a =
      singularHomologyMap (ContinuousMap.inclusion
        (inter_subset_left : singleComplementSet g x ∩ P.openHoles ⊆ singleComplementSet g x))
        n a := rfl

theorem overlapInclusion_comparison (x : singularSet g) (n : ℕ) (hn : n ≠ 0)
    (a : SingularHomology (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) n) :
    singularHomologyMap (complementToSingle g x) n
      (singularHomologyMap (ContinuousMap.inclusion (inter_subset_left :
        singularComplementSet g ∩ P.openHoles ⊆ singularComplementSet g)) n a) =
      P.singleOverlapInclusionEquiv x n hn
        (singularHomologyMap (P.globalToSingleIntersection x) n a) := by
  rw [P.singleOverlapInclusionEquiv_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, ← singularHomologyMap_comp]
  rfl

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
