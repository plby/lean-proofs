import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureContractible
import Wikipedia.NoExoticSixSphere.OpenDisjointUnion
import Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Positive homology vanishing for the actual puncture neighborhoods

The literal neighborhood union has the actual finite coproduct topology.
Its component contractions therefore imply vanishing of every positive
integral homology group. The same vanishing holds for each genuine one-point
complement by its stereographic coordinates.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.ThreefoldHomologyStarCoproduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

theorem singlePunctureRegularSet_homology_subsingleton (g : ℝ → Sphere 3 → M)
    (i : ParityBallSystem.BoundaryIndex g) (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularHomology (singlePunctureRegularSet g i) n) := by
  let := singlePunctureRegularSet_contractible g i
  exact contractible_homology_subsingleton _ n hn

namespace ParityBallSystem

variable {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

def coverHomeomorph : (Σ i, P.coverPiece i) ≃ₜ P.coverRegion :=
  OpenDisjointUnion.homeomorph P.coverPiece P.isOpen_coverPiece P.pairwise_disjoint_coverPiece

theorem coverHomeomorph_apply (i : BoundaryIndex g) (x : P.coverPiece i) :
    (P.coverHomeomorph ⟨i, x⟩).val = x.val := rfl

theorem coverRegion_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (SingularHomology P.coverRegion n) := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (BoundaryIndex g)
  let (i : BoundaryIndex g) : ContractibleSpace (P.coverPiece i) := P.coverPiece_contractible i
  let (i : BoundaryIndex g) : Subsingleton (SingularHomology (P.coverPiece i) n) :=
    contractible_homology_subsingleton _ n hn
  let : Subsingleton (SingularHomology (Σ i, P.coverPiece i) n) :=
    (sigmaHomologyEquiv (fun i ↦ P.coverPiece i) n).injective.subsingleton
  exact (homeomorphHomologyEquiv P.coverHomeomorph.symm n).injective.subsingleton

end ParityBallSystem
end NoExoticSixSphere.SphereFamily
