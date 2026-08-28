import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionSurjective
import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionNaturality
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationSingular

/-!
# Torsion duality for the original integral singular cohomology

The literal simplex bases discharge all chain-freeness inputs. If the
original H_n is finite and H_(n+1) vanishes, the constructed original
torsion evaluation is a linear equivalence. Its original bounding-chain
formula and continuous-map naturality are retained.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree

variable (X : Type) [TopologicalSpace X] (n : ℕ)
  [Finite (SingularHomology X n)] [Subsingleton (SingularHomology X (n + 1))]

def singularTorsionEvaluation :
    SingularCohomology X (n + 1) →ₗ[ℤ] (SingularHomology X n →ₗ[ℤ] RationalResidue.Value) :=
  torsionEvaluation (singularComplex X) n

theorem singularTorsionEvaluation_bijective :
    Function.Bijective (singularTorsionEvaluation X n) := by
  let (j : ℕ) : Module.Free ℤ ((singularComplex X).X j) := Module.Free.of_basis (chainBasis X j)
  exact torsionEvaluation_bijective (singularComplex X) n

def singularTorsionEvaluationEquiv :
    SingularCohomology X (n + 1) ≃ₗ[ℤ] (SingularHomology X n →ₗ[ℤ] RationalResidue.Value) :=
  LinearEquiv.ofBijective (singularTorsionEvaluation X n) (singularTorsionEvaluation_bijective X n)

theorem singularTorsionEvaluationEquiv_toLinearMap :
    (singularTorsionEvaluationEquiv X n).toLinearMap = singularTorsionEvaluation X n := rfl

theorem singularTorsionEvaluation_bounding_formula
    (c : Cocycle (dualComplex (singularComplex X)) (n + 1))
    (z : ModuleHomology.Cycle (singularComplex X) n) (l : ℤ) (hl : l ≠ 0)
    (b : (singularComplex X).X (n + 1))
    (hb : ((singularComplex X).d (n + 1) n).hom b = l • z.val) :
    singularTorsionEvaluation X n
      (cocycleClass (dualComplex (singularComplex X)) (n + 1) c)
      (ModuleHomology.cycleClass (singularComplex X) n z) =
        RationalResidue.residue ((c.val b : ℚ) / (l : ℚ)) :=
  torsionEvaluation_bounding_formula (singularComplex X) n c z l hl b hb

variable {X n}
variable {Y : Type} [TopologicalSpace Y]
  [Finite (SingularHomology Y n)] [Subsingleton (SingularHomology Y (n + 1))]

theorem singularTorsionEvaluation_naturality (f : C(X, Y))
    (a : SingularCohomology Y (n + 1)) (b : SingularHomology X n) :
    singularTorsionEvaluation X n (singularCohomologyPullback f (n + 1) a) b =
      singularTorsionEvaluation Y n a (singularHomologyMap f n b) :=
  torsionEvaluation_naturality (singularChainMap f) n a b

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
