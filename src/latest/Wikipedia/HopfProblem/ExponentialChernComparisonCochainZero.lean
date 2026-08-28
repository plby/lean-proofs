import Wikipedia.HopfProblem.HolomorphicExponentialSheafIntegersInclusion
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCoefficientSheaf

/-!
# Holomorphic functions evaluated on actual singular vertices

The map to the degree-zero singular cochain sheaf first evaluates the original
holomorphic section at each singular vertex, extends these values along the
actual singular-chain basis, and then applies the native sheafification unit.
The integer inclusion of the ordinary exponential sequence agrees with the
constant-cochain augmentation after the literal coefficient map `n ↦ 2πin`.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ExponentialChernComparison.CochainZero

open FirstHurewicz ConstantSheafSingularComparison

/-- The actual coefficient homomorphism for the ordinary complex exponential. -/
def integerCoefficient : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℂ :=
  AddCommGrpCat.ofHom HolomorphicExponentialSheaf.integerScalarHom

@[simp] theorem integerCoefficient_apply (n : ℤ) :
    integerCoefficient n = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := rfl

/-- The native constant-sheaf functor applied to the actual integer-period map. -/
def integerCoefficientMap (X : TopCat.{0}) :
    HolomorphicExponentialSheaf.integerSheaf X ⟶
      ConstantSheafFirstCohomology.Constant.sheaf X (AddCommGrpCat.of ℂ) :=
  (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).map
    integerCoefficient

/-- The coefficient map sends each original integer-unit representative to
the complex-unit representative of the same actual exponential period. -/
@[simp] theorem integerCoefficientMap_app_unit (X : TopCat.{0})
    (U : Opens X) (n : ℤ) :
    (integerCoefficientMap X).hom.app (op U)
        ((HolomorphicExponentialSheaf.integerUnit X).app (op U) n) =
      (ConstantSheafFirstCohomology.Constant.unit X (AddCommGrpCat.of ℂ)).app (op U)
        (integerCoefficient n) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (constantUnit_coefficient_naturality X integerCoefficient) (op U)) n

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Literal evaluation of a holomorphic section on each original singular
vertex, extended additively on the original integral singular chains. -/
def evaluateSections (U : Opens M) :
    HolomorphicFunctionSheaf.Section I M U →+ Cochains U (AddCommGrpCat.of ℂ) 0 where
  toFun s := cochainFromValues U (AddCommGrpCat.of ℂ) 0
    (fun σ => s (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))))
  map_zero' := by
    apply cochain_ext U (AddCommGrpCat.of ℂ) 0
    intro σ
    exact cochainFromValues_simplex U (AddCommGrpCat.of ℂ) 0 (fun _ => 0) σ
  map_add' s t := by
    apply cochain_ext U (AddCommGrpCat.of ℂ) 0
    intro σ
    exact (cochainFromValues_simplex U (AddCommGrpCat.of ℂ) 0
      (fun τ => (s + t) (τ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))) σ).trans
        (congrArg₂ (fun a b : ℂ => a + b)
          (cochainFromValues_simplex U (AddCommGrpCat.of ℂ) 0
            (fun τ => s (τ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))) σ).symm
          (cochainFromValues_simplex U (AddCommGrpCat.of ℂ) 0
            (fun τ => t (τ (stdSimplex.vertex (S := ℝ) (0 : Fin 1)))) σ).symm)

@[simp] theorem evaluateSections_simplex (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M U) (σ : SingularSimplex U 0) :
    evaluateSections I M U s (simplexChain U 0 σ) =
      s (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))) :=
  cochainFromValues_simplex U (AddCommGrpCat.of ℂ) 0 _ σ

/-- Actual holomorphic constant sections give actual constant zero-cochains. -/
@[simp] theorem evaluateSections_constant (U : Opens M) (z : ℂ) :
    evaluateSections I M U
        (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U) z) =
      constantCochain U (AddCommGrpCat.of ℂ) z := rfl

/-- Vertex evaluation commutes with the original open-set restriction maps. -/
def evaluatePresheaf : (HolomorphicFunctionSheaf.additiveSheaf I M).obj ⟶
    cochainPresheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 0 where
  app U := AddCommGrpCat.ofHom (evaluateSections I M U.unop)
  naturality U V i := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    apply cochain_ext V.unop (AddCommGrpCat.of ℂ) 0
    intro σ
    exact (evaluateSections_simplex I M V.unop
      ((HolomorphicFunctionSheaf.additiveSheaf I M).obj.map i s) σ).trans
        (((cochainPresheaf_map_simplex (TopCat.of M) (AddCommGrpCat.of ℂ) 0 i.unop
          (evaluateSections I M U.unop s) σ).trans
            (evaluateSections_simplex I M U.unop s
              (((Opens.toTopCat (TopCat.of M)).map i.unop).hom.comp σ))).symm)

@[simp] theorem evaluatePresheaf_app (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M U) :
    (evaluatePresheaf I M).app (op U) s = evaluateSections I M U s := rfl

/-- Evaluation into the actual sheafification of native singular zero-cochains. -/
def evaluate : HolomorphicFunctionSheaf.additiveSheaf I M ⟶
    cochainSheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 0 where
  hom := evaluatePresheaf I M ≫ cochainSheafUnit (TopCat.of M) (AddCommGrpCat.of ℂ) 0

@[simp] theorem evaluate_app (U : Opens M)
    (s : HolomorphicFunctionSheaf.Section I M U) :
    (evaluate I M).hom.app (op U) s =
      (cochainSheafUnit (TopCat.of M) (AddCommGrpCat.of ℂ) 0).app (op U)
        (evaluateSections I M U s) := rfl

/-- On every actual holomorphic constant, evaluation is the original unit
applied to the original constant singular cochain. -/
@[simp] theorem evaluate_constant (U : Opens M) (z : ℂ) :
    (evaluate I M).hom.app (op U)
        (algebraMap ℂ (HolomorphicFunctionSheaf.Section I M U) z) =
      (cochainSheafUnit (TopCat.of M) (AddCommGrpCat.of ℂ) 0).app (op U)
        (constantCochain U (AddCommGrpCat.of ℂ) z) := rfl

/-- The actual ordinary-exponential integer inclusion and the original
constant-cochain augmentation form a commuting square of native sheaves. -/
@[reassoc] theorem integerInclusion_evaluate :
    HolomorphicExponentialSheaf.integerInclusion I M ≫ evaluate I M =
      integerCoefficientMap (TopCat.of M) ≫
        sheafAugmentation (TopCat.of M) (AddCommGrpCat.of ℂ) := by
  apply HolomorphicExponentialSheaf.integerHom_ext_on_constants
  intro U n
  change (evaluate I M).hom.app (op U)
      ((HolomorphicExponentialSheaf.integerInclusion I M).hom.app (op U)
        ((HolomorphicExponentialSheaf.integerUnit (TopCat.of M)).app (op U) n)) =
    (sheafAugmentation (TopCat.of M) (AddCommGrpCat.of ℂ)).hom.app (op U)
      ((integerCoefficientMap (TopCat.of M)).hom.app (op U)
        ((HolomorphicExponentialSheaf.integerUnit (TopCat.of M)).app (op U) n))
  rw [HolomorphicExponentialSheaf.integerInclusion_app_unit, evaluate_constant,
    integerCoefficientMap_app_unit]
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (constantUnit_sheafAugmentation (TopCat.of M) (AddCommGrpCat.of ℂ)) (op U))
    (integerCoefficient n)).symm

end Wikipedia.HopfProblem.ExponentialChernComparison.CochainZero
