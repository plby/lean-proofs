import Wikipedia.NoExoticSixSphere.CompactManifoldHomologyFinite
import Wikipedia.NoExoticSixSphere.TwoConnectedCoefficientReduction
import Wikipedia.NoExoticSixSphere.ModHomologyModule
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The actual mod-two middle homology is a finite vector space

Finite generation comes from the constructed Morse sequence of the original
compact smooth manifold. For a two-connected target, the exact coefficient
sequence makes reduction onto mod-two middle homology surjective. The finite
coefficient field then makes that actual homology type finite.
-/

noncomputable section

open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
  (m : M) [h₂ : Subsingleton (π_ 2 M m)]

include E m h₂

theorem compactManifold_modTwoMiddleHomology_finite :
    Module.Finite (ZMod 2) (ModHomology 2 M 3) := by
  let : Module.Finite ℤ (SingularHomology M 3) := compactManifold_middleHomology_finite E M
  let : Module.Finite ℤ (ModHomology 2 M 3) :=
    Module.Finite.of_surjective (reductionHomologyMap 2 M 3)
      (TwoConnectedCoefficients.middleReduction_surjective m)
  refine @Module.Finite.of_restrictScalars_finite ℤ (ZMod 2) (ModHomology 2 M 3)
    inferInstance inferInstance inferInstance inferInstance (modHomologyModule 2 M 3)
    inferInstance ?_ inferInstance
  refine @IsScalarTower.mk ℤ (ZMod 2) (ModHomology 2 M 3) inferInstance
    (modHomologyModule 2 M 3).toSMul (ModHomology 2 M 3).isModule.toSMul ?_
  intro n a x
  change (n • a) • x = (ModHomology 2 M 3).isModule.smul n (a • x)
  calc
    (n • a) • x = (n : ZMod 2) • (a • x) := by rw [zsmul_eq_mul, mul_smul]
    _ = n • (a • x) := Int.cast_smul_eq_zsmul (ZMod 2) n (a • x)
    _ = (ModHomology 2 M 3).isModule.smul n (a • x) :=
      (int_smul_eq_zsmul (ModHomology 2 M 3).isModule n (a • x)).symm

theorem compactManifold_modTwoMiddleHomology_finiteType : Finite (ModHomology 2 M 3) := by
  let := compactManifold_modTwoMiddleHomology_finite E M m
  exact Module.finite_of_finite (ZMod 2)

end NoExoticSixSphere
