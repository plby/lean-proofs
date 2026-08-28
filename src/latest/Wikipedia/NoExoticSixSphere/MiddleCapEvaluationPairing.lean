import Wikipedia.NoExoticSixSphere.NativeModTwoMiddleEvaluation
import Wikipedia.NoExoticSixSphere.CompactManifoldCapDuality
import Wikipedia.NoExoticSixSphere.ModHomologyModule
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.Field.ZMod

/-!
# The nondegenerate actual cap-evaluation pairing in dimension six

Invert the proved original global cap and evaluate the resulting
original cohomology class on native mod-two middle homology. Both
maps are the checked actual maps. Their bijectivity and the separating
dual of the native coefficient vector space prove nondegeneracy.

This file does not identify this pairing with the previously constructed
geometric intersection count. That comparison remains required before
deducing nondegeneracy of the geometric quadratic obstruction.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris
open scoped Topology

namespace NoExoticSixSphere.MiddleCapEvaluation

attribute [local instance] modHomologyModule

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = (3 + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [CompactSpace M] [SimplyConnectedSpace M] (m : M) [Subsingleton (π_ 2 M m)]

/-- Inverse original cap followed by original native mod-two evaluation. -/
def functionalEquiv : ModHomology 2 M 3 ≃ₗ[ℤ] (ModHomology 2 M 3 →ₗ[ℤ] ZMod 2) :=
  (ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl).symm.trans
    (NativeModTwoMiddleEvaluation.evaluationEquiv m)

/-- The integer-enriched pairing uses those original maps as its two-variable function. -/
def pairingInt : ModHomology 2 M 3 →ₗ[ℤ] ModHomology 2 M 3 →ₗ[ℤ] ZMod 2 :=
  (functionalEquiv (E := E) m).toLinearMap

/-- The same actual function, with the native finite-coefficient scalar structure. -/
def pairing : ModHomology 2 M 3 →ₗ[ZMod 2] ModHomology 2 M 3 →ₗ[ZMod 2] ZMod 2 :=
  ModTwoBilinear.scalarUpgrade (pairingInt (E := E) m)

theorem pairing_apply (a b : ModHomology 2 M 3) :
    pairing (E := E) m a b = NativeModTwoMiddleEvaluation.evaluation m
      ((ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl).symm a) b := rfl

/-- A class obtained by the original cap evaluates to the original cohomology functional. -/
theorem pairing_cap (a : ModTwoCapProduct.Cohomology M 3) (b : ModHomology 2 M 3) :
    pairing (E := E) m (ManifoldCapMap.dualityMap (E := E) 3 M 3 3 rfl a) b =
      NativeModTwoMiddleEvaluation.evaluation m a b := by
  let D := ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl
  change NativeModTwoMiddleEvaluation.evaluation m (D.symm (D a)) b = _
  rw [LinearEquiv.symm_apply_apply]

/-- On a reduced integral class the formula is the original cochain evaluation. -/
theorem pairing_cap_reduction (a : ModTwoCapProduct.Cohomology M 3)
    (b : SingularHomology M 3) :
    pairing (E := E) m (ManifoldCapMap.dualityMap (E := E) 3 M 3 3 rfl a)
        (reductionHomologyMap 2 M 3 b) = SingularModTwoEvaluation.evaluation M 3 a b :=
  (pairing_cap (E := E) m a _).trans
    (NativeModTwoMiddleEvaluation.evaluation_reduction m a b)

/-- The proved cap and evaluation injections separate the left variable. -/
theorem eq_zero_of_pairing_left (a : ModHomology 2 M 3)
    (ha : ∀ b, pairing (E := E) m a b = 0) : a = 0 := by
  apply (functionalEquiv (E := E) m).injective
  have hz : functionalEquiv (E := E) m a = 0 := LinearMap.ext fun b => ha b
  exact hz.trans (functionalEquiv (E := E) m).map_zero.symm

/-- All functionals occur, and the native coefficient vector-space dual separates the right side. -/
theorem eq_zero_of_pairing_right (b : ModHomology 2 M 3)
    (hb : ∀ a, pairing (E := E) m a b = 0) : b = 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Field (ZMod 2) := inferInstance
  let : Module.Free (ZMod 2) (ModHomology 2 M 3) := Module.Free.of_divisionRing (ZMod 2) _
  let : Module.Projective (ZMod 2) (ModHomology 2 M 3) := inferInstance
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) b).mp
  intro φ
  let φInt : ModHomology 2 M 3 →ₗ[ℤ] ZMod 2 :=
    ConstantSheafSingularComparison.addHomToIntLinearMap φ.toAddMonoidHom
  obtain ⟨a, ha⟩ := (functionalEquiv (E := E) m).surjective φInt
  exact (LinearMap.congr_fun ha b).symm.trans (hb a)

/-- Nondegeneracy is proved for the actual cap-evaluation pairing, not yet the geometric pairing. -/
theorem pairing_nondegenerate : (pairing (E := E) m).Nondegenerate :=
  ⟨eq_zero_of_pairing_left (E := E) m, eq_zero_of_pairing_right (E := E) m⟩

/-- The basepoint used to prove the coefficient comparison does not affect this pairing. -/
theorem pairing_basepoint_independent (m' : M) [Subsingleton (π_ 2 M m')] :
    pairing (E := E) m = pairing (E := E) m' := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  exact congrArg (fun f => f ((ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl).symm a) b)
    (NativeModTwoMiddleEvaluation.evaluation_basepoint_independent m m')

end NoExoticSixSphere.MiddleCapEvaluation
