import Wikipedia.NoExoticSixSphere.ZeroSecondHomologyEvaluation
import Wikipedia.NoExoticSixSphere.MiddleCapEvaluationPairing

/-!
# The original cap-evaluation pairing on a possibly disconnected boundary

Use the actual global fundamental-class cap and the original cochain
evaluation. Second integral homology vanishing gives their comparison
with the native mod-two middle group, without requiring connectedness.
On a two-connected manifold this is the previous cap pairing itself.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris
open scoped Topology

namespace NoExoticSixSphere.ZeroSecondHomologyCap

attribute [local instance] modHomologyModule

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = (3 + 2) + 1)]
  (M : Type) [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [CompactSpace M] [Subsingleton (SingularHomology M 2)]

def functionalEquiv : ModHomology 2 M 3 ≃ₗ[ℤ] (ModHomology 2 M 3 →ₗ[ℤ] ZMod 2) :=
  (ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl).symm.trans
    (ZeroSecondHomologyEvaluation.evaluationEquiv M)

def pairing : ModHomology 2 M 3 →ₗ[ZMod 2] ModHomology 2 M 3 →ₗ[ZMod 2] ZMod 2 :=
  ModTwoBilinear.scalarUpgrade (functionalEquiv (E := E) M).toLinearMap

theorem pairing_apply (a b : ModHomology 2 M 3) :
    pairing (E := E) M a b = ZeroSecondHomologyEvaluation.evaluation M
      ((ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl).symm a) b := rfl

theorem pairing_cap (a : ModTwoCapProduct.Cohomology M 3) (b : ModHomology 2 M 3) :
    pairing (E := E) M (ManifoldCapMap.dualityMap (E := E) 3 M 3 3 rfl a) b =
      ZeroSecondHomologyEvaluation.evaluation M a b := by
  let D := ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl
  change ZeroSecondHomologyEvaluation.evaluation M (D.symm (D a)) b = _
  rw [LinearEquiv.symm_apply_apply]

theorem pairing_cap_reduction (a : ModTwoCapProduct.Cohomology M 3)
    (b : SingularHomology M 3) :
    pairing (E := E) M (ManifoldCapMap.dualityMap (E := E) 3 M 3 3 rfl a)
        (reductionHomologyMap 2 M 3 b) = SingularModTwoEvaluation.evaluation M 3 a b :=
  (pairing_cap (E := E) M a _).trans
    (ZeroSecondHomologyEvaluation.evaluation_reduction M a b)

theorem eq_zero_of_pairing_left (a : ModHomology 2 M 3)
    (ha : ∀ b, pairing (E := E) M a b = 0) : a = 0 := by
  apply (functionalEquiv (E := E) M).injective
  have hz : functionalEquiv (E := E) M a = 0 := LinearMap.ext ha
  exact hz.trans (functionalEquiv (E := E) M).map_zero.symm

theorem eq_zero_of_pairing_right (b : ModHomology 2 M 3)
    (hb : ∀ a, pairing (E := E) M a b = 0) : b = 0 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Field (ZMod 2) := inferInstance
  let : Module.Free (ZMod 2) (ModHomology 2 M 3) := Module.Free.of_divisionRing (ZMod 2) _
  let : Module.Projective (ZMod 2) (ModHomology 2 M 3) := inferInstance
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) b).mp
  intro φ
  let φInt : ModHomology 2 M 3 →ₗ[ℤ] ZMod 2 :=
    ConstantSheafSingularComparison.addHomToIntLinearMap φ.toAddMonoidHom
  obtain ⟨a, ha⟩ := (functionalEquiv (E := E) M).surjective φInt
  exact (LinearMap.congr_fun ha b).symm.trans (hb a)

theorem pairing_nondegenerate : (pairing (E := E) M).Nondegenerate :=
  ⟨eq_zero_of_pairing_left (E := E) M, eq_zero_of_pairing_right (E := E) M⟩

theorem pairing_eq_connected [SimplyConnectedSpace M] (m : M)
    [Subsingleton (π_ 2 M m)] : pairing (E := E) M = MiddleCapEvaluation.pairing (E := E) m := by
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  exact congrArg (fun f ↦ f ((ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl).symm a) b)
    (ZeroSecondHomologyEvaluation.evaluation_eq_connected M m)

end NoExoticSixSphere.ZeroSecondHomologyCap
