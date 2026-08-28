import Wikipedia.NoExoticSixSphere.MiddleCapEvaluationPairing

/-!
# Self-orthogonality from the actual cap kernel and evaluation maps

For an actual map to a two-connected space, the proved evaluation
naturality and separation of native mod-two homology identify the right
annihilator of its kernel. The input cap-kernel criterion is a statement
about the original cap and cohomology restriction maps; filling slabs
will supply it by their proved boundary connecting square.
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
  {W : Type} [TopologicalSpace W] [SimplyConnectedSpace W]
  (w : W) [hW₂ : Subsingleton (π_ 2 W w)] (j : C(M, W))

include w hW₂

theorem kernel_selfOrthogonal
    (hkernel : ∀ a : ModTwoCapProduct.Cohomology M 3,
      modHomologyMap 2 j 3 (ManifoldCapMap.dualityMap (E := E) 3 M 3 3 rfl a) = 0 ↔
        ∃ b : ModTwoCapProduct.Cohomology W 3,
          ModTwoCapProduct.cohomologyPullback j 3 b = a)
    (b : ModHomology 2 M 3) :
    (∀ a : ModHomology 2 M 3, modHomologyMap 2 j 3 a = 0 → pairing (E := E) m a b = 0) ↔
      modHomologyMap 2 j 3 b = 0 := by
  constructor
  · intro hb
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : Field (ZMod 2) := inferInstance
    let : Module.Free (ZMod 2) (ModHomology 2 W 3) := Module.Free.of_divisionRing (ZMod 2) _
    let : Module.Projective (ZMod 2) (ModHomology 2 W 3) := inferInstance
    apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (modHomologyMap 2 j 3 b)).mp
    intro φ
    let φInt : ModHomology 2 W 3 →ₗ[ℤ] ZMod 2 :=
      ConstantSheafSingularComparison.addHomToIntLinearMap φ.toAddMonoidHom
    obtain ⟨β, hβ⟩ := (NativeModTwoMiddleEvaluation.evaluationEquiv w).surjective φInt
    have ha : modHomologyMap 2 j 3 (ManifoldCapMap.dualityMap (E := E) 3 M 3 3 rfl
        (ModTwoCapProduct.cohomologyPullback j 3 β)) = 0 :=
      (hkernel _).mpr ⟨β, rfl⟩
    have hvalue : NativeModTwoMiddleEvaluation.evaluation w β (modHomologyMap 2 j 3 b) = 0 :=
      (NativeModTwoMiddleEvaluation.evaluation_naturality m w j β b).symm.trans
        ((pairing_cap (E := E) m (ModTwoCapProduct.cohomologyPullback j 3 β) b).symm.trans
          (hb _ ha))
    exact (LinearMap.congr_fun hβ (modHomologyMap 2 j 3 b)).symm.trans hvalue
  · intro hb a ha
    obtain ⟨α, rfl⟩ := (ManifoldCapMap.dualityEquiv (E := E) 3 M 3 3 rfl).surjective a
    obtain ⟨β, hβ⟩ := (hkernel α).mp ha
    change pairing (E := E) m (ManifoldCapMap.dualityMap (E := E) 3 M 3 3 rfl α) b = 0
    rw [pairing_cap, ← hβ, NativeModTwoMiddleEvaluation.evaluation_naturality m w j β b,
      hb, map_zero]

end NoExoticSixSphere.MiddleCapEvaluation
