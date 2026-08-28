import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsCancellation
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleSquare

/-!
# Actual cancellation of a line against the dual of its square

The native line bundle `A tensor dual(A^2)` is holomorphically and
fibre-linearly isomorphic to `dual(A)`. The maps use the original variable
cocycles and original bundle atlases. On full tensor fibres the comparison
is partial evaluation against the actual square, not a degree computation.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  (A : TransitionData M ι) [hA : A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

private theorem singleDualSquare_identity {G : Type*} [CommGroup G]
    (a b c d : G) (h : b * a = d * c) :
    c⁻¹ * a ^ 2 = d ^ 2 * (c * (b ^ 2)⁻¹) := by
  have ha : a = b⁻¹ * (d * c) := by rw [← h]; simp
  rw [ha, mul_pow, mul_pow]
  calc
    c⁻¹ * ((b⁻¹) ^ 2 * (d ^ 2 * c ^ 2)) =
        d ^ 2 * ((b⁻¹) ^ 2 * (c⁻¹ * c ^ 2)) := by ac_rfl
    _ = d ^ 2 * (c * (b ^ 2)⁻¹) := by
      have hc : c⁻¹ * c ^ 2 = c := by simp [pow_two]
      rw [hc, inv_pow, mul_comm ((b ^ 2)⁻¹) c]

/-- The genuine partial-evaluation gauge on the paired original cover. -/
def singleDualSquareGauge :
    Gauge I (tensor A (dual (A.power 2))) (leftRefinement (dual A) A) where
  baseSet_eq := rfl
  value i x := A.transition i.1 i.2 x ^ 2
  compatible i j x hx := by
    have hc : A.transition i.2 j.2 x * A.transition i.1 i.2 x =
        A.transition j.1 j.2 x * A.transition i.1 j.1 x :=
      (A.transition_comp i.1 i.2 j.2 x ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩).trans
        (A.transition_comp i.1 j.1 j.2 x ⟨⟨hx.1.1, hx.2.1⟩, hx.2.2⟩).symm
    exact singleDualSquare_identity (A.transition i.1 i.2 x) (A.transition i.2 j.2 x)
      (A.transition i.1 j.1 x) (A.transition j.1 j.2 x) hc
  holomorphicOn i := by
    simpa only [Units.val_pow_eq_pow_val, tensor_baseSet, dual_baseSet,
      TransitionData.power_baseSet] using
      (A.transition_holomorphic I i.1 i.2).pow 2

/-- The cancellation is a genuine biholomorphism of native total spaces. -/
def singleDualSquareDiffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    (tensor A (dual (A.power 2))).core.TotalSpace (dual A).core.TotalSpace ω :=
  (singleDualSquareGauge I A).diffeomorph.trans
    (leftRefinementDiffeomorph (dual A) A I).symm

/-- The fibrewise complex-linear cancellation in the original fibres. -/
def singleDualSquareFiberEquiv (x : M) :
    (tensor A (dual (A.power 2))).core.Fiber x ≃L[ℂ] (dual A).core.Fiber x :=
  ((singleDualSquareGauge I A).fiberEquiv x).trans
    (leftRefinementFiberEquiv (dual A) A x).symm

@[simp] theorem singleDualSquareDiffeomorph_mk (x : M)
    (v : (tensor A (dual (A.power 2))).core.Fiber x) :
    singleDualSquareDiffeomorph I A ⟨x, v⟩ = ⟨x, singleDualSquareFiberEquiv I A x v⟩ := rfl

@[simp] theorem singleDualSquareDiffeomorph_proj
    (p : (tensor A (dual (A.power 2))).core.TotalSpace) :
    (singleDualSquareDiffeomorph I A p).proj = p.proj := rfl

include hA in
/-- Cancellation has no arbitrary rescaling in the common preferred fibre. -/
theorem singleDualSquareFiberEquiv_apply (x : M)
    (v : (tensor A (dual (A.power 2))).core.Fiber x) :
    singleDualSquareFiberEquiv I A x v = id (α := ℂ) v := by
  change (((A.transition (A.indexAt x) (A.indexAt x) x)⁻¹ *
      A.transition (A.indexAt x) (A.indexAt x) x ^ 2 : ℂˣ) : ℂ) * id (α := ℂ) v = _
  rw [A.transition_self _ _ (A.mem_baseSet_at x)]
  simp only [inv_one, one_pow, mul_one, Units.val_one, one_mul]

/-- The same map identifies the full original tensor product with the
full continuous dual of the surviving line. -/
def singleDualSquareTensorEquiv (x : M) :
    A.core.Fiber x ⊗[ℂ] (dual (A.power 2)).core.Fiber x ≃ₗ[ℂ]
      (A.core.Fiber x →L[ℂ] ℂ) :=
  (fibreTensorEquiv A (dual (A.power 2)) x).trans
    ((singleDualSquareFiberEquiv I A x).toLinearEquiv.trans (dualFiberEquiv A x).toLinearEquiv)

/-- On elementary tensors it is precisely partial evaluation on the
actual tensor square; the preceding equivalence is on the full tensor product. -/
theorem singleDualSquareTensorEquiv_tmul (x : M) (a v : A.core.Fiber x)
    (b : (dual (A.power 2)).core.Fiber x) :
    singleDualSquareTensorEquiv I A x (a ⊗ₜ[ℂ] b) v =
      dualFiberEquiv (A.power 2) x b (squareFiberTensorEquiv I A x (a ⊗ₜ[ℂ] v)) := by
  change dualFiberEquiv A x
    (singleDualSquareFiberEquiv I A x (fibreTensorEquiv A (dual (A.power 2)) x
      (a ⊗ₜ[ℂ] b))) v = _
  have hm : id (α := ℂ)
      (singleDualSquareFiberEquiv I A x
        (fibreTensorEquiv A (dual (A.power 2)) x (a ⊗ₜ[ℂ] b))) =
        id (α := ℂ) a * id (α := ℂ) b :=
    (singleDualSquareFiberEquiv_apply I A x _).trans
      (fibreTensorEquiv_tmul A (dual (A.power 2)) x a b)
  calc
    _ = id (α := ℂ) (singleDualSquareFiberEquiv I A x
        (fibreTensorEquiv A (dual (A.power 2)) x (a ⊗ₜ[ℂ] b))) * id (α := ℂ) v :=
      dualFiberEquiv_apply A x _ v
    _ = (id (α := ℂ) a * id (α := ℂ) b) * id (α := ℂ) v :=
      congrArg (fun c : ℂ => c * id (α := ℂ) v) hm
    _ = id (α := ℂ) b * (id (α := ℂ) a * id (α := ℂ) v) := by ring
    _ = id (α := ℂ) b * id (α := ℂ)
        (squareFiberTensorEquiv I A x (a ⊗ₜ[ℂ] v)) :=
      congrArg (fun c : ℂ => id (α := ℂ) b * c)
        (squareFiberTensorEquiv_tmul I A x a v).symm
    _ = _ := (dualFiberEquiv_apply (A.power 2) x b _).symm

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
