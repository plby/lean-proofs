import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersComparisonsNative
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleDual
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalLineBundleTensor

/-!
# Cancellation of one genuine dual factor from a tensor square

The native tensor bundle `A^2 tensor A.dual` is holomorphically and
fibre-linearly isomorphic to the original line bundle `A`.  The proof
uses the actual variable cocycles on the paired cover, followed by
the actual common-cover refinement isomorphism.  The dual and tensor
fibres already have their full linear-dual and tensor-product meanings.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
  [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
  (A : TransitionData M ι) [A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The evaluation comparison on the paired cover uses the genuine
transition between its two factor charts. -/
def squareDualGauge : Gauge I (tensor (A.power 2) (dual A)) (leftRefinement A A) where
  baseSet_eq := rfl
  value i x := A.transition i.1 i.2 x
  compatible i j x hx := by
    have hc : A.transition i.2 j.2 x * A.transition i.1 i.2 x =
        A.transition j.1 j.2 x * A.transition i.1 j.1 x :=
      (A.transition_comp i.1 i.2 j.2 x ⟨⟨hx.1.1, hx.1.2⟩, hx.2.2⟩).trans
        (A.transition_comp i.1 j.1 j.2 x ⟨⟨hx.1.1, hx.2.1⟩, hx.2.2⟩).symm
    change A.transition i.1 j.1 x * A.transition i.1 i.2 x =
      A.transition j.1 j.2 x *
        (A.transition i.1 j.1 x ^ 2 * (A.transition i.2 j.2 x)⁻¹)
    calc
      _ = A.transition i.1 j.1 x * ((A.transition i.2 j.2 x)⁻¹ *
          (A.transition i.2 j.2 x * A.transition i.1 i.2 x)) := by simp
      _ = A.transition i.1 j.1 x * ((A.transition i.2 j.2 x)⁻¹ *
          (A.transition j.1 j.2 x * A.transition i.1 j.1 x)) := by rw [hc]
      _ = _ := by simp only [pow_two]; ac_rfl
  holomorphicOn i := A.transition_holomorphic I i.1 i.2

/-- An actual holomorphic isomorphism of the original total spaces. -/
def squareDualDiffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    (tensor (A.power 2) (dual A)).core.TotalSpace A.core.TotalSpace ω :=
  (squareDualGauge I A).diffeomorph.trans (leftRefinementDiffeomorph A A I).symm

/-- Its complex-linear map on the literal original fibres. -/
def squareDualFiberEquiv (x : M) :
    (tensor (A.power 2) (dual A)).core.Fiber x ≃L[ℂ] A.core.Fiber x :=
  ((squareDualGauge I A).fiberEquiv x).trans (leftRefinementFiberEquiv A A x).symm

@[simp] theorem squareDualDiffeomorph_mk (x : M)
    (v : (tensor (A.power 2) (dual A)).core.Fiber x) :
    squareDualDiffeomorph I A ⟨x, v⟩ = ⟨x, squareDualFiberEquiv I A x v⟩ := rfl

@[simp] theorem squareDualDiffeomorph_proj
    (p : (tensor (A.power 2) (dual A)).core.TotalSpace) :
    (squareDualDiffeomorph I A p).proj = p.proj := rfl

/-- The preferred-frame fibre expression is evaluation multiplication,
with no arbitrary rescaling of the surviving original line. -/
theorem squareDualFiberEquiv_apply (x : M)
    (v : (tensor (A.power 2) (dual A)).core.Fiber x) :
    squareDualFiberEquiv I A x v = id (α := ℂ) v := by
  change ((A.transition (A.indexAt x) (A.indexAt x) x *
      A.transition (A.indexAt x) (A.indexAt x) x : ℂˣ) : ℂ) * id (α := ℂ) v = _
  rw [A.transition_self _ _ (A.mem_baseSet_at x)]
  simp only [mul_one, Units.val_one, one_mul]

private theorem squareDual_preferredMap_eq :
    OpenMaps.preferredMap (tensor (A.power 2) (dual A)) A (fun _ => 1) =
      squareDualDiffeomorph I A := by
  funext p
  cases p with
  | mk x v =>
    rw [squareDualDiffeomorph_mk, squareDualFiberEquiv_apply]
    change (⟨x, (1 : ℂ) * id (α := ℂ) v⟩ : A.core.TotalSpace) = ⟨x, id (α := ℂ) v⟩
    rw [one_mul]

/-- The same genuine cancellation is available for composition and
raising to powers through the cross-cover gauge API. -/
def squareDualCrossGauge : CrossGauge I (tensor (A.power 2) (dual A)) A :=
  CrossGauge.ofPreferredMap (tensor (A.power 2) (dual A)) A (fun _ => 1) (by
    rw [squareDual_preferredMap_eq I A]
    exact (squareDualDiffeomorph I A).contMDiff)

theorem squareDualCrossGauge_diffeomorph_apply
    (p : (tensor (A.power 2) (dual A)).core.TotalSpace) :
    (squareDualCrossGauge I A).diffeomorph p = squareDualDiffeomorph I A p :=
  (CrossGauge.ofPreferredMap_diffeomorph_apply _ _ _ _ p).trans
    (congrFun (squareDual_preferredMap_eq I A) p)

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
