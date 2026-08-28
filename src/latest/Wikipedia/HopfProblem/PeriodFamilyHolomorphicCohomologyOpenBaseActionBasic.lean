import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyBaseFunctionAction

/-!
# Actual base-open multipliers on the original full-preimage sheaf

A holomorphic function on a base open acts on the holomorphic sheaf of
its original full preimage by literal pullback multiplication. This is
defined on every open of the actual open submanifold, using the atlas
inherited from the original varying-period family. It uses no choice of
cohomology coordinates and no restricted-family cohomology equivalence.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction

open PeriodFamilyHigherDirectImage

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- Actual holomorphic sections on a nested open of the original full preimage. -/
abbrev PreimageSection (P : HolomorphicPeriodMap V B) (U : Opens B)
    (W : Opens (Zero.basePreimage P U)) : Type :=
  letI := P.totalChartedSpace
  HolomorphicFunctionSheaf.Section IT (Zero.basePreimage P U) W

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original base-open function pulled back to an arbitrary nested original open. -/
def preimagePullbackSection (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : Zero.BaseSection P U) (W : Opens (Zero.basePreimage P U)) :
    PreimageSection P U W := by
  letI := P.totalChartedSpace
  exact ⟨fun x => g (Zero.baseProjection P U x),
    (g.contMDiff.comp (Zero.baseProjection_holomorphic P U)).comp contMDiff_subtype_val⟩

@[simp] theorem preimagePullbackSection_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (g : Zero.BaseSection P U) (W : Opens (Zero.basePreimage P U)) (x : W) :
    preimagePullbackSection P U g W x = g (Zero.baseProjection P U x) := rfl

/-- Literal multiplication on every original full-preimage open gives
an actual endomorphism of its genuine holomorphic coefficient sheaf. -/
def preimageMultiplyEnd (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : Zero.BaseSection P U) :
    OpenClasses.preimageHolomorphicSheaf P U ⟶ OpenClasses.preimageHolomorphicSheaf P U := by
  letI := P.totalChartedSpace
  refine
    { hom :=
        { app := fun W => AddCommGrpCat.ofHom
            ({ toFun := fun s => preimagePullbackSection P U g W.unop * s
               map_zero' := mul_zero _
               map_add' := mul_add _ } :
              PreimageSection P U W.unop →+ PreimageSection P U W.unop)
          naturality := ?_ } }
  intro W Z h
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The coefficient action retains its original pointwise base value. -/
@[simp] theorem preimageMultiplyEnd_apply (P : HolomorphicPeriodMap V B) (U : Opens B)
    (g : Zero.BaseSection P U) (W : Opens (Zero.basePreimage P U))
    (s : PreimageSection P U W) (x : W) :
    Subtype.val ((preimageMultiplyEnd P U g).hom.app (op W) s : PreimageSection P U W) x =
      g (Zero.baseProjection P U x) * s x := rfl

omit [IsManifold (modelWithCornersSelf ℂ V) ω B] in
/-- Extensionality for original open-submanifold holomorphic coefficient endomorphisms. -/
theorem preimageSheafEnd_ext (P : HolomorphicPeriodMap V B) (U : Opens B)
    {f g : OpenClasses.preimageHolomorphicSheaf P U ⟶
      OpenClasses.preimageHolomorphicSheaf P U}
    (h : ∀ (W : Opens (Zero.basePreimage P U)) (s : PreimageSection P U W) (x : W),
      Subtype.val (f.hom.app (op W) s : PreimageSection P U W) x =
        Subtype.val (g.hom.app (op W) s : PreimageSection P U W) x) : f = g := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact ContMDiffMap.ext (h W.unop s)

/-- Genuine holomorphic base-open functions act by original coefficient endomorphisms. -/
def preimageMultiplyRingHom (P : HolomorphicPeriodMap V B) (U : Opens B) :
    Zero.BaseSection P U →+* End (OpenClasses.preimageHolomorphicSheaf P U) where
  toFun := preimageMultiplyEnd P U
  map_zero' := by
    apply preimageSheafEnd_ext P U
    intro W s x
    exact zero_mul (s x)
  map_one' := by
    apply preimageSheafEnd_ext P U
    intro W s x
    exact one_mul (s x)
  map_add' f g := by
    apply preimageSheafEnd_ext P U
    intro W s x
    exact add_mul (f (Zero.baseProjection P U x)) (g (Zero.baseProjection P U x)) (s x)
  map_mul' f g := by
    apply preimageSheafEnd_ext P U
    intro W s x
    exact mul_assoc (f (Zero.baseProjection P U x)) (g (Zero.baseProjection P U x)) (s x)

@[simp] theorem preimageMultiplyRingHom_apply (P : HolomorphicPeriodMap V B)
    (U : Opens B) (g : Zero.BaseSection P U) :
    (preimageMultiplyRingHom P U g).asHom = preimageMultiplyEnd P U g := rfl

/-- Constant base-open functions give the unchanged scalar endomorphism
of the original full-preimage holomorphic sheaf. -/
@[simp] theorem preimageMultiplyEnd_algebraMap (P : HolomorphicPeriodMap V B)
    (U : Opens B) (c : ℂ) :
    letI := P.totalChartedSpace
    preimageMultiplyEnd P U (algebraMap ℂ (Zero.BaseSection P U) c) =
      HolomorphicFunctionSheaf.scalarSheafEnd IT (Zero.basePreimage P U) c := by
  let := P.totalChartedSpace
  apply preimageSheafEnd_ext P U
  intro W s x
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction
