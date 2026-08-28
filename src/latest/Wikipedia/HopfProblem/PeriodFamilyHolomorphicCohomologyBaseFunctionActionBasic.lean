import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCocycleSections

/-!
# Actual holomorphic base-function multipliers on a period family

Every original holomorphic base function acts on the original total-space
holomorphic sheaf by multiplication with its literal pullback. The maps
are defined on every open in the unchanged varying-period quotient atlas
and commute with the actual restriction maps. Their ring homomorphism
uses composition in the genuine sheaf endomorphism ring.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.BaseFunctionAction

open PeriodFamilyHigherDirectImage

/-- The ring of actual bundled holomorphic functions on the original base. -/
abbrev BaseFunction (V : Type*) (B : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] :=
  ContMDiffMap (modelWithCornersSelf ℂ V) 𝓘(ℂ) B ℂ ω

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]
  [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- Literal pullback of a base function, restricted to any original total-space open. -/
def basePullbackSection (P : HolomorphicPeriodMap V B) (g : BaseFunction V B)
    (U : Opens P.TotalSpace) : Cocycle.NativeSection P U := by
  letI := P.totalChartedSpace
  exact ⟨fun x => g (P.projection x),
    (g.contMDiff.comp P.projection_holomorphic).comp contMDiff_subtype_val⟩

@[simp] theorem basePullbackSection_apply (P : HolomorphicPeriodMap V B)
    (g : BaseFunction V B) (U : Opens P.TotalSpace) (x : U) :
    basePullbackSection P g U x = g (P.projection x) := rfl

/-- Multiplication by the genuine holomorphic pullback on every original open. -/
def baseMultiplyEnd (P : HolomorphicPeriodMap V B) (g : BaseFunction V B) :
    Zero.totalAdditiveSheaf P ⟶ Zero.totalAdditiveSheaf P := by
  letI := P.totalChartedSpace
  refine
    { hom :=
        { app := fun U => AddCommGrpCat.ofHom
            ({ toFun := fun s => basePullbackSection P g U.unop * s
               map_zero' := mul_zero _
               map_add' := mul_add _ } :
              Cocycle.NativeSection P U.unop →+ Cocycle.NativeSection P U.unop)
          naturality := ?_ } }
  intro U W h
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- The original coefficient endomorphism acts by the literal base value. -/
@[simp] theorem baseMultiplyEnd_apply (P : HolomorphicPeriodMap V B)
    (g : BaseFunction V B) (U : Opens P.TotalSpace)
    (s : Cocycle.NativeSection P U) (x : U) :
    Subtype.val ((baseMultiplyEnd P g).hom.app (op U) s : Cocycle.NativeSection P U) x =
      g (P.projection x) * s x := rfl

omit [IsManifold (modelWithCornersSelf ℂ V) ω B] in
/-- Pointwise extensionality retains the actual family sheaf and its native atlas. -/
theorem totalSheafEnd_ext (P : HolomorphicPeriodMap V B)
    {f g : Zero.totalAdditiveSheaf P ⟶ Zero.totalAdditiveSheaf P}
    (h : ∀ (U : Opens P.TotalSpace) (s : Cocycle.NativeSection P U) (x : U),
      Subtype.val (f.hom.app (op U) s : Cocycle.NativeSection P U) x =
        Subtype.val (g.hom.app (op U) s : Cocycle.NativeSection P U) x) : f = g := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact ContMDiffMap.ext (h U.unop s)

/-- Actual base multiplication is a ring action by genuine coefficient endomorphisms. -/
def baseMultiplyRingHom (P : HolomorphicPeriodMap V B) :
    BaseFunction V B →+* End (Zero.totalAdditiveSheaf P) where
  toFun := baseMultiplyEnd P
  map_zero' := by
    apply totalSheafEnd_ext P
    intro U s x
    exact zero_mul (s x)
  map_one' := by
    apply totalSheafEnd_ext P
    intro U s x
    exact one_mul (s x)
  map_add' f g := by
    apply totalSheafEnd_ext P
    intro U s x
    exact add_mul (f (P.projection x)) (g (P.projection x)) (s x)
  map_mul' f g := by
    apply totalSheafEnd_ext P
    intro U s x
    exact mul_assoc (f (P.projection x)) (g (P.projection x)) (s x)

@[simp] theorem baseMultiplyRingHom_apply (P : HolomorphicPeriodMap V B)
    (g : BaseFunction V B) :
    (baseMultiplyRingHom P g).asHom = baseMultiplyEnd P g := rfl

/-- Constant base functions recover the unchanged original complex scalar endomorphism. -/
@[simp] theorem baseMultiplyEnd_algebraMap (P : HolomorphicPeriodMap V B) (c : ℂ) :
    baseMultiplyEnd P (algebraMap ℂ (BaseFunction V B) c) = Zero.totalScalarEnd P c := by
  apply totalSheafEnd_ext P
  intro U s x
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.BaseFunctionAction
