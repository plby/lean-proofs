import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsAdditiveBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsMaps
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsPullback
import Wikipedia.HopfProblem.HolomorphicFunctionSheafCohomologyZeroBasic

/-!
# Additive maps from the actual constant complex sheaf

These are the additive images of the already constructed ring-sheaf
maps, not replacement maps between abstract constant sheaves.  Their
targets are the actual additive holomorphic-function sheaves used in
sheaf cohomology and in the normalization sequence.
-/

noncomputable section

open Set TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- The actual constant-to-holomorphic map after forgetting multiplication. -/
def holomorphicAdditiveMap :
    complexAdditiveSheaf (TopCat.of M) ⟶ HolomorphicFunctionSheaf.additiveSheaf I M :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
    (holomorphicMap I M)

@[simp] theorem holomorphicAdditiveMap_unit (U : Opens M) (c : ℂ) (x : U) :
    (fun f : HolomorphicFunctionSheaf.Section I M U => f x)
      ((holomorphicAdditiveMap I M).hom.app (op U)
        ((additiveUnit (TopCat.of M)).app (op U) c)) = c :=
  holomorphicMap_unit I M U c x

variable {M} (S : Set M)

/-- The actual constant-to-reduced-holomorphic map on additive sheaves. -/
def reducedAdditiveMap :
    complexAdditiveSheaf (TopCat.of S) ⟶ SheafReduced.additiveSheaf I S :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
    (reducedMap I S)

@[simp] theorem reducedAdditiveMap_unit (U : Opens S) (c : ℂ) (x : U) :
    (fun f : SheafReduced.Section I S U => f x)
      ((reducedAdditiveMap I S).hom.app (op U)
        ((additiveUnit (TopCat.of S)).app (op U) c)) = c :=
  reducedMap_unit I S U c x

section Pullback

variable {X Y : TopCat.{0}}

/-- The additive image of actual constant-sheaf pullback, with its native
additive pushforward target. -/
def additivePullbackMap (f : X ⟶ Y) :
    complexAdditiveSheaf Y ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat f).obj (complexAdditiveSheaf X) :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)).map
    (pullbackMap f)

@[simp] theorem additivePullbackMap_unit (f : X ⟶ Y) (U : Opens Y) (c : ℂ) :
    (additivePullbackMap f).hom.app (op U) ((additiveUnit Y).app (op U) c) =
      (additiveUnit X).app (op ((Opens.map f).obj U)) c :=
  pullbackMap_unit f U c

end Pullback

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
