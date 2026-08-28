import Wikipedia.HopfProblem.ExponentialChernComparisonDLogResolution
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalSections
import Wikipedia.HopfProblem.ExponentialChernComparisonConnecting

/-!
# Literal local cochains as lifts in the original sheaf resolution

The sections in this file are the images of actual local singular
cochains under the original sheafification unit. Their restrictions and
differentials retain the original presheaf formulas. Equality in the
last cycle sheaf is checked through its genuine kernel inclusion.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge

open ConstantSheafSingularComparison HolomorphicFunctionSheaf.SphereH1

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

/-- An actual local singular one-cochain gives a literal section of the
degree-one cochain sheaf in the original truncated resolution. -/
def localSection (U : Opens X) (t : Cochains U (AddCommGrpCat.of ℂ) 1) :
    Section (DLog.resolution X hLC).complex.X₂ U :=
  (cochainSheafUnit X (AddCommGrpCat.of ℂ) 1).app (op U) t

@[simp] theorem localSection_eq (U : Opens X) (t : Cochains U (AddCommGrpCat.of ℂ) 1) :
    localSection X hLC U t =
      (cochainSheafUnit X (AddCommGrpCat.of ℂ) 1).app (op U) t := rfl

/-- Restriction is the image of the original singular-cochain restriction. -/
theorem localSection_restrict {U V : Opens X} (h : U ≤ V)
    (t : Cochains V (AddCommGrpCat.of ℂ) 1) :
    res (DLog.resolution X hLC).complex.X₂ h (localSection X hLC V t) =
      localSection X hLC U
        ((cochainPresheaf X (AddCommGrpCat.of ℂ) 1).map (homOfLE h).op t) :=
  (cochainSheafUnit_restrict X (AddCommGrpCat.of ℂ) 1 (homOfLE h) t).symm

/-- Later-minus-earlier overlap differences remain the literal
presheaf differences under the original sheafification unit. -/
theorem localSection_restrict_sub {U V W : Opens X} (hUV : U ≤ V) (hUW : U ≤ W)
    (s : Cochains V (AddCommGrpCat.of ℂ) 1) (t : Cochains W (AddCommGrpCat.of ℂ) 1) :
    res (DLog.resolution X hLC).complex.X₂ hUW (localSection X hLC W t) -
        res (DLog.resolution X hLC).complex.X₂ hUV (localSection X hLC V s) =
      localSection X hLC U
        ((cochainPresheaf X (AddCommGrpCat.of ℂ) 1).map (homOfLE hUW).op t -
          (cochainPresheaf X (AddCommGrpCat.of ℂ) 1).map (homOfLE hUV).op s) := by
  rw [localSection_restrict, localSection_restrict]
  exact (map_sub ((cochainSheafUnit X (AddCommGrpCat.of ℂ) 1).app (op U)).hom _ _).symm

/-- The differential of the actual local section, followed by the
original degree-two kernel inclusion, is the unit of the actual local
singular differential. -/
theorem localSection_g_inclusion (U : Opens X)
    (t : Cochains U (AddCommGrpCat.of ℂ) 1) :
    (kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.app (op U)
        ((DLog.resolution X hLC).complex.g.hom.app (op U) (localSection X hLC U t)) =
      (cochainSheafUnit X (AddCommGrpCat.of ℂ) 2).app (op U)
        ((singularCochainComplex U (AddCommGrpCat.of ℂ)).d 1 2 t) := by
  have hg := ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg (fun f => f.hom) (DLog.resolution_g_ι X hLC)) (op U))
    (localSection X hLC U t)
  change (kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.app (op U)
      ((DLog.resolution X hLC).complex.g.hom.app (op U) (localSection X hLC U t)) =
    (sheafDifferential X (AddCommGrpCat.of ℂ) 1 2).hom.app (op U)
      (localSection X hLC U t) at hg
  rw [hg, localSection_eq]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (cochainSheafUnit_d X (AddCommGrpCat.of ℂ) 1 2) (op U)) t

/-- A literal primitive of the restricted global cochain lifts its
actual degree-two kernel section through the original resolution map. -/
theorem localSection_lifts (U : Opens X)
    (σ : Section (DLog.resolution X hLC).complex.X₃ ⊤)
    (ζ : Cochains X (AddCommGrpCat.of ℂ) 2)
    (hσ : (kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.app (op ⊤) σ =
      globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ)
    (t : Cochains U (AddCommGrpCat.of ℂ) 1)
    (ht : (singularCochainComplex U (AddCommGrpCat.of ℂ)).d 1 2 t =
      restrictGlobalCochain (AddCommGrpCat.of ℂ) 2 ζ U) :
    (DLog.resolution X hLC).complex.g.hom.app (op U) (localSection X hLC U t) =
      res (DLog.resolution X hLC).complex.X₃ le_top σ := by
  have hm : Mono (kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom :=
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X).map_mono
      (kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3))
  apply (AddCommGrpCat.mono_iff_injective
    ((kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.app (op U))).mp
      ((NatTrans.mono_iff_mono_app _).mp hm (op U))
  have hn := ConcreteCategory.congr_hom
    ((kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.naturality
      (homOfLE (le_top : U ≤ ⊤)).op) σ
  change (kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.app (op U)
      (res (DLog.resolution X hLC).complex.X₃ le_top σ) =
    (cochainSheaf X (AddCommGrpCat.of ℂ) 2).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      ((kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3)).hom.app (op ⊤) σ) at hn
  rw [hσ] at hn
  calc
    _ = (cochainSheafUnit X (AddCommGrpCat.of ℂ) 2).app (op U)
        ((singularCochainComplex U (AddCommGrpCat.of ℂ)).d 1 2 t) :=
      localSection_g_inclusion X hLC U t
    _ = (cochainSheafUnit X (AddCommGrpCat.of ℂ) 2).app (op U)
        (restrictGlobalCochain (AddCommGrpCat.of ℂ) 2 ζ U) := by rw [ht]
    _ = (cochainSheaf X (AddCommGrpCat.of ℂ) 2).obj.map
        (homOfLE (le_top : U ≤ ⊤)).op (globalCochainUnit X (AddCommGrpCat.of ℂ) 2 ζ) :=
      (globalCochainUnit_restrict X (AddCommGrpCat.of ℂ) 2 ζ U).symm
    _ = _ := hn.symm

end Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge
