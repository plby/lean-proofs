import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyCechFibreInteger

/-!
# The genuine map of Čech extensions to a source-space pushforward

The literal coordinatewise map is followed by the target sheafification
unit. The universal property of the source sheafification then gives
an actual sheaf morphism, preserving the original coefficient inclusion
and the native constant-integer map into pushforward.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre

open HolomorphicFunctionSheaf.SphereH1 HolomorphicPicard.CechExtension
open CuspNormalization.SheafCohomologyFinitePushforward

variable {T X : TopCat.{0}} (f : T ⟶ X)
  {F : AbelianSheaf X} {G : AbelianSheaf T}
  (κ : F ⟶ (pushforward f).obj G) {ι : Type} {U : ι → Opens X}
  (c : CechOneCocycle F U)

/-- Actual compatible data are sent into the sheafification of the
literal source-space extension. -/
def pullbackSheafPre :
    presheaf c ⟶ ((pushforward f).obj (extensionSheaf (pullbackCocycle f κ c))).obj :=
  pullbackPre f κ c ≫ Functor.whiskerLeft (Opens.map f).op (unit (pullbackCocycle f κ c))

@[simp] theorem pullbackSheafPre_app (V : Opens X) (s : ExtensionSection c V) :
    (pullbackSheafPre f κ c).app (op V) s =
      (unit (pullbackCocycle f κ c)).app (op ((Opens.map f).obj V))
        (pullbackSectionHom f κ c V s) := rfl

/-- The genuine sheaf morphism induced by literal restriction of
the original extension data, using the actual sheafification property. -/
def pullbackExtension :
    extensionSheaf c ⟶ (pushforward f).obj (extensionSheaf (pullbackCocycle f κ c)) where
  hom := CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (pullbackSheafPre f κ c)
    ((pushforward f).obj (extensionSheaf (pullbackCocycle f κ c))).property

/-- On original presheaf representatives, the map is the literal
coordinatewise restriction followed by the source-space unit. -/
theorem unit_pullbackExtension :
    unit c ≫ (pullbackExtension f κ c).hom = pullbackSheafPre f κ c :=
  CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X)
    (pullbackSheafPre f κ c)
    ((pushforward f).obj (extensionSheaf (pullbackCocycle f κ c))).property

@[simp] theorem pullbackExtension_app_unit (V : Opens X) (s : ExtensionSection c V) :
    (pullbackExtension f κ c).hom.app (op V) ((unit c).app (op V) s) =
      (unit (pullbackCocycle f κ c)).app (op ((Opens.map f).obj V))
        (pullbackSectionHom f κ c V s) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (unit_pullbackExtension f κ c) (op V)) s

/-- The first endpoint is exactly the original coefficient map. -/
theorem inclusion_pullbackExtension :
    inclusion c ≫ pullbackExtension f κ c =
      κ ≫ (pushforward f).map (inclusion (pullbackCocycle f κ c)) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro a
  change (pullbackExtension f κ c).hom.app V
      ((unit c).app V (includeHom c V.unop a)) =
    (unit (pullbackCocycle f κ c)).app (op ((Opens.map f).obj V.unop))
      (includeHom (pullbackCocycle f κ c) ((Opens.map f).obj V.unop) (κ.hom.app V a))
  rw [pullbackExtension_app_unit, pullbackSectionHom_includeHom]

/-- The degree endpoint is the canonical native integer-sheaf map,
not an identification chosen after computing cohomology. -/
theorem pullbackExtension_projection :
    pullbackExtension f κ c ≫ (pushforward f).map (projection (pullbackCocycle f κ c)) =
      projection c ≫ integerUnit f := by
  apply extensionHom_ext c
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro s
  exact (congrArg
    (((pushforward f).map (projection (pullbackCocycle f κ c))).hom.app V)
    (pullbackExtension_app_unit f κ c V.unop s)).trans
      ((projection_app_unit (pullbackCocycle f κ c) ((Opens.map f).obj V.unop)
        (pullbackSectionHom f κ c V.unop s)).trans
        ((integerUnit_degreeUnit_app f V.unop (degreeHom c V.unop s)).symm.trans
          (congrArg ((integerUnit f).hom.app V) (projection_app_unit c V.unop s).symm)))

/-- A genuine space-changing map of the original extension complexes.
Its endpoints are the original coefficient map and canonical integer map. -/
def pullbackComplexMap :
    complex c ⟶ (complex (pullbackCocycle f κ c)).map (pushforward f) where
  τ₁ := κ
  τ₂ := pullbackExtension f κ c
  τ₃ := integerUnit f
  comm₁₂ := (inclusion_pullbackExtension f κ c).symm
  comm₂₃ := pullbackExtension_projection f κ c

@[simp] theorem pullbackComplexMap_τ₁ : (pullbackComplexMap f κ c).τ₁ = κ := rfl

@[simp] theorem pullbackComplexMap_τ₂ :
    (pullbackComplexMap f κ c).τ₂ = pullbackExtension f κ c := rfl

@[simp] theorem pullbackComplexMap_τ₃ :
    (pullbackComplexMap f κ c).τ₃ = integerUnit f := rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.CechFibre
