import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionImageIntegerBasic

/-!
# Identity and composition of the native integer endpoint

The endpoint along the identity is the actual identity sheaf map. Along a
composite of continuous open-site functors it is the composite of the actual
endpoints under native sheaf pushforward, as proved on integer degree units.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
namespace OpenClassRestriction.ImageInteger

open CuspNormalization.SheafCohomologyFinitePushforward
open HolomorphicPicard.CechExtension

/-- The integer endpoint for the identity open-site functor is the genuine
identity of the original integer sheaf. -/
theorem unit_id (X : TopCat.{0}) : unit (𝟭 (Opens X)) = 𝟙 (integerSheaf X) := by
  symm
  apply unit_unique (T := X) (X := X) (𝟭 (Opens X))
  rfl

variable {T X Y : TopCat.{0}} (J : Opens T ⥤ Opens X) (K : Opens X ⥤ Opens Y)
  [J.IsContinuous (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)]
  [K.IsContinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)]

/-- Composition is literal composition of native integer sheaf maps and the
actual continuous-site pushforward. Continuity of the composite is proved. -/
theorem unit_comp :
    letI := Functor.isContinuous_comp J K (Opens.grothendieckTopology T)
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
    unit (J ⋙ K) = unit J ≫
      (J.sheafPushforwardContinuous AddCommGrpCat
        (Opens.grothendieckTopology T) (Opens.grothendieckTopology X)).map (unit K) := by
  let := Functor.isContinuous_comp J K (Opens.grothendieckTopology T)
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
  symm
  apply unit_unique (T := T) (X := Y) (J ⋙ K)
  apply NatTrans.ext
  funext W
  apply ConcreteCategory.hom_ext
  intro n
  change (unit K).hom.app (op (J.obj W.unop))
      ((unit J).hom.app (op W.unop) ((degreeUnit T).app (op W.unop) n)) =
    (degreeUnit Y).app (op (K.obj (J.obj W.unop))) n
  exact (congrArg (fun s => (unit K).hom.app (op (J.obj W.unop)) s)
    (unit_degreeUnit_app (T := T) (X := X) J W.unop n)).trans
      (unit_degreeUnit_app (T := X) (X := Y) K (J.obj W.unop) n)

end OpenClassRestriction.ImageInteger
end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology
