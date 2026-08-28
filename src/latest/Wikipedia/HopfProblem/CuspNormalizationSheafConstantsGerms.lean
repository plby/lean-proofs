import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsStalk
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsMaps

/-!
# Literal constant germs under the actual sheaf inclusions

The canonical stalk identification with `ℂ` sends each scalar to the
actual germ of its sheafified constant section.  Under either analytic
inclusion this becomes the ordinary germ of the actual constant function.
These formulas identify the stalk maps used in a normalization sequence.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory TopCat
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants

/-- The inverse stalk identification is a genuine constant germ on any
chosen neighbourhood, independently of that neighbourhood. -/
theorem complexSheafStalkEquiv_symm_eq_germ_unit (X : TopCat.{0}) (x : X)
    (U : Opens X) (hx : x ∈ U) (c : ℂ) :
    (complexSheafStalkEquiv X x).symm c =
      Presheaf.germ (complexSheaf X).obj U x hx ((unit X).app (op U) c) := by
  apply (complexSheafStalkEquiv X x).injective
  exact (complexSheafStalkEquiv X x).apply_symm_apply c |>.trans
    (complexSheafStalkEquiv_germ_unit X x U hx c).symm

/-- The stalk map constructed by sheafification has the literal
constant-germ formula specified by its original presheaf map. -/
theorem lift_stalk_constant {X : TopCat.{0}} (F : RingSheaf X)
    (φ : constantPresheaf X ⟶ F.obj) (x : X) (U : Opens X) (hx : x ∈ U) (c : ℂ) :
    (Presheaf.stalkFunctor CommRingCat x).map (lift F φ).hom
        ((complexSheafStalkEquiv X x).symm c) =
      Presheaf.germ F.obj U x hx (φ.app (op U) c) := by
  exact (congrArg ((Presheaf.stalkFunctor CommRingCat x).map (lift F φ).hom)
    (complexSheafStalkEquiv_symm_eq_germ_unit X x U hx c)).trans
      ((Presheaf.stalkFunctor_map_germ_apply U x hx (lift F φ).hom
        ((unit X).app (op U) c)).trans
        (congrArg (Presheaf.germ F.obj U x hx) (lift_app_unit F φ U c)))

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- On actual manifold stalks the inclusion is the ordinary constant
holomorphic germ. -/
theorem holomorphicMap_stalk_constant (x : M) (U : Opens M) (hx : x ∈ U) (c : ℂ) :
    (Presheaf.stalkFunctor CommRingCat x).map (holomorphicMap I M).hom
        ((complexSheafStalkEquiv (TopCat.of M) x).symm c) =
      Presheaf.germ (HolomorphicFunctionSheaf.sheaf I M).obj U x hx
        (ContMDiffMap.const c) :=
  lift_stalk_constant (HolomorphicFunctionSheaf.sheaf I M)
    (holomorphicPresheafMap I M) x U hx c

variable {M} (S : Set M)

/-- On reduced-function stalks the inclusion is the ordinary germ of
the literal constant locally ambient-holomorphic function. -/
theorem reducedMap_stalk_constant (x : S) (U : Opens S) (hx : x ∈ U) (c : ℂ) :
    (Presheaf.stalkFunctor CommRingCat x).map (reducedMap I S).hom
        ((complexSheafStalkEquiv (TopCat.of S) x).symm c) =
      Presheaf.germ (SheafReduced.sheaf I S).obj U x hx (SheafReduced.constant I S U c) :=
  lift_stalk_constant (SheafReduced.sheaf I S) (reducedPresheafMap I S) x U hx c

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants
