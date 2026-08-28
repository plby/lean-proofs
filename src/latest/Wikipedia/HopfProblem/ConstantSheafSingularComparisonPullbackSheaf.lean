import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafCoefficient
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafFunctorial
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackSheafInteger

/-!
# Native continuous pullback of the singular-cochain sheaf comparison

Every continuous map acts on the original raw cochain presheaves, the
actual sheafified cochain complexes, and their original global-section
complexes. All maps commute with the original augmentation, differentials,
and arbitrary abelian coefficient changes. The actual comparison from
singular cochains to global sections is natural before taking cohomology.

The construction is functorial for identities and compositions, and the
constant integer map is the very same map already used in the native Ext
pushforward comparison. No exactness of pushforward, compactness, or
local contractibility is assumed for these naturality statements.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf

variable {X Y Z : TopCat.{0}} (A : AddCommGrpCat.{0})

/-- The actual global-section complex pullback along the identity is
the identity of the original global cochain complex. -/
@[simp]
theorem globalSheafPullback_id :
    globalSheafPullback (𝟙 X) A = 𝟙 (globalSheafCochainComplex X A) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact NatTrans.congr_app
    (congrArg (fun θ : cochainSheaf X A n ⟶ cochainSheaf X A n => θ.hom)
      (cochainPullback_id A n)) (op ⊤)

/-- The original global-section pullbacks compose contravariantly,
using the actual original maps of complexes. -/
theorem globalSheafPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    globalSheafPullback (f ≫ g) A =
      globalSheafPullback g A ≫ globalSheafPullback f A := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact NatTrans.congr_app
    (congrArg (fun θ : cochainSheaf Z A n ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat (f ≫ g)).obj (cochainSheaf X A n) => θ.hom)
      (cochainPullback_comp A n f g)) (op ⊤)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackSheaf
