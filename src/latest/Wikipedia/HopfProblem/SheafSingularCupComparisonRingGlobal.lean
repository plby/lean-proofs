import Wikipedia.HopfProblem.SheafSingularCupComparisonRingDifferential
import Wikipedia.HopfProblem.SheafSingularCupComparisonRingScalars
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalSections

/-!
# The actual global singular-cochain unit preserves the cofaces

The original top-open inclusion and native ring sheafification unit
give a degreewise ring map from actual singular-simplex values to actual
global cochain-sheaf sections. This is a genuine coface morphism. Its
underlying additive map is the original global singular-cochain unit,
under the original basis-extension and sheaf comparisons.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains

open ConstantSheafSingularComparison

variable (X : TopCat.{0})

/-- The actual global ring-cochain unit, using the original top-open inclusion. -/
def globalUnit (n : ℕ) : Singular.Values X ℂ n →+* (sheaf X n).obj.obj (op ⊤) :=
  ((unit X n).app (op ⊤)).hom.comp
    (pullback (⟨Subtype.val, continuous_subtype_val⟩ : C((⊤ : Opens X), X)) n)

@[simp] theorem globalUnit_apply (n : ℕ) (a : Singular.Values X ℂ n) :
    globalUnit X n a = (unit X n).app (op ⊤)
      (fun σ => a ((⟨Subtype.val, continuous_subtype_val⟩ :
        C((⊤ : Opens X), X)).comp σ)) := rfl

/-- The original global unit commutes with every actual singular coface. -/
theorem globalUnit_coface (n : ℕ) (i : Fin (n + 2)) :
    (globalUnit X (n + 1)).comp (Singular.face X ℂ n i) =
      ((coface X n i).hom.app (op ⊤)).hom.comp (globalUnit X n) := by
  apply RingHom.ext
  intro a
  exact (ConcreteCategory.congr_hom
    (NatTrans.congr_app (unit_coface X n i) (op ⊤))
      (pullback (⟨Subtype.val, continuous_subtype_val⟩ : C((⊤ : Opens X), X)) n a)).symm

/-- The original global unit is an actual ring-coface morphism. -/
def globalUnitMorphism :
    (Singular.cofaceData X ℂ).Morphism (globalData X) where
  f0 := globalUnit X 0
  f1 := globalUnit X 1
  f2 := globalUnit X 2
  f3 := globalUnit X 3
  comm0 := globalUnit_coface X 0
  comm1 := globalUnit_coface X 1
  comm2 := globalUnit_coface X 2

/-- Literal global constant cochains give exactly the original coefficient sections. -/
@[simp] theorem globalUnit_constant (n : ℕ) (z : ℂ) :
    globalUnit X n (fun _ => z) = coefficients X n z := rfl

/-- The original additive global unit is retained on every actual cochain. -/
theorem globalUnit_additive (n : ℕ) (a : Singular.Values X ℂ n) :
    (forgetSheafIso X n).hom.hom.app (op ⊤) (globalUnit X n a) =
      globalCochainUnit X (AddCommGrpCat.of ℂ) n
        (cochainFromValues X (AddCommGrpCat.of ℂ) n a) := by
  let f : C((⊤ : Opens X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  exact (forgetSheafIso_app_unit X n ⊤ (pullback f n a)).trans
      (congrArg ((cochainSheafUnit X (AddCommGrpCat.of ℂ) n).app (op ⊤))
        (fromValues_pullback f n a))

/-- The same compatibility as an equality of the original additive group maps. -/
theorem globalUnit_additive_map (n : ℕ) :
    AddCommGrpCat.ofHom (globalUnit X n).toAddMonoidHom ≫
        (forgetSheafIso X n).hom.hom.app (op ⊤) =
      (cochainEvalEquiv X (AddCommGrpCat.of ℂ) n).symm.toAddCommGrpIso.hom ≫
        globalCochainUnit X (AddCommGrpCat.of ℂ) n := by
  ext a
  exact globalUnit_additive X n a

end Wikipedia.HopfProblem.SheafSingularCupComparison.RingCochains
