import Wikipedia.HopfProblem.MappingTorusTopology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturalityCoordinates
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Circle translations in the actual product action

The map changing only the fibre is homotopic to the map which also
translates the actual additive circle by any prescribed real amount.
The homotopy is the literal translation by `u * s` at time `u`.
Consequently the two maps induce the same integral singular homology map
in every degree, for every topological fibre and continuous fibre map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.DeckHomology

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

abbrev Circle := Wikipedia.HopfProblem.MappingTorus.Circle

/-- The existing literal `id × B` map used in the circle-product naturality theorem. -/
abbrev fibreProductMap (B : C(X, X)) : C(Circle × X, Circle × X) :=
  PeriodTorusHigherHomology.circleProductMap B

@[simp] theorem fibreProductMap_apply (B : C(X, X)) (p : Circle × X) :
    fibreProductMap B p = (p.1, B p.2) := rfl

/-- The actual product map with a prescribed translation on the circle factor. -/
def translatedProductMap (s : ℝ) (B : C(X, X)) : C(Circle × X, Circle × X) where
  toFun p := (p.1 + (s : Circle), B p.2)
  continuous_toFun := (continuous_fst.add continuous_const).prodMk
    (B.continuous.comp continuous_snd)

@[simp] theorem translatedProductMap_apply (s : ℝ) (B : C(X, X)) (p : Circle × X) :
    translatedProductMap s B p = (p.1 + (s : Circle), B p.2) := rfl

/-- Translate the actual circle by `u * s` while applying the same fibre map. -/
def productTranslationHomotopy (s : ℝ) (B : C(X, X)) :
    (fibreProductMap B).Homotopy (translatedProductMap s B) where
  toFun p := (p.2.1 + ((((p.1 : ℝ) * s : ℝ)) : Circle), B p.2.2)
  continuous_toFun := by
    have ht : Continuous (fun p : unitInterval × (Circle × X) => (p.1 : ℝ) * s) :=
      (continuous_subtype_val.comp continuous_fst).mul_const s
    have hc : Continuous (fun p : unitInterval × (Circle × X) =>
        (((p.1 : ℝ) * s : ℝ) : Circle)) :=
      (AddCircle.continuous_mk' (1 : ℝ)).comp ht
    exact ((continuous_fst.comp continuous_snd).add hc).prodMk
      (B.continuous.comp (continuous_snd.comp continuous_snd))
  map_zero_left p := by
    change (p.1 + (((((0 : unitInterval) : ℝ) * s : ℝ)) : Circle), B p.2) =
      (p.1, B p.2)
    simp
  map_one_left p := by
    change (p.1 + (((((1 : unitInterval) : ℝ) * s : ℝ)) : Circle), B p.2) =
      (p.1 + (s : Circle), B p.2)
    simp

@[simp] theorem productTranslationHomotopy_apply (s : ℝ) (B : C(X, X))
    (u : unitInterval) (p : Circle × X) :
    productTranslationHomotopy s B (u, p) =
      (p.1 + (((u : ℝ) * s : ℝ) : Circle), B p.2) := rfl

@[simp] theorem productTranslationHomotopy_zero (s : ℝ) (B : C(X, X)) (p : Circle × X) :
    productTranslationHomotopy s B (0, p) = (p.1, B p.2) :=
  (productTranslationHomotopy s B).map_zero_left p

@[simp] theorem productTranslationHomotopy_one (s : ℝ) (B : C(X, X)) (p : Circle × X) :
    productTranslationHomotopy s B (1, p) = (p.1 + (s : Circle), B p.2) :=
  (productTranslationHomotopy s B).map_one_left p

/-- The corresponding native singular-chain homotopy of the two actual product maps. -/
def productTranslationChainHomotopy (s : ℝ) (B : C(X, X)) :
    _root_.Homotopy (FirstHurewicz.singularChainMap (fibreProductMap B))
      (FirstHurewicz.singularChainMap (translatedProductMap s B)) :=
  PeriodTorusHigherHomology.singularChainHomotopy (productTranslationHomotopy s B)

/-- Adding a circle translation does not change the actual integral homology map. -/
theorem productTranslation_homologyMap (s : ℝ) (B : C(X, X)) (n : ℕ) :
    singularHomologyMap (fibreProductMap B) n =
      singularHomologyMap (translatedProductMap s B) n :=
  congrArg ModuleCat.Hom.hom ((productTranslationChainHomotopy s B).homologyMap_eq n)

/-- The translated map has exactly the map of the existing circle-product
endomorphism, in the orientation used to apply its naturality formulas. -/
theorem translatedProductMap_homologyMap (s : ℝ) (B : C(X, X)) (n : ℕ) :
    singularHomologyMap (translatedProductMap s B) n =
      singularHomologyMap (PeriodTorusHigherHomology.circleProductMap B) n :=
  (productTranslation_homologyMap s B n).symm

end Wikipedia.HopfProblem.Elliptic.HigherHomology.DeckHomology
