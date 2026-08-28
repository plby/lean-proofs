import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Exactness of the coproducts used in singular chains

The chosen coproduct object and map here are precisely `Sigma.map` and its
source and target, rather than a replacement by finitely supported functions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SphereHomologyCoefficients

/-- The constant discrete diagram, with the diagram used by `Sigma.map`. -/
def constantDiscreteDiagram (I : Type) : ModuleCat ℤ ⥤ Discrete I ⥤ ModuleCat ℤ where
  obj A := Discrete.functor (fun _ => A)
  map f := Discrete.natTrans (fun _ => f)

instance constantDiscreteDiagram_additive (I : Type) :
    (constantDiscreteDiagram I).Additive where
  map_add := by intros; rfl

/-- Identification with the ordinary constant-diagram functor. -/
def constantDiscreteDiagramIso (I : Type) :
    Functor.const (Discrete I) ≅ constantDiscreteDiagram I :=
  NatIso.ofComponents (fun _ => Discrete.natIsoFunctor) (by
    intro A B f
    apply NatTrans.ext
    funext i
    change f ≫ 𝟙 B = 𝟙 A ≫ f
    simp)

instance constantDiscreteDiagram_preservesFiniteLimits (I : Type) :
    PreservesFiniteLimits (constantDiscreteDiagram I) :=
  preservesFiniteLimits_of_natIso (constantDiscreteDiagramIso I)

instance constantDiscreteDiagram_preservesFiniteColimits (I : Type) :
    PreservesFiniteColimits (constantDiscreteDiagram I) :=
  preservesFiniteColimits_of_natIso (constantDiscreteDiagramIso I)

/-- The native coproduct of a fixed coefficient module, indexed by `I`. -/
def coefficientCoproductFunctor (I : Type) : ModuleCat ℤ ⥤ ModuleCat ℤ :=
  constantDiscreteDiagram I ⋙ colim

instance coefficientCoproductFunctor_additive (I : Type) :
    (coefficientCoproductFunctor I).Additive := by
  unfold coefficientCoproductFunctor
  infer_instance

instance coefficientCoproductFunctor_preservesFiniteLimits (I : Type) :
    PreservesFiniteLimits (coefficientCoproductFunctor I) := by
  unfold coefficientCoproductFunctor
  infer_instance

instance coefficientCoproductFunctor_preservesFiniteColimits (I : Type) :
    PreservesFiniteColimits (coefficientCoproductFunctor I) := by
  unfold coefficientCoproductFunctor
  infer_instance

theorem coefficientCoproductFunctor_obj (I : Type) (A : ModuleCat ℤ) :
    (coefficientCoproductFunctor I).obj A = ∐ (fun _ : I => A) := rfl

theorem coefficientCoproductFunctor_map (I : Type) {A B : ModuleCat ℤ} (f : A ⟶ B) :
    (coefficientCoproductFunctor I).map f = Limits.Sigma.map (fun _ : I => f) := rfl

/-- Exact coproducts of modules, on the exact chosen objects underlying chains. -/
theorem coefficientCoproductFunctor_shortExact (I : Type)
    (S : ShortComplex (ModuleCat ℤ)) (hS : S.ShortExact) :
    (S.map (coefficientCoproductFunctor I)).ShortExact :=
  hS.map_of_exact (coefficientCoproductFunctor I)

end Wikipedia.HopfProblem.SphereHomologyCoefficients
