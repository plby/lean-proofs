import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyGodementFunctor
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyFineBasic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The actual Godement successor preserves local vanishing

The product-of-stalks map is locally zero when the original map is:
points inside the open set have zero stalk maps, and the other
skyscrapers have zero sections on every smaller open set. The actual
cokernel map is then locally zero by epimorphy on actual stalks.
Consequently the actual additive successor preserves finite fine
decompositions with exactly the same closed supports.
-/

noncomputable section

open Set TopologicalSpace Opposite TopCat CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement

attribute [local instance] Classical.propDecidable

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {f : F ⟶ G} {U : Opens X}

/-- On the selected open set, each actual point-skyscraper map is zero. -/
theorem pointMap_isZeroOn (hf : IsZeroOn f U) (x : X) :
    IsZeroOn (pointMap f x) U := by
  by_cases hx : x ∈ U
  · have hp : pointMap f x = 0 := by
      change (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map
        ((CuspNormalization.SheafBiproduct.stalkFunctor X x).map f) = 0
      rw [hf.stalkMap_eq_zero x hx]
      exact (skyscraperSheafFunctor (C := AddCommGrpCat.{0}) x).map_zero _ _
    intro V hVU
    rw [hp]
    rfl
  · intro V hVU
    have hxV : x ∉ V := fun h => hx (hVU h)
    have ht : IsTerminal ((pointTerm G x).presheaf.obj (op V)) := by
      change IsTerminal (if x ∈ V then G.presheaf.stalk x else terminal AddCommGrpCat)
      rw [if_neg hxV]
      exact terminalIsTerminal
    exact ht.hom_ext _ _

/-- The actual product-of-stalks map preserves vanishing on an open set. -/
theorem map_isZeroOn (hf : IsZeroOn f U) : IsZeroOn (map f) U := by
  intro V hVU
  let E : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
    TopCat.Sheaf.forget AddCommGrpCat X ⋙
      (CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)
  let : (TopCat.Sheaf.forget AddCommGrpCat X).IsRightAdjoint :=
    (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat).isRightAdjoint
  let : PreservesLimitsOfShape (Discrete X) (TopCat.Sheaf.forget AddCommGrpCat X) :=
    (CategoryTheory.sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat).rightAdjoint_preservesLimits.preservesLimitsOfShape
  let : PreservesLimitsOfShape (Discrete X)
      ((CategoryTheory.evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op V)) := by
    infer_instance
  let : PreservesLimit (Discrete.functor (pointTerm G)) E := by
    dsimp [E]
    infer_instance
  change E.map (map f) = 0
  apply (isLimitOfPreserves E (productIsProduct (pointTerm G))).hom_ext
  intro j
  change E.map (map f) ≫ E.map (Pi.π (pointTerm G) j.as) =
    0 ≫ E.map (Pi.π (pointTerm G) j.as)
  rw [zero_comp]
  calc
    E.map (map f) ≫ E.map (Pi.π (pointTerm G) j.as) =
        E.map (map f ≫ Pi.π (pointTerm G) j.as) := (E.map_comp _ _).symm
    _ = E.map (Pi.π (pointTerm F) j.as ≫ pointMap f j.as) :=
      congrArg E.map (map_component f j.as)
    _ = E.map (Pi.π (pointTerm F) j.as) ≫ E.map (pointMap f j.as) := E.map_comp _ _
    _ = E.map (Pi.π (pointTerm F) j.as) ≫ 0 :=
      congrArg (fun m => E.map (Pi.π (pointTerm F) j.as) ≫ m)
        (pointMap_isZeroOn hf j.as V hVU)
    _ = 0 := comp_zero

/-- The genuine Godement functor is local, in addition to being additive. -/
theorem functor_isLocal : IsLocalFunctor (functor (X := X)) := by
  intro F G f U h
  exact map_isZeroOn h

/-- Local vanishing passes to the actual categorical cokernel map. -/
theorem successorMap_isZeroOn (hf : IsZeroOn f U) : IsZeroOn (successorMap f) U := by
  apply isZeroOn_of_stalkMap_eq_zero
  intro x hx
  let K := CuspNormalization.SheafBiproduct.stalkFunctor X x
  have hn : K.map (cokernel.π (inclusion F)) ≫ K.map (successorMap f) =
      K.map (map f) ≫ K.map (cokernel.π (inclusion G)) :=
    (K.map_comp _ _).symm.trans
      ((congrArg K.map (successorMap_π f)).trans (K.map_comp _ _))
  have hz : K.map (map f) = 0 := (map_isZeroOn hf).stalkMap_eq_zero x hx
  apply (cancel_epi (K.map (cokernel.π (inclusion F)))).mp
  rw [comp_zero]
  exact hn.trans ((congrArg (fun m => m ≫ K.map (cokernel.π (inclusion G))) hz).trans zero_comp)

/-- The genuine successor is a local additive functor. -/
theorem successorFunctor_isLocal : IsLocalFunctor (successorFunctor (X := X)) := by
  intro F G f U h
  exact successorMap_isZeroOn h

/-- An actual finite fine decomposition is retained by the actual
Godement cokernel construction. -/
theorem successor_finiteFine (hF : FiniteFine F) : FiniteFine (successor F) :=
  hF.map successorFunctor successorFunctor_isLocal

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Godement
