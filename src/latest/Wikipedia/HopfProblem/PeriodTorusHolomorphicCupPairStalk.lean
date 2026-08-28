import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupPairFunctor

/-!
# Actual pair-sheaf stalks and their coordinate projections

The stalk comparison is the canonical map of the genuine biproduct
comparison. Both coordinates remain the original stalk maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs

open CuspNormalization.SheafBiproduct SheafSingularCupComparison.TotalCategory

variable {X : TopCat.{0}}

/-- The actual coefficient-pair stalk is the product of the two original stalks. -/
def stalkIso (F : AbSheaf X) (x : X) :
    (stalkFunctor X x).obj (sheaf F) ≅
      AddCommGrpCat.of ((stalkFunctor X x).obj F × (stalkFunctor X x).obj F) :=
  (stalkFunctor X x).mapIso (biprodIso F) ≪≫ binaryIso (stalkFunctor X x) F F

def stalkEquiv (F : AbSheaf X) (x : X) :
    (stalkFunctor X x).obj (sheaf F) ≃+
      ((stalkFunctor X x).obj F × (stalkFunctor X x).obj F) :=
  (stalkIso F x).addCommGroupIsoToAddEquiv

@[reassoc] theorem stalkIso_hom_fst (F : AbSheaf X) (x : X) :
    (stalkIso F x).hom ≫ AddCommGrpCat.ofHom
        (AddMonoidHom.fst ((stalkFunctor X x).obj F) ((stalkFunctor X x).obj F)) =
      (stalkFunctor X x).map (fst F) := by
  change ((stalkFunctor X x).map (biprodIso F).hom ≫
    (binaryIso (stalkFunctor X x) F F).hom) ≫ _ = _
  rw [Category.assoc, binaryIso_hom_fst, ← Functor.map_comp, biprodIso_hom_fst]

@[reassoc] theorem stalkIso_hom_snd (F : AbSheaf X) (x : X) :
    (stalkIso F x).hom ≫ AddCommGrpCat.ofHom
        (AddMonoidHom.snd ((stalkFunctor X x).obj F) ((stalkFunctor X x).obj F)) =
      (stalkFunctor X x).map (snd F) := by
  change ((stalkFunctor X x).map (biprodIso F).hom ≫
    (binaryIso (stalkFunctor X x) F F).hom) ≫ _ = _
  rw [Category.assoc, binaryIso_hom_snd, ← Functor.map_comp, biprodIso_hom_snd]

@[simp] theorem stalkEquiv_fst (F : AbSheaf X) (x : X)
    (s : (stalkFunctor X x).obj (sheaf F)) :
    (stalkEquiv F x s).1 = (stalkFunctor X x).map (fst F) s :=
  ConcreteCategory.congr_hom (stalkIso_hom_fst F x) s

@[simp] theorem stalkEquiv_snd (F : AbSheaf X) (x : X)
    (s : (stalkFunctor X x).obj (sheaf F)) :
    (stalkEquiv F x s).2 = (stalkFunctor X x).map (snd F) s :=
  ConcreteCategory.congr_hom (stalkIso_hom_snd F x) s

/-- Every original stalk map acts on the two original coefficients. -/
theorem stalkEquiv_map {F G : AbSheaf X} (f : F ⟶ G) (x : X)
    (s : (stalkFunctor X x).obj (sheaf F)) :
    stalkEquiv G x ((stalkFunctor X x).map (map f) s) =
      ((stalkFunctor X x).map f (stalkEquiv F x s).1,
        (stalkFunctor X x).map f (stalkEquiv F x s).2) := by
  apply Prod.ext
  · rw [stalkEquiv_fst, stalkEquiv_fst]
    exact ConcreteCategory.congr_hom
      (((stalkFunctor X x).map_comp (map f) (fst G)).symm.trans
        ((congrArg (stalkFunctor X x).map (map_fst f)).trans
          ((stalkFunctor X x).map_comp (fst F) f))) s
  · rw [stalkEquiv_snd, stalkEquiv_snd]
    exact ConcreteCategory.congr_hom
      (((stalkFunctor X x).map_comp (map f) (snd G)).symm.trans
        ((congrArg (stalkFunctor X x).map (map_snd f)).trans
          ((stalkFunctor X x).map_comp (snd F) f))) s

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs
