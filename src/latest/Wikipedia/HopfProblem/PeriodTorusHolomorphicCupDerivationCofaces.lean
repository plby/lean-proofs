import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupDerivationGodementUnit

/-!
# Actual derivations on the first four multiplicative Godement terms

The original ring cofaces insert the genuine germ inclusion. Its proved
additive naturality, and the actual ring-functor agreement of the lift,
give all coface squares through degree two.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation

open SheafCupProduct

variable {X : TopCat.{0}} {F : GodementRing.RingSheaf X}

abbrev term0Derivation (D : SheafDerivation F) : SheafDerivation (GodementRing.term0 F) :=
  liftedDerivation D

abbrev term1Derivation (D : SheafDerivation F) : SheafDerivation (GodementRing.term1 F) :=
  liftedDerivation (term0Derivation D)

abbrev term2Derivation (D : SheafDerivation F) : SheafDerivation (GodementRing.term2 F) :=
  liftedDerivation (term1Derivation D)

abbrev term3Derivation (D : SheafDerivation F) : SheafDerivation (GodementRing.term3 F) :=
  liftedDerivation (term2Derivation D)

theorem term0Derivation_coface (D : SheafDerivation F) (j : Fin 2) :
    (term0Derivation D).map ≫ (GodementRing.forgetSheaf X).map (GodementRing.face0 F j) =
      (GodementRing.forgetSheaf X).map (GodementRing.face0 F j) ≫ (term1Derivation D).map := by
  fin_cases j
  · exact (liftMap_inclusion (term0Derivation D).map).symm
  · exact liftMap_ring_square D.map (term0Derivation D).map (GodementRing.inclusion F)
      (liftMap_inclusion D.map).symm

theorem term1Derivation_coface (D : SheafDerivation F) (j : Fin 3) :
    (term1Derivation D).map ≫ (GodementRing.forgetSheaf X).map (GodementRing.face1 F j) =
      (GodementRing.forgetSheaf X).map (GodementRing.face1 F j) ≫ (term2Derivation D).map := by
  fin_cases j
  · exact (liftMap_inclusion (term1Derivation D).map).symm
  · exact liftMap_ring_square (term0Derivation D).map (term1Derivation D).map
      (GodementRing.face0 F 0) (term0Derivation_coface D 0)
  · exact liftMap_ring_square (term0Derivation D).map (term1Derivation D).map
      (GodementRing.face0 F 1) (term0Derivation_coface D 1)

theorem term2Derivation_coface (D : SheafDerivation F) (j : Fin 4) :
    (term2Derivation D).map ≫ (GodementRing.forgetSheaf X).map (GodementRing.face2 F j) =
      (GodementRing.forgetSheaf X).map (GodementRing.face2 F j) ≫ (term3Derivation D).map := by
  fin_cases j
  · exact (liftMap_inclusion (term2Derivation D).map).symm
  · exact liftMap_ring_square (term1Derivation D).map (term2Derivation D).map
      (GodementRing.face1 F 0) (term1Derivation_coface D 0)
  · exact liftMap_ring_square (term1Derivation D).map (term2Derivation D).map
      (GodementRing.face1 F 1) (term1Derivation_coface D 1)
  · exact liftMap_ring_square (term1Derivation D).map (term2Derivation D).map
      (GodementRing.face1 F 2) (term1Derivation_coface D 2)

theorem term0Derivation_commute (D E : SheafDerivation F)
    (h : D.map ≫ E.map = E.map ≫ D.map) :
    (term0Derivation D).map ≫ (term0Derivation E).map =
      (term0Derivation E).map ≫ (term0Derivation D).map :=
  liftMap_commute D.map E.map h

theorem term1Derivation_commute (D E : SheafDerivation F)
    (h : D.map ≫ E.map = E.map ≫ D.map) :
    (term1Derivation D).map ≫ (term1Derivation E).map =
      (term1Derivation E).map ≫ (term1Derivation D).map :=
  liftMap_commute _ _ (term0Derivation_commute D E h)

theorem term2Derivation_commute (D E : SheafDerivation F)
    (h : D.map ≫ E.map = E.map ≫ D.map) :
    (term2Derivation D).map ≫ (term2Derivation E).map =
      (term2Derivation E).map ≫ (term2Derivation D).map :=
  liftMap_commute _ _ (term1Derivation_commute D E h)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Derivation
