import Wikipedia.HopfProblem.SheafCupProductGodementExactRetraction

/-!
# Contracting identities on the actual Godement stalk complex

Evaluation at the point cancels the first inserted germ. Its proved
naturality pairs all remaining terms in the alternating differential.
This proves the contracting identity in each required degree.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.GodementExact

open GodementRing

variable {X : TopCat.{0}}

/-- The contracting identity at the original degree-zero Godement term. -/
theorem contraction0 (F : RingSheaf X) (x : X) :
    stalkRetraction F x ≫ (additiveStalk x).map (augmentation F) +
      (additiveStalk x).map (d0 F) ≫ stalkRetraction (term0 F) x =
        𝟙 ((additiveStalk x).obj (I0 F)) := by
  change stalkRetraction F x ≫ (additiveStalk x).map (augmentation F) +
    (additiveStalk x).map (augmentation (term0 F) -
      (forgetSheaf X).map (map (inclusion F))) ≫ stalkRetraction (term0 F) x = _
  rw [Functor.map_sub, Preadditive.sub_comp,
    augmentation_stalkRetraction (term0 F) x,
    stalkRetraction_naturality (inclusion F) x]
  change stalkRetraction F x ≫ (additiveStalk x).map (augmentation F) +
    (𝟙 _ - stalkRetraction F x ≫ (additiveStalk x).map (augmentation F)) = _
  abel

/-- The contracting identity at the original degree-one Godement term. -/
theorem contraction1 (F : RingSheaf X) (x : X) :
    stalkRetraction (term0 F) x ≫ (additiveStalk x).map (d0 F) +
      (additiveStalk x).map (d1 F) ≫ stalkRetraction (term1 F) x =
        𝟙 ((additiveStalk x).obj (I1 F)) := by
  change stalkRetraction (term0 F) x ≫
      (additiveStalk x).map (augmentation (term0 F) -
        (forgetSheaf X).map (map (inclusion F))) +
    (additiveStalk x).map (augmentation (term1 F) -
      (forgetSheaf X).map (map (inclusion (term0 F))) +
      (forgetSheaf X).map (map (map (inclusion F)))) ≫
        stalkRetraction (term1 F) x = _
  simp only [Functor.map_sub, Functor.map_add, Preadditive.comp_sub,
    Preadditive.sub_comp, Preadditive.add_comp]
  rw [augmentation_stalkRetraction (term1 F) x,
    stalkRetraction_naturality (inclusion (term0 F)) x,
    stalkRetraction_naturality (map (inclusion F)) x]
  change (stalkRetraction (term0 F) x ≫ (additiveStalk x).map (augmentation (term0 F)) -
      stalkRetraction (term0 F) x ≫
        (additiveStalk x).map ((forgetSheaf X).map (map (inclusion F)))) +
    (𝟙 _ - stalkRetraction (term0 F) x ≫
      (additiveStalk x).map (augmentation (term0 F)) +
      stalkRetraction (term0 F) x ≫
        (additiveStalk x).map ((forgetSheaf X).map (map (inclusion F)))) = _
  abel

/-- The contracting identity at the original degree-two Godement term. -/
theorem contraction2 (F : RingSheaf X) (x : X) :
    stalkRetraction (term1 F) x ≫ (additiveStalk x).map (d1 F) +
      (additiveStalk x).map (d2 F) ≫ stalkRetraction (term2 F) x =
        𝟙 ((additiveStalk x).obj (I2 F)) := by
  change stalkRetraction (term1 F) x ≫
      (additiveStalk x).map (augmentation (term1 F) -
        (forgetSheaf X).map (map (inclusion (term0 F))) +
        (forgetSheaf X).map (map (map (inclusion F)))) +
    (additiveStalk x).map (augmentation (term2 F) -
      (forgetSheaf X).map (map (inclusion (term1 F))) +
      (forgetSheaf X).map (map (map (inclusion (term0 F)))) -
      (forgetSheaf X).map (map (map (map (inclusion F))))) ≫
        stalkRetraction (term2 F) x = _
  simp only [Functor.map_sub, Functor.map_add, Preadditive.comp_sub,
    Preadditive.comp_add, Preadditive.sub_comp, Preadditive.add_comp]
  rw [augmentation_stalkRetraction (term2 F) x,
    stalkRetraction_naturality (inclusion (term1 F)) x,
    stalkRetraction_naturality (map (inclusion (term0 F))) x,
    stalkRetraction_naturality (map (map (inclusion F))) x]
  unfold augmentation
  abel

end Wikipedia.HopfProblem.SheafCupProduct.GodementExact
