import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionMaps

/-!
# Naturality of the actual low-degree Ext comparisons

These squares compare the functorial Ext maps to the actual homology
and cokernel maps. Their proofs use the genuine connecting representatives.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C]

/-- A comparison defined by surjective representatives is natural
when both its representative square and its class square commute. -/
theorem comparison_naturality_of_epi {K L H H' V W : C}
    (c : K ⟶ H) (c' : L ⟶ H') (e : H ⟶ V) (e' : H' ⟶ W)
    (q : K ⟶ V) (q' : L ⟶ W) (k : K ⟶ L) (h : H ⟶ H') (v : V ⟶ W)
    [Epi c] (hc : k ≫ c' = c ≫ h) (he : c ≫ e = q)
    (he' : c' ≫ e' = q') (hq : k ≫ q' = q ≫ v) : h ≫ e' = e ≫ v := by
  apply (cancel_epi c).mp
  rw [← Category.assoc, ← hc, Category.assoc, he', hq, ← he, Category.assoc]

variable [Abelian C] [HasExt.{w} C]

namespace AugmentedResolution.Hom

variable {R S : AugmentedResolution C} (φ : Hom R S) (P : C)

/-- The actual cokernel map on the last degree-zero Ext differential. -/
def extCokernelMap : cokernel (R.extZeroComplex P).g ⟶ cokernel (S.extZeroComplex P).g :=
  cokernel.map (R.extZeroComplex P).g (S.extZeroComplex P).g
    (φ.extZeroMap P).τ₂ (φ.extZeroMap P).τ₃ (φ.extZeroMap P).comm₂₃.symm

@[reassoc (attr := simp)] theorem extCokernelMap_π :
    cokernel.π (R.extZeroComplex P).g ≫ φ.extCokernelMap P =
      (extFunctorObj P 0).map φ.complex.τ₃ ≫ cokernel.π (S.extZeroComplex P).g :=
  cokernel.π_desc _ _ _

/-- Genuine degree-one Ext and actual section homology commute with
every map of the augmented resolutions. -/
@[reassoc] theorem extOneIso_naturality
    [Subsingleton (Ext P R.complex.X₁ 1)] [Subsingleton (Ext P S.complex.X₁ 1)] :
    (extFunctorObj P 1).map φ.augmentation ≫ (S.extOneIso P).hom =
      (R.extOneIso P).hom ≫ ShortComplex.homologyMap (φ.extZeroMap P) := by
  have : Epi (AddCommGrpCat.ofHom (connecting P R.first_shortExact 0)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (connecting_surjective P R.first_shortExact 0)
  refine comparison_naturality_of_epi
    (AddCommGrpCat.ofHom (connecting P R.first_shortExact 0))
    (AddCommGrpCat.ofHom (connecting P S.first_shortExact 0))
    (R.extOneIso P).hom (S.extOneIso P).hom
    (R.extCycleMap P ≫ (R.extZeroComplex P).homologyπ)
    (S.extCycleMap P ≫ (S.extZeroComplex P).homologyπ)
    ((extFunctorObj P 0).map φ.kernelMap) ((extFunctorObj P 1).map φ.augmentation)
    (ShortComplex.homologyMap (φ.extZeroMap P))
    (φ.connectingOne_naturality P) (R.extOneIso_connecting_cycle P)
    (S.extOneIso_connecting_cycle P) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (S.extZeroComplex P).homologyπ)
      (φ.extCycleMap_naturality P)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun k => R.extCycleMap P ≫ k)
            (ShortComplex.homologyπ_naturality (φ.extZeroMap P)).symm).trans
              (Category.assoc _ _ _).symm)))

/-- Genuine degree-two Ext and the actual final cokernel commute with
every map of the augmented resolutions. -/
@[reassoc] theorem extTwoIso_naturality
    [Subsingleton (Ext P R.complex.X₁ 1)] [Subsingleton (Ext P R.complex.X₁ 2)]
    [Subsingleton (Ext P R.complex.X₂ 1)]
    [Subsingleton (Ext P S.complex.X₁ 1)] [Subsingleton (Ext P S.complex.X₁ 2)]
    [Subsingleton (Ext P S.complex.X₂ 1)] :
    (extFunctorObj P 2).map φ.augmentation ≫ (S.extTwoIso P).hom =
      (R.extTwoIso P).hom ≫ φ.extCokernelMap P := by
  have : Epi (AddCommGrpCat.ofHom (R.connectingTwo P)) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr (R.connectingTwo_surjective P)
  exact comparison_naturality_of_epi
    (AddCommGrpCat.ofHom (R.connectingTwo P)) (AddCommGrpCat.ofHom (S.connectingTwo P))
    (R.extTwoIso P).hom (S.extTwoIso P).hom
    (cokernel.π (R.extZeroComplex P).g) (cokernel.π (S.extZeroComplex P).g)
    ((extFunctorObj P 0).map φ.complex.τ₃) ((extFunctorObj P 2).map φ.augmentation)
    (φ.extCokernelMap P) (φ.connectingTwo_naturality P)
    (R.extTwoIso_connecting P) (S.extTwoIso_connecting P) (φ.extCokernelMap_π P).symm

end AugmentedResolution.Hom

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
