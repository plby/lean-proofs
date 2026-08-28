import Wikipedia.HopfProblem.SheafHigherDirectImageExtBasic

/-!
# Ext representatives and native homology classes

The existing injective-resolution computation of Ext is compared with
actual categorical homology.  The formula on cocycles fixes the
comparison and will make its compatibility with restriction maps
explicit.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u

theorem shortCycleClass_eq_leftHomologyData
    (S : ShortComplex AddCommGrpCat.{0}) (h : S.LeftHomologyData)
    (z : h.K) (hz : S.g (h.i z) = 0) :
    shortCycleClass S (h.i z) hz = h.homologyIso.inv (h.π z) := by
  have hc : S.abCyclesIso.inv ⟨h.i z, hz⟩ = h.cyclesIso.inv z := by
    apply (AddCommGrpCat.mono_iff_injective S.iCycles).mp inferInstance
    rw [ShortComplex.abCyclesIso_inv_apply_iCycles]
    exact (ConcreteCategory.congr_hom h.cyclesIso_inv_comp_iCycles z).symm
  unfold shortCycleClass
  rw [hc]
  exact (ConcreteCategory.congr_hom h.π_comp_homologyIso_inv z).symm

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- The quotient cocycle class agrees with native categorical homology. -/
theorem homologyAddEquiv_symm_mk (K L : CochainComplex C ℤ) (n : ℤ)
    (z : Cocycle K L n) :
    (homologyAddEquiv K L n).symm (CohomologyClass.mk z) =
      cycleClass (CochainComplex.HomComplex K L) n (z : Cochain K L n)
        (Cocycle.δ_eq_zero z _) := by
  exact (shortCycleClass_eq_leftHomologyData
    ((CochainComplex.HomComplex K L).sc n) (leftHomologyData K L n)
    z (Cocycle.δ_eq_zero z _)).symm

/-- The complex comparison sends a single-object cocycle to its original morphism. -/
theorem singleHomComplexIso_hom_cohomologyClass_mk_fromSingle
    (A : C) (K : CochainComplex C ℤ) (n m : ℤ) (hm : n + 1 = m)
    (f : A ⟶ K.X n) (hf : f ≫ K.d n m = 0)
    (hf' : ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj K).sc n).g
      f = 0) :
    HomologicalComplex.homologyMap (singleHomComplexIso A K).hom n
      ((homologyAddEquiv ((CochainComplex.singleFunctor C 0).obj A) K n).symm
        (CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) m hm hf))) =
      cycleClass (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj K)
        n f hf' := by
  rw [homologyAddEquiv_symm_mk]
  simpa only [singleHomComplexIso_hom_f, Cocycle.fromSingleMk_coe,
    Cochain.fromSingleEquiv_fromSingleMk] using
    homologyMap_cycleClass (singleHomComplexIso A K).hom n
      ((Cocycle.fromSingleMk f (zero_add n) m hm hf :
        Cocycle ((CochainComplex.singleFunctor C 0).obj A) K n) :
        Cochain ((CochainComplex.singleFunctor C 0).obj A) K n)
      (Cocycle.δ_eq_zero _ _)
      (by simpa only [singleHomComplexIso_hom_f, Cocycle.fromSingleMk_coe,
        Cochain.fromSingleEquiv_fromSingleMk] using hf')

variable {F : C} (R : InjectiveResolution F)

/-- A resolution cocycle is still a cocycle after extension to integer degrees. -/
theorem extMk_extended_isCycle {A : C} {n : ℕ}
    (f : A ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
      R.cochainComplex).sc (n : ℤ)).g (f ≫ (R.cochainComplexXIso n n rfl).inv) = 0 := by
  change (f ≫ (R.cochainComplexXIso n n rfl).inv) ≫
    R.cochainComplex.d (n : ℤ) ((ComplexShape.up ℤ).next n) = 0
  rw [CochainComplex.next]
  have hm' : (n : ℤ) + 1 = (m : ℤ) := by exact_mod_cast hm
  rw [hm', R.cochainComplex_d _ _ n m rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% hf, zero_comp]

variable [HasExt.{0} C]

/-- Ext computed by the literal coyoneda complex of the extended resolution. -/
def extExtendedHomologyIso (A : C) (n : ℕ) :
    AddCommGrpCat.of (Ext A F n) ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
        R.cochainComplex).homology n :=
  (R.extAddEquivCohomologyClass.toAddCommGrpIso :
    AddCommGrpCat.of (Ext A F n) ≅ AddCommGrpCat.of
      (CohomologyClass ((CochainComplex.singleFunctor C 0).obj A) R.cochainComplex n)) ≪≫
    (homologyAddEquiv ((CochainComplex.singleFunctor C 0).obj A)
      R.cochainComplex n).symm.toAddCommGrpIso ≪≫
    HomologicalComplex.homologyMapIso (singleHomComplexIso A R.cochainComplex) n

/-- Formula on the original injective-resolution representative of an Ext class. -/
theorem extExtendedHomologyIso_hom_extMk {A : C} {n : ℕ}
    (f : A ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0)
    (hf' : ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
      R.cochainComplex).sc (n : ℤ)).g (f ≫ (R.cochainComplexXIso n n rfl).inv) = 0) :
    (extExtendedHomologyIso R A n).hom (R.extMk f m hm hf) =
      cycleClass (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
        R.cochainComplex) (n : ℤ) (f ≫ (R.cochainComplexXIso n n rfl).inv) hf' := by
  change HomologicalComplex.homologyMap (singleHomComplexIso A R.cochainComplex).hom
    (n : ℤ) ((homologyAddEquiv ((CochainComplex.singleFunctor C 0).obj A)
      R.cochainComplex (n : ℤ)).symm
        (R.extEquivCohomologyClass (R.extMk f m hm hf))) = _
  rw [R.extEquivCohomologyClass_extMk]
  exact singleHomComplexIso_hom_cohomologyClass_mk_fromSingle A R.cochainComplex
    n m (by exact_mod_cast hm) (f ≫ (R.cochainComplexXIso n n rfl).inv) _ hf'

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge
