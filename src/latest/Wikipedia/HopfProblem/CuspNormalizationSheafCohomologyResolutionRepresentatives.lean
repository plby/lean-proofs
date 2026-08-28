import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionZero
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtRepresentatives

/-!
# Literal global-section representatives of genuine sheaf cohomology

Both comparisons retain the actual Ext connecting maps. A section of
the intermediate kernel gives its ordinary homology class in degree
one, and a section of the last term gives its ordinary cokernel class
in degree two.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

/-- Precomposing a surjective group map by the inverse of an actual
isomorphism remains surjective. -/
theorem surjective_iso_inv_comp {A B D : AddCommGrpCat.{0}}
    (e : A ≅ B) (f : A ⟶ D) (hf : Function.Surjective f) :
    Function.Surjective (e.inv ≫ f) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  refine ⟨e.hom y, ?_⟩
  exact (congrArg f (ConcreteCategory.congr_hom e.hom_inv_id y)).trans hy

namespace AugmentedResolution

variable {X : TopCat.{0}} (R : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X))

/-- Literal global sections of the actual kernel give actual cycles. -/
def globalCycleMap : (globalSectionsFunctor X).obj R.K ⟶ R.globalComplex.cycles :=
  R.globalComplex.liftCycles ((globalSectionsFunctor X).map (kernel.ι R.complex.g))
    (R.second.map (globalSectionsFunctor X)).zero

@[reassoc] theorem globalCycleMap_i :
    R.globalCycleMap ≫ R.globalComplex.iCycles =
      (globalSectionsFunctor X).map (kernel.ι R.complex.g) :=
  R.globalComplex.liftCycles_i _ _

/-- The actual degree-zero comparison carries the kernel section
to the same literal global cycle. -/
theorem extCycleMap_global :
    (h0GlobalIso R.K).inv ≫ R.extCycleMap (unitSheaf X) ≫
        ShortComplex.cyclesMap R.extZeroGlobalIso.hom = R.globalCycleMap := by
  apply (cancel_mono R.globalComplex.iCycles).mp
  have hcycles : ShortComplex.cyclesMap R.extZeroGlobalIso.hom ≫ R.globalComplex.iCycles =
      (R.extZeroComplex (unitSheaf X)).iCycles ≫ (h0GlobalIso R.complex.X₂).hom :=
    ShortComplex.cyclesMap_i R.extZeroGlobalIso.hom
  have h₁ : ((h0GlobalIso R.K).inv ≫ R.extCycleMap (unitSheaf X) ≫
        ShortComplex.cyclesMap R.extZeroGlobalIso.hom) ≫ R.globalComplex.iCycles =
        (h0GlobalIso R.K).inv ≫
          (R.extCycleMap (unitSheaf X) ≫ (R.extZeroComplex (unitSheaf X)).iCycles) ≫
            (h0GlobalIso R.complex.X₂).hom := by
      exact (Category.assoc _ _ _).trans
        (congrArg (fun k => (h0GlobalIso R.K).inv ≫ k)
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => R.extCycleMap (unitSheaf X) ≫ k) hcycles).trans
              (Category.assoc _ _ _).symm)))
  have h₂ : (h0GlobalIso R.K).inv ≫
          (R.extCycleMap (unitSheaf X) ≫ (R.extZeroComplex (unitSheaf X)).iCycles) ≫
            (h0GlobalIso R.complex.X₂).hom = (h0GlobalIso R.K).inv ≫
        (extFunctorObj (unitSheaf X) 0).map (kernel.ι R.complex.g) ≫
          (h0GlobalIso R.complex.X₂).hom := by
      exact congrArg (fun k => (h0GlobalIso R.K).inv ≫ k ≫ (h0GlobalIso R.complex.X₂).hom)
        (R.extCycleMap_i (unitSheaf X))
  have h₃ : (h0GlobalIso R.K).inv ≫
        (extFunctorObj (unitSheaf X) 0).map (kernel.ι R.complex.g) ≫
          (h0GlobalIso R.complex.X₂).hom =
      (globalSectionsFunctor X).map (kernel.ι R.complex.g) := by
      exact (congrArg (fun k => (h0GlobalIso R.K).inv ≫ k)
        (h0GlobalIso_naturality (kernel.ι R.complex.g))).trans
          ((h0GlobalIso R.K).inv_hom_id_assoc _)
  exact h₁.trans (h₂.trans (h₃.trans R.globalCycleMap_i.symm))

/-- The actual connecting map on a literal global kernel section. -/
def globalConnectingOne : (globalSectionsFunctor X).obj R.K ⟶
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 1) :=
  (h0GlobalIso R.K).inv ≫ AddCommGrpCat.ofHom (connecting (unitSheaf X) R.first_shortExact 0)

/-- Every actual degree-one class has a global-kernel-section
representative when the first term is acyclic in degree one. -/
theorem globalConnectingOne_surjective
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)] :
    Function.Surjective R.globalConnectingOne := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  exact surjective_iso_inv_comp (h0GlobalIso R.K)
    (AddCommGrpCat.ofHom (connecting (unitSheaf X) R.first_shortExact 0))
    (connecting_surjective (unitSheaf X) R.first_shortExact 0)

/-- The comparison sends a genuine degree-one connecting class to
the class of the corresponding literal global cycle. -/
theorem h1Iso_connecting
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)] :
    R.globalConnectingOne ≫ R.h1Iso.hom = R.globalCycleMap ≫ R.globalComplex.homologyπ := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  calc
    R.globalConnectingOne ≫ R.h1Iso.hom =
        (h0GlobalIso R.K).inv ≫
          (AddCommGrpCat.ofHom (connecting (unitSheaf X) R.first_shortExact 0) ≫
            (R.extOneIso (unitSheaf X)).hom) ≫
              ShortComplex.homologyMap R.extZeroGlobalIso.hom := by
      change ((h0GlobalIso R.K).inv ≫
          AddCommGrpCat.ofHom (connecting (unitSheaf X) R.first_shortExact 0)) ≫
          ((R.extOneIso (unitSheaf X)).hom ≫
            ShortComplex.homologyMap R.extZeroGlobalIso.hom) = _
      simp only [Category.assoc]
    _ = (h0GlobalIso R.K).inv ≫
        (R.extCycleMap (unitSheaf X) ≫ (R.extZeroComplex (unitSheaf X)).homologyπ) ≫
          ShortComplex.homologyMap R.extZeroGlobalIso.hom := by
      rw [R.extOneIso_connecting_cycle]
    _ = (h0GlobalIso R.K).inv ≫ R.extCycleMap (unitSheaf X) ≫
        ShortComplex.cyclesMap R.extZeroGlobalIso.hom ≫ R.globalComplex.homologyπ := by
      rw [Category.assoc, ShortComplex.homologyπ_naturality]
    _ = R.globalCycleMap ≫ R.globalComplex.homologyπ := by
      simpa only [Category.assoc] using
        congrArg (fun f => f ≫ R.globalComplex.homologyπ) R.extCycleMap_global

/-- The actual composite connecting map on a global section of the
last sheaf term. -/
def globalConnectingTwo : (globalSectionsFunctor X).obj R.complex.X₃ ⟶
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} R.F 2) :=
  (h0GlobalIso R.complex.X₃).inv ≫ AddCommGrpCat.ofHom (R.connectingTwo (unitSheaf X))

/-- The global degree-two representative map is onto under precisely
the required degree-two and degree-one acyclicity hypotheses. -/
theorem globalConnectingTwo_surjective
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    Function.Surjective R.globalConnectingTwo := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  exact surjective_iso_inv_comp (h0GlobalIso R.complex.X₃)
    (AddCommGrpCat.ofHom (R.connectingTwo (unitSheaf X)))
    (R.connectingTwo_surjective (unitSheaf X))

/-- The degree-two comparison sends the genuine double connecting
class of a literal section to its ordinary cokernel class. -/
theorem h2Iso_connecting
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)]
    [Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)] :
    R.globalConnectingTwo ≫ R.h2Iso.hom = cokernel.π R.globalComplex.g := by
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 1)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₁ 2) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₁ 2)›
  let : Subsingleton (Ext.{0} (unitSheaf X) R.complex.X₂ 1) :=
    ‹Subsingleton (CategoryTheory.Sheaf.H.{0} R.complex.X₂ 1)›
  let e := cokernel.mapIso (R.extZeroComplex (unitSheaf X)).g R.globalComplex.g
    (h0GlobalIso R.complex.X₂) (h0GlobalIso R.complex.X₃)
    (h0GlobalIso_naturality R.complex.g)
  have hπ : cokernel.π (R.extZeroComplex (unitSheaf X)).g ≫ e.hom =
      (h0GlobalIso R.complex.X₃).hom ≫ cokernel.π R.globalComplex.g :=
    cokernel.π_desc _ _ _
  have h₁ : R.globalConnectingTwo ≫ R.h2Iso.hom =
        (h0GlobalIso R.complex.X₃).inv ≫
          (AddCommGrpCat.ofHom (R.connectingTwo (unitSheaf X)) ≫
            (R.extTwoIso (unitSheaf X)).hom) ≫ e.hom := by
      change ((h0GlobalIso R.complex.X₃).inv ≫
          AddCommGrpCat.ofHom (R.connectingTwo (unitSheaf X))) ≫
          ((R.extTwoIso (unitSheaf X)).hom ≫ e.hom) = _
      simp only [Category.assoc]
  have h₂ : (h0GlobalIso R.complex.X₃).inv ≫
          (AddCommGrpCat.ofHom (R.connectingTwo (unitSheaf X)) ≫
            (R.extTwoIso (unitSheaf X)).hom) ≫ e.hom =
      (h0GlobalIso R.complex.X₃).inv ≫
        cokernel.π (R.extZeroComplex (unitSheaf X)).g ≫ e.hom := by
      rw [R.extTwoIso_connecting]
  have h₃ : (h0GlobalIso R.complex.X₃).inv ≫
        cokernel.π (R.extZeroComplex (unitSheaf X)).g ≫ e.hom =
      (h0GlobalIso R.complex.X₃).inv ≫
        (h0GlobalIso R.complex.X₃).hom ≫ cokernel.π R.globalComplex.g := by
      exact congrArg (fun k => (h0GlobalIso R.complex.X₃).inv ≫ k) hπ
  exact h₁.trans (h₂.trans (h₃.trans ((h0GlobalIso R.complex.X₃).inv_hom_id_assoc _)))

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
