import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractHomology
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractCoreNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractResolutionMap

/-!
# Naturality of the native middle homology comparison

The kernel comparison commutes with the actual maps on cycles.  The
quotient-class formula then proves that the middle comparison commutes
with genuine maps of cochain complexes, and hence with their native
maps on homology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Abelian Opposite
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]
  (A : C) {K L : CochainComplex C ℕ} (φ : K ⟶ L)

/-- Hom carries the native map on cycles to the cycles map of the Hom complex. -/
@[reassoc]
theorem homCyclesIso_hom_naturality (n : ℕ) :
    (preadditiveCoyoneda.obj (op A)).map (cyclesMap φ n) ≫ (homCyclesIso A L n).hom =
      (homCyclesIso A K n).hom ≫ cyclesMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) n := by
  let F := preadditiveCoyoneda.obj (op A)
  let ψ := (F.mapHomologicalComplex (.up ℕ)).map φ
  apply (cancel_mono ((homComplex A L).iCycles n)).mp
  have hl : (F.map (cyclesMap φ n) ≫ (homCyclesIso A L n).hom) ≫
      (homComplex A L).iCycles n = F.map (K.iCycles n) ≫ F.map (φ.f n) :=
    (assoc _ _ _).trans
      ((congrArg (fun f => F.map (cyclesMap φ n) ≫ f)
        (homCyclesIso_hom_iCycles A L n)).trans
        ((F.map_comp _ _).symm.trans
          ((congrArg F.map (cyclesMap_i φ n)).trans (F.map_comp _ _))))
  have hr : ((homCyclesIso A K n).hom ≫ cyclesMap ψ n) ≫
      (homComplex A L).iCycles n = F.map (K.iCycles n) ≫ F.map (φ.f n) :=
    (assoc _ _ _).trans
      ((congrArg (fun f => (homCyclesIso A K n).hom ≫ f) (cyclesMap_i ψ n)).trans
        ((assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ F.map (φ.f n)) (homCyclesIso_hom_iCycles A K n))))
  exact hl.trans hr.symm

variable [HasExt.{0} C]

/-- The actual middle cokernel comparison is natural for genuine cochain maps. -/
@[reassoc]
theorem middleIso_hom_naturality :
    Core.middleMap A (resolutionMap φ) ≫ (middleIso A L).hom =
      (middleIso A K).hom ≫ homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) 1 := by
  let F := preadditiveCoyoneda.obj (op A)
  let ψ := (F.mapHomologicalComplex (.up ℕ)).map φ
  apply (cancel_epi ((resolution K).extZeroComplex A).pOpcycles).mp
  apply AddCommGrpCat.ext
  intro x
  have h₀ := ConcreteCategory.congr_hom
    (ShortComplex.p_opcyclesMap ((resolutionMap φ).extZeroMap A)) x
  have h₁ := ConcreteCategory.congr_hom (pOpcycles_middleIso_hom A L)
    ((extFunctorObj A 0).map (cyclesMap φ 1) x)
  have h₂ := ConcreteCategory.congr_hom
    (extZeroHomIso_hom_naturality A (cyclesMap φ 1)) x
  have h₃ := ConcreteCategory.congr_hom (homCyclesIso_hom_naturality A φ 1)
    ((extZeroHomIso A (K.cycles 1)).hom x)
  have h₄ := ConcreteCategory.congr_hom (homologyπ_naturality ψ 1)
    ((homCyclesIso A K 1).hom ((extZeroHomIso A (K.cycles 1)).hom x))
  have h₅ := ConcreteCategory.congr_hom (pOpcycles_middleIso_hom A K) x
  exact (congrArg (middleIso A L).hom h₀).trans
    (h₁.trans
      ((congrArg (fun z => (homComplex A L).homologyπ 1 ((homCyclesIso A L 1).hom z))
        h₂).trans
        ((congrArg ((homComplex A L).homologyπ 1) h₃).trans
          (h₄.symm.trans (congrArg (homologyMap ψ 1) h₅.symm)))))

/-- The inverse native comparison is natural as well. -/
@[reassoc]
theorem middleIso_inv_naturality :
    homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).map φ) 1 ≫
        (middleIso A L).inv =
      (middleIso A K).inv ≫ Core.middleMap A (resolutionMap φ) := by
  apply (cancel_epi (middleIso A K).hom).mp
  rw [← assoc, ← middleIso_hom_naturality, assoc, Iso.hom_inv_id, comp_id,
    ← assoc, Iso.hom_inv_id, id_comp]

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
