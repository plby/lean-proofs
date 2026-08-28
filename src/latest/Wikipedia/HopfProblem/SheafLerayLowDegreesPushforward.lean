import Wikipedia.HopfProblem.SheafHigherDirectImageResolution
import Wikipedia.HopfProblem.SheafHigherDirectImageExt
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforwardComparison

/-!
# Global sections of an actual pushed-forward injective resolution

Global sections of the native pushforward are canonically the original
global sections, for every continuous map.  Applying this natural
comparison to a genuine injective resolution identifies source sheaf
cohomology with the Hom-complex cohomology used in the low-degree Leray
sequence.  The pushed-forward resolution is degreewise injective,
although it need not be a resolution of its degree-zero homology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees

open SheafHigherDirectImage
open CuspNormalization.SheafCohomologyFinitePushforward
  (integerSheaf homPushforwardEquiv homPushforwardEquiv_naturality integerUnit integerUnit_comp)

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The genuine global-Hom comparison, natural in every abelian sheaf.
There is no finiteness or closed-map hypothesis. -/
def globalHomPushforwardIso :
    preadditiveCoyoneda.obj (op (integerSheaf X)) ≅
      pushforward f ⋙ preadditiveCoyoneda.obj (op (integerSheaf Y)) :=
  NatIso.ofComponents
    (fun G => (homPushforwardEquiv f G).toAddCommGrpIso)
    (fun g => by
      ext h
      exact homPushforwardEquiv_naturality f h g)

@[simp] theorem globalHomPushforwardIso_hom_app (G : AbelianSheaf X)
    (h : integerSheaf X ⟶ G) :
    (globalHomPushforwardIso f).hom.app G h = homPushforwardEquiv f G h := rfl

/-- On actual morphisms the comparison is the canonical integer-sheaf
map followed by the native pushforward. -/
theorem globalHomPushforwardIso_hom_app_eq_integerUnit (G : AbelianSheaf X)
    (h : integerSheaf X ⟶ G) :
    (globalHomPushforwardIso f).hom.app G h = integerUnit f ≫ (pushforward f).map h :=
  (integerUnit_comp f h).symm

/-- The global-Hom comparison applied degreewise to an actual complex. -/
def globalHomComplexIso (K : CochainComplex (AbelianSheaf X) ℕ) :
    (((preadditiveCoyoneda.obj (op (integerSheaf X))).mapHomologicalComplex _).obj K) ≅
      (((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).obj
        (((pushforward f).mapHomologicalComplex _).obj K)) :=
  (NatIso.mapHomologicalComplex (globalHomPushforwardIso f) _).app K

@[simp] theorem globalHomComplexIso_hom_f
    (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) (h : integerSheaf X ⟶ K.X n) :
    (globalHomComplexIso f K).hom.f n h = homPushforwardEquiv f (K.X n) h := rfl

/-- The complex comparison commutes with genuine maps of complexes. -/
@[reassoc] theorem globalHomComplexIso_hom_naturality
    {K L : CochainComplex (AbelianSheaf X) ℕ} (φ : K ⟶ L) :
    ((preadditiveCoyoneda.obj (op (integerSheaf X))).mapHomologicalComplex _).map φ ≫
      (globalHomComplexIso f L).hom =
    (globalHomComplexIso f K).hom ≫
      ((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).map
        (((pushforward f).mapHomologicalComplex _).map φ) :=
  NatTrans.mapHomologicalComplex_naturality (globalHomPushforwardIso f).hom φ

/-- The comparison uses native cochain homology on both sides. -/
def globalHomComplexHomologyIso (K : CochainComplex (AbelianSheaf X) ℕ) (n : ℕ) :
    ((((preadditiveCoyoneda.obj (op (integerSheaf X))).mapHomologicalComplex _).obj K).homology n) ≅
      ((((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).obj
        (((pushforward f).mapHomologicalComplex _).obj K)).homology n) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℕ) n).mapIso
    (globalHomComplexIso f K)

/-- Genuine source sheaf cohomology is the global-Hom cohomology of
the actual pushed-forward injective resolution. -/
def sourceCohomologyIso (F : AbelianSheaf X) (I : InjectiveResolution F) (n : ℕ) :
    AddCommGrpCat.of (CategoryTheory.Sheaf.H.{0} F n) ≅
      ((((preadditiveCoyoneda.obj (op (integerSheaf Y))).mapHomologicalComplex _).obj
        (pushedResolution f I)).homology n) :=
  ExtBridge.extHomologyIso I (integerSheaf X) n ≪≫
    globalHomComplexHomologyIso f I.cocomplex n

/-- Each term is genuinely injective: arbitrary topological sheaf
pushforward preserves injectives by its exact left adjoint. -/
theorem pushedResolution_term_injective {F : AbelianSheaf X}
    (I : InjectiveResolution F) (n : ℕ) : Injective ((pushedResolution f I).X n) := by
  let _ : (pushforward f).PreservesInjectiveObjects :=
    CuspNormalization.SheafCohomologyFinitePushforward.pushforward_preservesInjectiveObjects f
  exact (pushforward f).injective_obj_of_injective (I.injective n)

end Wikipedia.HopfProblem.SheafLerayLowDegrees
