import Wikipedia.HopfProblem.SheafLerayLowDegreesAbstractResolution
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Native first homology of a section complex

The additive coyoneda functor preserves kernels.  Consequently the native
first homology of its image of a cochain complex is the cokernel of the
section map into degree-one cycles.  The comparison below is constructed
from the actual limiting kernel forks and colimiting cokernel coforks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits Opposite
open HomologicalComplex

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- The actual cochain complex obtained by applying additive coyoneda. -/
abbrev homComplex (A : C) (K : CochainComplex C ℕ) : CochainComplex AddCommGrpCat ℕ :=
  ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj K

/-- Applying Hom to the native low-degree augmented complex. -/
abbrev homAugmentedComplex (A : C) (K : CochainComplex C ℕ) : ShortComplex AddCommGrpCat :=
  (complex K).map (preadditiveCoyoneda.obj (op A))

/-- Hom carries the actual cycles kernel to the cycles kernel of the section complex. -/
def homCyclesIso (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (preadditiveCoyoneda.obj (op A)).obj (K.cycles n) ≅ (homComplex A K).cycles n :=
  IsLimit.conePointUniqueUpToIso
    (KernelFork.mapIsLimit
      (KernelFork.ofι (K.iCycles n) (K.iCycles_d n ((ComplexShape.up ℕ).next n)))
      (K.cyclesIsKernel n _ rfl) (preadditiveCoyoneda.obj (op A)))
    ((homComplex A K).cyclesIsKernel n _ rfl)

/-- The kernel comparison preserves the actual inclusion of cycle representatives. -/
@[reassoc (attr := simp)]
theorem homCyclesIso_hom_iCycles (A : C) (K : CochainComplex C ℕ) (n : ℕ) :
    (homCyclesIso A K n).hom ≫ (homComplex A K).iCycles n =
      (preadditiveCoyoneda.obj (op A)).map (K.iCycles n) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The section differential into cycles is the native boundary map under the kernel comparison. -/
@[reassoc (attr := simp)]
theorem map_toCycles_homCyclesIso (A : C) (K : CochainComplex C ℕ) (i j : ℕ) :
    (preadditiveCoyoneda.obj (op A)).map (K.toCycles i j) ≫ (homCyclesIso A K j).hom =
      (homComplex A K).toCycles i j := by
  apply (cancel_mono ((homComplex A K).iCycles j)).mp
  let F := preadditiveCoyoneda.obj (op A)
  exact (assoc _ _ _).trans
    ((congrArg (fun f => F.map (K.toCycles i j) ≫ f)
      (homCyclesIso_hom_iCycles A K j)).trans
      ((F.map_comp _ _).symm.trans
        ((congrArg F.map (K.toCycles_i i j)).trans
          ((homComplex A K).toCycles_i i j).symm)))

/-- The genuine Hom-cokernel of the low-degree augmented complex is native first homology. -/
def homMiddleIso (A : C) (K : CochainComplex C ℕ) :
    (homAugmentedComplex A K).opcycles ≅ (homComplex A K).homology 1 :=
  CokernelCofork.mapIsoOfIsColimit
    (homAugmentedComplex A K).opcyclesIsCokernel
    ((homComplex A K).homologyIsCokernel 0 1 (CochainComplex.prev_nat_succ 0))
    (Arrow.isoMk (Iso.refl _) (homCyclesIso A K 1)
      (by exact (id_comp _).trans (map_toCycles_homCyclesIso A K 0 1).symm))

/-- Quotient classes correspond to native cycle classes. -/
@[reassoc (attr := simp)]
theorem pOpcycles_homMiddleIso_hom (A : C) (K : CochainComplex C ℕ) :
    (homAugmentedComplex A K).pOpcycles ≫ (homMiddleIso A K).hom =
      (homCyclesIso A K 1).hom ≫ (homComplex A K).homologyπ 1 :=
  CokernelCofork.π_mapOfIsColimit (homAugmentedComplex A K).opcyclesIsCokernel _ _

/-- The inverse comparison carries native cycle classes back to the augmented cokernel. -/
@[reassoc (attr := simp)]
theorem homCyclesIso_hom_homologyπ_homMiddleIso_inv (A : C) (K : CochainComplex C ℕ) :
    (homCyclesIso A K 1).hom ≫ (homComplex A K).homologyπ 1 ≫
        (homMiddleIso A K).inv = (homAugmentedComplex A K).pOpcycles := by
  exact (assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (homMiddleIso A K).inv)
      (pOpcycles_homMiddleIso_hom A K).symm).trans
      ((assoc _ _ _).trans
        ((congrArg (fun f => (homAugmentedComplex A K).pOpcycles ≫ f)
          (homMiddleIso A K).hom_inv_id).trans (comp_id _))))

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Abstract
