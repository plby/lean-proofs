import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupRowAcyclic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyNativeConnecting

/-!
# The actual degree-one row class retains the original marked coefficients

Global sections preserve the genuine kernel of the native top operator.
Thus every literal closed pair is an actual global kernel section, and
the original positive Ext connecting formula identifies its row class.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row

open PeriodTorusHolomorphicCohomology
open CuspNormalization.SheafCohomologyResolution

variable (p : PeriodDomain)

/-- Actual global kernel sections are exactly the literal closed coefficient pairs. -/
def globalOneKernelIso : GlobalKernelSections p ≅ AddCommGrpCat.of (oneComplex p).g.hom.ker :=
  PreservesKernel.iso (globalSectionsFunctor (TopCat.of p.Torus))
    (Dolbeault.resolution p).complex.g ≪≫
      AddCommGrpCat.kernelIsoKer ((globalSectionsFunctor (TopCat.of p.Torus)).map
        (Dolbeault.resolution p).complex.g)

theorem globalOneKernelIso_inv_ι :
    (globalOneKernelIso p).inv ≫
        (globalSectionsFunctor (TopCat.of p.Torus)).map
          (kernel.ι (Dolbeault.resolution p).complex.g) =
      AddCommGrpCat.ofHom (oneComplex p).g.hom.ker.subtype := by
  let G := globalSectionsFunctor (TopCat.of p.Torus)
  let f := (Dolbeault.resolution p).complex.g
  change ((AddCommGrpCat.kernelIsoKer (G.map f)).inv ≫
    (PreservesKernel.iso G f).inv) ≫ G.map (kernel.ι f) =
      AddCommGrpCat.ofHom (G.map f).hom.ker.subtype
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (AddCommGrpCat.kernelIsoKer (G.map f)).inv ≫ k)
      (PreservesKernel.iso_inv_ι G f)).trans (AddCommGrpCat.kernelIsoKer_inv_comp_ι (G.map f)))

/-- A given closed native pair defines its actual section of the old kernel sheaf. -/
def kernelSectionOfClosed (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) : GlobalKernelSections p :=
  (globalOneKernelIso p).inv ⟨s, hs⟩

@[simp] theorem nativeKernelSection_kernelSectionOfClosed
    (s : Dolbeault.PairSection p ⊤) (hs : Dolbeault.topSection p ⊤ s = 0) :
    nativeKernelSection p (kernelSectionOfClosed p s hs) = s :=
  ConcreteCategory.congr_hom (globalOneKernelIso_inv_ι p) ⟨s, hs⟩

/-- The old kernel section and the literal row pair give the same actual homology class. -/
theorem oneClass_kernel (k : GlobalKernelSections p) :
    oneClass p (nativeKernelSection p k) (nativeKernelSection_closed p k) =
      (Dolbeault.resolution p).globalComplex.homologyπ
        ((Dolbeault.resolution p).globalCycleMap k) := by
  apply congrArg (oneComplex p).homologyπ
  apply AddCommGrpCat.injective_of_mono (oneComplex p).iCycles
  exact (oneCycle_i p _ _).trans (globalCycleMap_nativeKernelSection p k).symm

/-- On every actual kernel section the native H¹ comparison has the original positive class. -/
theorem h1Iso_nativeKernelClass (k : GlobalKernelSections p) :
    (h1Iso p).hom
        (nativeH1Class p (nativeKernelSection p k) (nativeKernelSection_closed p k)) =
      oneClass p (nativeKernelSection p k) (nativeKernelSection_closed p k) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (Dolbeault.resolution p).complex.X₁ 1) :=
    Dolbeault.smooth_higher_subsingleton p 0
  rw [h1Iso_hom_eq_original, nativeH1Class_eq_globalConnectingOne]
  exact (ConcreteCategory.congr_hom (Dolbeault.resolution p).h1Iso_connecting k).trans
    (oneClass_kernel p k).symm

/-- Every original closed pair keeps its original native H¹ class under the actual row map. -/
theorem h1Iso_nativeClass (s : Dolbeault.PairSection p ⊤)
    (hs : Dolbeault.topSection p ⊤ s = 0) :
    (h1Iso p).hom (nativeH1Class p s hs) = oneClass p s hs := by
  simpa only [nativeKernelSection_kernelSectionOfClosed] using
    h1Iso_nativeKernelClass p (kernelSectionOfClosed p s hs)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Row
