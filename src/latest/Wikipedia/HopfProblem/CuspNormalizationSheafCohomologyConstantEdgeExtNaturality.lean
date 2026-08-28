import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyConstantEdgeExt

/-!
# Naturality of the genuine edge-kernel comparison

The kernel map is induced by the original degree-two Ext maps. Its
naturality is proved using the actual double-connecting representatives.
The mixed comparison allows the target's first term to be Ext²-acyclic
without imposing this false requirement on a constant source resolution.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge

open SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {R S : AugmentedResolution C} (φ : R.Hom S) (P : C)

theorem extEdgeMap_naturality :
    (extFunctorObj P 2).map φ.augmentation ≫ extEdgeMap S P =
      extEdgeMap R P ≫ (extFunctorObj P 2).map φ.complex.τ₁ := by
  exact Eq.trans ((extFunctorObj P 2).map_comp φ.augmentation S.ι).symm
    (Eq.trans (congrArg (fun f : R.F ⟶ S.complex.X₁ => (extFunctorObj P 2).map f) φ.comm)
      ((extFunctorObj P 2).map_comp R.ι φ.complex.τ₁))

/-- The literal kernel map induced by the actual degree-two Ext map. -/
def extEdgeKernelMap : kernel (extEdgeMap R P) ⟶ kernel (extEdgeMap S P) :=
  kernel.map (extEdgeMap R P) (extEdgeMap S P)
    ((extFunctorObj P 2).map φ.augmentation) ((extFunctorObj P 2).map φ.complex.τ₁)
    (extEdgeMap_naturality φ P).symm

@[reassoc] theorem extEdgeKernelMap_ι :
    extEdgeKernelMap φ P ≫ kernel.ι (extEdgeMap S P) =
      kernel.ι (extEdgeMap R P) ≫ (extFunctorObj P 2).map φ.augmentation :=
  kernel.lift_ι _ _ _

theorem extEdgeConnecting_naturality :
    (extFunctorObj P 0).map φ.complex.τ₃ ≫ extEdgeConnecting S P =
      extEdgeConnecting R P ≫ extEdgeKernelMap φ P := by
  apply (cancel_mono (kernel.ι (extEdgeMap S P))).mp
  have hl : ((extFunctorObj P 0).map φ.complex.τ₃ ≫ extEdgeConnecting S P) ≫
      kernel.ι (extEdgeMap S P) =
        (extFunctorObj P 0).map φ.complex.τ₃ ≫ AddCommGrpCat.ofHom (S.connectingTwo P) :=
    Eq.trans (Category.assoc _ _ _)
      (congrArg (fun f => (extFunctorObj P 0).map φ.complex.τ₃ ≫ f)
        (extEdgeConnecting_ι S P))
  have hr : (extEdgeConnecting R P ≫ extEdgeKernelMap φ P) ≫
      kernel.ι (extEdgeMap S P) =
        AddCommGrpCat.ofHom (R.connectingTwo P) ≫ (extFunctorObj P 2).map φ.augmentation :=
    Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg (fun f => extEdgeConnecting R P ≫ f) (extEdgeKernelMap_ι φ P))
        (Eq.trans (Category.assoc _ _ _).symm
          (congrArg (fun f => f ≫ (extFunctorObj P 2).map φ.augmentation)
            (extEdgeConnecting_ι R P))))
  exact hl.trans ((φ.connectingTwo_naturality P).trans hr.symm)

/-- The actual edge-kernel comparison commutes with every actual
resolution morphism, assuming only degree-one term vanishings. -/
theorem extEdgeIso_naturality
    [Subsingleton (Ext P R.complex.X₁ 1)] [Subsingleton (Ext P R.complex.X₂ 1)]
    [Subsingleton (Ext P S.complex.X₁ 1)] [Subsingleton (Ext P S.complex.X₂ 1)] :
    extEdgeKernelMap φ P ≫ (extEdgeIso S P).hom =
      (extEdgeIso R P).hom ≫ φ.extCokernelMap P := by
  have := extEdgeConnecting_epi R P
  exact comparison_naturality_of_epi
    (extEdgeConnecting R P) (extEdgeConnecting S P) (extEdgeIso R P).hom (extEdgeIso S P).hom
    (cokernel.π (R.extZeroComplex P).g) (cokernel.π (S.extZeroComplex P).g)
    ((extFunctorObj P 0).map φ.complex.τ₃) (extEdgeKernelMap φ P) (φ.extCokernelMap P)
    (extEdgeConnecting_naturality φ P) (extEdgeIso_connecting R P) (extEdgeIso_connecting S P)
    (φ.extCokernelMap_π P).symm

/-- The actual degree-two map, restricted to the source's literal edge kernel. -/
def extEdgeToCohomology : kernel (extEdgeMap R P) ⟶ AddCommGrpCat.of (Ext P S.F 2) :=
  kernel.ι (extEdgeMap R P) ≫ (extFunctorObj P 2).map φ.augmentation

/-- Mixed comparison with a target whose first term really is Ext²-acyclic.
No Ext² acyclicity of the source's first term is required. -/
theorem extEdgeToCohomology_naturality
    [Subsingleton (Ext P R.complex.X₁ 1)] [Subsingleton (Ext P R.complex.X₂ 1)]
    [Subsingleton (Ext P S.complex.X₁ 1)] [Subsingleton (Ext P S.complex.X₁ 2)]
    [Subsingleton (Ext P S.complex.X₂ 1)] :
    extEdgeToCohomology φ P ≫ (S.extTwoIso P).hom =
      (extEdgeIso R P).hom ≫ φ.extCokernelMap P := by
  have := extEdgeConnecting_epi R P
  have hc : (extFunctorObj P 0).map φ.complex.τ₃ ≫ AddCommGrpCat.ofHom (S.connectingTwo P) =
      extEdgeConnecting R P ≫ extEdgeToCohomology φ P :=
    Eq.trans (φ.connectingTwo_naturality P)
      (Eq.trans (congrArg (fun f => f ≫ (extFunctorObj P 2).map φ.augmentation)
        (extEdgeConnecting_ι R P).symm) (Category.assoc _ _ _))
  exact comparison_naturality_of_epi
    (extEdgeConnecting R P) (AddCommGrpCat.ofHom (S.connectingTwo P))
    (extEdgeIso R P).hom (S.extTwoIso P).hom
    (cokernel.π (R.extZeroComplex P).g) (cokernel.π (S.extZeroComplex P).g)
    ((extFunctorObj P 0).map φ.complex.τ₃) (extEdgeToCohomology φ P) (φ.extCokernelMap P)
    hc (extEdgeIso_connecting R P) (S.extTwoIso_connecting P) (φ.extCokernelMap_π P).symm

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyConstantEdge
