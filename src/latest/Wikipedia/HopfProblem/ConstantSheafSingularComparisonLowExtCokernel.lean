import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtCokernelBasic
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The mapped cycle cokernel is genuine degree-two cohomology

This specializes the kernel-preservation comparison to the actual
degree-one, degree-two and degree-three terms of a cochain complex.
The comparison is natural for the actual cochain maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt.CycleCokernel

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- The literal differential into the categorical degree-two cycles. -/
def toCycles₂ (K : CochainComplex C ℕ) : K.X 1 ⟶ kernel (K.d 2 3) :=
  kernel.lift (K.d 2 3) (K.d 1 2) (K.d_comp_d 1 2 3)

/-- The canonical native comparison between degree-two homology and
the three consecutive terms that compute it. -/
def windowHomologyIso₂ (K : CochainComplex D ℕ) :
    K.homology 2 ≅ (K.sc' 1 2 3).homology :=
  (HomologicalComplex.homologyFunctorIso' D (ComplexShape.up ℕ) 1 2 3
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))).app K

@[reassoc] theorem windowHomologyIso₂_inv_naturality
    {K L : CochainComplex D ℕ} (φ : K ⟶ L) :
    ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' D (ComplexShape.up ℕ) 1 2 3).map φ) ≫
          (windowHomologyIso₂ L).inv =
      (windowHomologyIso₂ K).inv ≫ HomologicalComplex.homologyMap φ 2 :=
  (HomologicalComplex.homologyFunctorIso' D (ComplexShape.up ℕ) 1 2 3
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))).inv.naturality φ

variable (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]

/-- The cokernel of the mapped boundary into the original kernel is
the actual degree-two homology of the mapped full complex. -/
def cokernelIsoHomology₂ (K : CochainComplex C ℕ) :
    cokernel (G.map (toCycles₂ K)) ≅
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homology 2 :=
  shortCokernelIsoHomology G (K.sc' 1 2 3) ≪≫
    (windowHomologyIso₂ ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)).symm

variable {K L : CochainComplex C ℕ}

/-- The actual induced map on the categorical degree-two kernels. -/
def kernelMap₂ (φ : K ⟶ L) : kernel (K.d 2 3) ⟶ kernel (L.d 2 3) :=
  kernel.map (K.d 2 3) (L.d 2 3) (φ.f 2) (φ.f 3) (φ.comm 2 3).symm

@[reassoc] theorem toCycles₂_naturality (φ : K ⟶ L) :
    toCycles₂ K ≫ kernelMap₂ φ = φ.f 1 ≫ toCycles₂ L :=
  toKernel_naturality
    ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 1 2 3).map φ)

/-- The cokernel map is induced by the actual degree-one and kernel
components of the cochain map. -/
def mappedCokernelMap₂ (φ : K ⟶ L) :
    cokernel (G.map (toCycles₂ K)) ⟶ cokernel (G.map (toCycles₂ L)) :=
  mappedCokernelMap G
    ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 1 2 3).map φ)

omit [G.Additive] [PreservesFiniteLimits G] in
theorem mappedCokernelMap₂_eq (φ : K ⟶ L) :
    mappedCokernelMap₂ G φ =
      cokernel.map (G.map (toCycles₂ K)) (G.map (toCycles₂ L))
        (G.map (φ.f 1)) (G.map (kernelMap₂ φ))
          (by simp only [← G.map_comp, toCycles₂_naturality]) := rfl

/-- Naturality for the genuine maps on degree-two cohomology. -/
@[reassoc] theorem cokernelIsoHomology₂_hom_naturality (φ : K ⟶ L) :
    mappedCokernelMap₂ G φ ≫ (cokernelIsoHomology₂ G L).hom =
      (cokernelIsoHomology₂ G K).hom ≫
        HomologicalComplex.homologyMap
          ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) 2 := by
  let φ' := (HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 1 2 3).map φ
  let K' := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let L' := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj L
  let f := (G.mapHomologicalComplex (ComplexShape.up ℕ)).map φ
  let aK := shortCokernelIsoHomology G (K.sc' 1 2 3)
  let aL := shortCokernelIsoHomology G (L.sc' 1 2 3)
  let bK := windowHomologyIso₂ K'
  let bL := windowHomologyIso₂ L'
  change mappedCokernelMap G φ' ≫ (aL.hom ≫ bL.inv) =
    (aK.hom ≫ bK.inv) ≫ HomologicalComplex.homologyMap f 2
  calc
    _ = (mappedCokernelMap G φ' ≫ aL.hom) ≫ bL.inv :=
      (Category.assoc _ _ _).symm
    _ = (aK.hom ≫ ShortComplex.homologyMap (G.mapShortComplex.map φ')) ≫ bL.inv :=
      congrArg (fun h => h ≫ bL.inv) (shortCokernelIsoHomology_hom_naturality G φ')
    _ = aK.hom ≫
        (ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor' D (ComplexShape.up ℕ) 1 2 3).map f) ≫
            bL.inv) := Category.assoc _ _ _
    _ = aK.hom ≫ (bK.inv ≫ HomologicalComplex.homologyMap f 2) :=
      congrArg (fun h => aK.hom ≫ h) (windowHomologyIso₂_inv_naturality f)
    _ = _ := (Category.assoc _ _ _).symm

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt.CycleCokernel
