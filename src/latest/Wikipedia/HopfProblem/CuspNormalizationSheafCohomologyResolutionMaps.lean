import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExtRepresentatives

/-!
# Maps of actual augmented resolutions

A commuting map of the four genuine sheaf terms induces maps of the
two short exact sequences. Consequently its connecting maps commute,
including when these are actual scalar endomorphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace AugmentedResolution

/-- A genuine commuting map of augmented resolutions. -/
structure Hom (R S : AugmentedResolution C) where
  augmentation : R.F ⟶ S.F
  complex : R.complex ⟶ S.complex
  comm : augmentation ≫ S.ι = R.ι ≫ complex.τ₁

namespace Hom

variable {R S : AugmentedResolution C} (φ : Hom R S)

/-- The induced map of the actual intermediate kernels. -/
def kernelMap : R.K ⟶ S.K :=
  kernel.map R.complex.g S.complex.g φ.complex.τ₂ φ.complex.τ₃
    φ.complex.comm₂₃.symm

@[reassoc (attr := simp)] theorem kernelMap_ι :
    φ.kernelMap ≫ kernel.ι S.complex.g = kernel.ι R.complex.g ≫ φ.complex.τ₂ :=
  kernel.lift_ι _ _ _

theorem toK_kernelMap : R.toK ≫ φ.kernelMap = φ.complex.τ₁ ≫ S.toK := by
  apply (cancel_mono (kernel.ι S.complex.g)).mp
  simp only [Category.assoc, kernelMap_ι, toK_ι, toK_ι_assoc]
  exact φ.complex.comm₁₂.symm

/-- The induced commuting map of the first actual short exact sequences. -/
def firstMap : R.first ⟶ S.first where
  τ₁ := φ.augmentation
  τ₂ := φ.complex.τ₁
  τ₃ := φ.kernelMap
  comm₁₂ := φ.comm
  comm₂₃ := φ.toK_kernelMap.symm

/-- The induced commuting map of the second actual short exact sequences. -/
def secondMap : R.second ⟶ S.second where
  τ₁ := φ.kernelMap
  τ₂ := φ.complex.τ₂
  τ₃ := φ.complex.τ₃
  comm₁₂ := φ.kernelMap_ι
  comm₂₃ := φ.complex.comm₂₃

variable [HasExt.{w} C] (P : C)

/-- The actual map on the degree-zero Ext complexes. -/
def extZeroMap : R.extZeroComplex P ⟶ S.extZeroComplex P :=
  (extFunctorObj P 0).mapShortComplex.map φ.complex

/-- Naturality of the first genuine connecting map. -/
@[reassoc] theorem connectingOne_naturality :
    (extFunctorObj P 0).map φ.kernelMap ≫
        AddCommGrpCat.ofHom (connecting P S.first_shortExact 0) =
      AddCommGrpCat.ofHom (connecting P R.first_shortExact 0) ≫
        (extFunctorObj P 1).map φ.augmentation := by
  ext x
  exact connecting_naturality P R.first_shortExact S.first_shortExact φ.firstMap 0 x

/-- Naturality of the genuine composite connecting map into degree two. -/
@[reassoc] theorem connectingTwo_naturality :
    (extFunctorObj P 0).map φ.complex.τ₃ ≫ AddCommGrpCat.ofHom (S.connectingTwo P) =
      AddCommGrpCat.ofHom (R.connectingTwo P) ≫
        (extFunctorObj P 2).map φ.augmentation := by
  ext x
  change connecting P S.first_shortExact 1
      (connecting P S.second_shortExact 0
        ((extFunctorObj P 0).map φ.complex.τ₃ x)) =
    (extFunctorObj P 2).map φ.augmentation
      (connecting P R.first_shortExact 1 (connecting P R.second_shortExact 0 x))
  have h₂ := connecting_naturality P R.second_shortExact S.second_shortExact φ.secondMap 0 x
  have h₁ := connecting_naturality P R.first_shortExact S.first_shortExact φ.firstMap 1
    (connecting P R.second_shortExact 0 x)
  exact (congrArg (connecting P S.first_shortExact 1) h₂).trans h₁

/-- Kernel sections give the same actual cycles after applying a map
of augmented resolutions. -/
@[reassoc] theorem extCycleMap_naturality :
    (extFunctorObj P 0).map φ.kernelMap ≫ S.extCycleMap P =
      R.extCycleMap P ≫ ShortComplex.cyclesMap (φ.extZeroMap P) := by
  apply (cancel_mono (S.extZeroComplex P).iCycles).mp
  change ((extFunctorObj P 0).map φ.kernelMap ≫ S.extCycleMap P) ≫
      (S.extZeroComplex P).iCycles =
    (R.extCycleMap P ≫ ShortComplex.cyclesMap (φ.extZeroMap P)) ≫
      (S.extZeroComplex P).iCycles
  have hmap : (extFunctorObj P 0).map φ.kernelMap ≫
        (extFunctorObj P 0).map (kernel.ι S.complex.g) =
      (extFunctorObj P 0).map (kernel.ι R.complex.g) ≫
        (extFunctorObj P 0).map φ.complex.τ₂ := by
    rw [← Functor.map_comp, ← Functor.map_comp, φ.kernelMap_ι]
  have hleft : ((extFunctorObj P 0).map φ.kernelMap ≫ S.extCycleMap P) ≫
        (S.extZeroComplex P).iCycles =
      (extFunctorObj P 0).map φ.kernelMap ≫
        (extFunctorObj P 0).map (kernel.ι S.complex.g) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => (extFunctorObj P 0).map φ.kernelMap ≫ k) (S.extCycleMap_i P))
  have hright : (R.extCycleMap P ≫ ShortComplex.cyclesMap (φ.extZeroMap P)) ≫
        (S.extZeroComplex P).iCycles =
      (extFunctorObj P 0).map (kernel.ι R.complex.g) ≫
        (extFunctorObj P 0).map φ.complex.τ₂ := by
    simp only [Category.assoc, ShortComplex.cyclesMap_i, extCycleMap_i_assoc]
    rfl
  exact hleft.trans (hmap.trans hright.symm)

end Hom

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
