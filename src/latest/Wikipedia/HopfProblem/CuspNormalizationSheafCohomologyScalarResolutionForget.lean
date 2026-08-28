import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyGlobalSectionsForgetLinear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Scalar compatibility of the canonical forgetful homology comparisons

These generic lemmas relate actual scalar endomorphisms of a complex
to the canonical complex modules on its forgotten homological objects.
No dimension calculation is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution

open SheafCohomologyGlobalSections

abbrev linearForget : ModuleCat.{0} ℂ ⥤ AddCommGrpCat.{0} :=
  forget₂ (ModuleCat ℂ) AddCommGrpCat

variable (S : ShortComplex (ModuleCat.{0} ℂ))

/-- The actual forgotten scalar endomorphism of a complex of complex vector spaces. -/
def forgottenScalarMap (c : ℂ) : S.map linearForget ⟶ S.map linearForget :=
  linearForget.mapShortComplex.map (c • 𝟙 S)

/-- The map on the actual first kernel induced by that scalar endomorphism. -/
def forgottenKernelScalarMap (c : ℂ) :
    kernel (S.map linearForget).f ⟶ kernel (S.map linearForget).f :=
  kernel.map _ _ (forgottenScalarMap S c).τ₁ (forgottenScalarMap S c).τ₂
    (forgottenScalarMap S c).comm₁₂.symm

/-- The canonical forgetful comparison for the actual first kernel. -/
def kernelForgetAddEquiv : ↥(kernel (S.map linearForget).f) ≃+ ↥(kernel S.f) :=
  moduleForgetAddEquiv (PreservesKernel.iso linearForget S.f).symm

theorem kernelForgetAddEquiv_ι (x : ↥(kernel (S.map linearForget).f)) :
    (kernel.ι S.f) (kernelForgetAddEquiv S x) =
      (kernel.ι (S.map linearForget).f x : S.X₁) :=
  ConcreteCategory.congr_hom (PreservesKernel.iso_inv_ι linearForget S.f) x

/-- The kernel comparison identifies the induced scalar map with the original module scalar. -/
theorem kernelForget_scalar (c : ℂ) (x : ↥(kernel (S.map linearForget).f)) :
    kernelForgetAddEquiv S (forgottenKernelScalarMap S c x) =
      c • kernelForgetAddEquiv S x := by
  apply (ModuleCat.mono_iff_injective (kernel.ι S.f)).mp inferInstance
  have hc : (kernel.ι (S.map linearForget).f (forgottenKernelScalarMap S c x) : S.X₁) =
      SMul.smul (M := ℂ) (α := S.X₁) c (kernel.ι (S.map linearForget).f x) :=
    ConcreteCategory.congr_hom
      (kernel.lift_ι (S.map linearForget).f
        (kernel.ι (S.map linearForget).f ≫ (forgottenScalarMap S c).τ₁) _) x
  exact Eq.trans (kernelForgetAddEquiv_ι S (forgottenKernelScalarMap S c x))
    (Eq.trans hc (Eq.trans
      (congrArg (fun y : S.X₁ => c • y) (kernelForgetAddEquiv_ι S x).symm)
      ((kernel.ι S.f).hom.map_smul c (kernelForgetAddEquiv S x)).symm))

/-- The canonical forgetful comparison for actual middle homology. -/
def homologyForgetAddEquiv : (S.map linearForget).homology ≃+ S.homology :=
  moduleForgetAddEquiv (S.mapHomologyIso linearForget)

/-- Actual homology functoriality identifies the scalar endomorphism with the module action. -/
theorem homologyForget_scalar (c : ℂ) (x : (S.map linearForget).homology) :
    homologyForgetAddEquiv S (ShortComplex.homologyMap (forgottenScalarMap S c) x) =
      c • homologyForgetAddEquiv S x := by
  have h := ConcreteCategory.congr_hom
    (ShortComplex.mapHomologyIso_hom_naturality (c • 𝟙 S) linearForget) x
  simp only [ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id] at h
  exact h

/-- The map on the actual final cokernel induced by the scalar endomorphism. -/
def forgottenCokernelScalarMap (c : ℂ) :
    cokernel (S.map linearForget).g ⟶ cokernel (S.map linearForget).g :=
  cokernel.map _ _ (forgottenScalarMap S c).τ₂ (forgottenScalarMap S c).τ₃
    (forgottenScalarMap S c).comm₂₃.symm

/-- The canonical forgetful comparison for the actual final cokernel. -/
def cokernelForgetAddEquiv : ↥(cokernel (S.map linearForget).g) ≃+ ↥(cokernel S.g) :=
  moduleForgetAddEquiv (PreservesCokernel.iso linearForget S.g).symm

theorem cokernelForgetAddEquiv_π (s : S.X₃) :
    cokernelForgetAddEquiv S (cokernel.π (S.map linearForget).g s) = cokernel.π S.g s := by
  have h : cokernel.π (linearForget.map S.g) ≫ (PreservesCokernel.iso linearForget S.g).inv =
      linearForget.map (cokernel.π S.g) := by
    rw [PreservesCokernel.iso_inv]
    exact π_comp_cokernelComparison S.g linearForget
  exact ConcreteCategory.congr_hom h s

/-- The cokernel comparison identifies the induced scalar map with the original module scalar. -/
theorem cokernelForget_scalar (c : ℂ) (x : ↥(cokernel (S.map linearForget).g)) :
    cokernelForgetAddEquiv S (forgottenCokernelScalarMap S c x) =
      c • cokernelForgetAddEquiv S x := by
  obtain ⟨s, rfl⟩ := (AddCommGrpCat.epi_iff_surjective
    (cokernel.π (S.map linearForget).g)).mp inferInstance x
  have hc : forgottenCokernelScalarMap S c (cokernel.π (S.map linearForget).g s) =
      cokernel.π (S.map linearForget).g (SMul.smul (M := ℂ) (α := S.X₃) c s) :=
    ConcreteCategory.congr_hom
      (cokernel.π_desc (S.map linearForget).g
        ((forgottenScalarMap S c).τ₃ ≫ cokernel.π (S.map linearForget).g) _) s
  exact Eq.trans (congrArg (cokernelForgetAddEquiv S) hc)
    (Eq.trans (cokernelForgetAddEquiv_π S (SMul.smul (M := ℂ) (α := S.X₃) c s))
      (Eq.trans ((cokernel.π S.g).hom.map_smul c s)
        (congrArg (fun y : ↥(cokernel S.g) => c • y) (cokernelForgetAddEquiv_π S s).symm)))

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyScalarResolution
