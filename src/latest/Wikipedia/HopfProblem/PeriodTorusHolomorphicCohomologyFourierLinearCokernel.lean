import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The actual top Fourier cokernel and probability Haar mean

The constructed smooth top primitive proves exactness of the genuine
top differential followed by Haar mean. The mean is a categorical
cokernel map because constants give a right inverse. Uniqueness of
cokernels identifies Mathlib's original cokernel with the scalar module,
and its inverse sends each scalar to the actual constant-function class.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits MeasureTheory UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

open PeriodTorusLineBundleClassification

/-- The actual top differential is annihilated by the actual probability Haar mean. -/
theorem top_mean_comp (p : PeriodDomain) :
    (complex p).g ≫ ModuleCat.ofHom (meanLinear (d := Fin 4)) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact mean_top p a

/-- The top differential and mean, as a short complex of the original smooth modules. -/
def topMeanComplex (p : PeriodDomain) : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.mk (complex p).g (ModuleCat.ofHom (meanLinear (d := Fin 4)))
    (top_mean_comp p)

/-- Actual smooth top primitives identify the image with the mean-zero kernel. -/
theorem topMeanExact (p : PeriodDomain) : (topMeanComplex p).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro h hh
  obtain ⟨a, ha⟩ := (FourierTop.exists_top_primitive_iff p h).mpr hh
  exact ⟨a, ha⟩

theorem topMean_range_eq_ker (p : PeriodDomain) :
    LinearMap.range (top p) = LinearMap.ker (meanLinear (d := Fin 4)) :=
  (topMeanExact p).moduleCat_range_eq_ker

/-- Literal constants make probability Haar mean surjective. -/
theorem meanLinear_surjective : Function.Surjective (meanLinear (d := Fin 4)) :=
  fun c => ⟨constantLinear c, mean_constant c⟩

instance mean_epi : Epi (ModuleCat.ofHom (meanLinear (d := Fin 4))) :=
  ConcreteCategory.epi_of_surjective _ meanLinear_surjective

/-- The existing categorical cokernel is the scalar module, by its universal property. -/
def cokernelIso (p : PeriodDomain) : cokernel (complex p).g ≅ ModuleCat.of ℂ ℂ := by
  letI : Epi (topMeanComplex p).g := mean_epi
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (complex p).g) (topMeanExact p).gIsCokernel

/-- The canonical cokernel projection becomes the original complex-linear Haar mean. -/
theorem cokernelIso_π (p : PeriodDomain) :
    cokernel.π (complex p).g ≫ (cokernelIso p).hom =
      ModuleCat.ofHom (meanLinear (d := Fin 4)) := by
  have : Epi (topMeanComplex p).g := mean_epi
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (complex p).g) (topMeanExact p).gIsCokernel WalkingParallelPair.one

@[simp] theorem cokernelIso_π_apply (p : PeriodDomain) (h : Smooth) :
    (cokernelIso p).hom (cokernel.π (complex p).g h) = meanLinear h :=
  congrArg (fun f : ModuleCat.of ℂ Smooth ⟶ ModuleCat.of ℂ ℂ => f h) (cokernelIso_π p)

/-- The coordinate of a class is literally its probability Haar integral. -/
theorem cokernelIso_π_haarMean (p : PeriodDomain) (h : Smooth) :
    (cokernelIso p).hom (cokernel.π (complex p).g h) =
      ∫ t : UnitAddTorus (Fin 4), h t
        ∂Measure.pi (fun _ : Fin 4 => AddCircle.haarAddCircle) :=
  (cokernelIso_π_apply p h).trans (torusFourierMean_eq_haarIntegral h)

/-- The inverse is the categorical class of the literal constant smooth function. -/
theorem cokernelIso_inv (p : PeriodDomain) :
    (cokernelIso p).inv =
      ModuleCat.ofHom (constantLinear (d := Fin 4)) ≫ cokernel.π (complex p).g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply (ModuleCat.mono_iff_injective (cokernelIso p).hom).mp inferInstance
  exact (congrArg (fun f : ModuleCat.of ℂ ℂ ⟶ ModuleCat.of ℂ ℂ => f c)
    (Iso.inv_hom_id (cokernelIso p))).trans
      ((mean_constant c).symm.trans (cokernelIso_π_apply p (constantLinear c)).symm)

@[simp] theorem cokernelIso_inv_apply (p : PeriodDomain) (c : ℂ) :
    (cokernelIso p).inv c = cokernel.π (complex p).g (constantLinear c) :=
  congrArg (fun f : ModuleCat.of ℂ ℂ ⟶ cokernel (complex p).g => f c) (cokernelIso_inv p)

/-- Every original smooth coefficient has the same actual cokernel class as its Haar mean. -/
theorem cokernel_class_eq_constant (p : PeriodDomain) (h : Smooth) :
    cokernel.π (complex p).g h =
      cokernel.π (complex p).g (constantLinear (meanLinear h)) := by
  apply (ModuleCat.mono_iff_injective (cokernelIso p).hom).mp inferInstance
  rw [cokernelIso_π_apply, cokernelIso_π_apply, mean_constant]

theorem cokernel_finrank (p : PeriodDomain) :
    Module.finrank ℂ ↥(cokernel (complex p).g) = 1 :=
  (cokernelIso p).toLinearEquiv.finrank_eq.trans (Module.finrank_self ℂ)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear
