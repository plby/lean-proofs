import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

/-!
# The normalized cokernel-to-kernel extension

An exact segment whose two outer maps are the three-overlap maps induces
an actual short exact sequence from the cokernel of the higher monodromy
difference map to the kernel of the lower monodromy difference map. The
middle module and the original incoming and outgoing maps are unchanged.

The incoming map sends the class of `y` to `j (0, -y)`. The outgoing map
keeps the last two coordinates of the original connecting map. No
freeness, splitting, or geometric identification is assumed.
-/

noncomputable section

universe u

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

open CategoryTheory PeriodTorusHigherHomology

variable {High Low Middle : Type u}
  [AddCommGroup High] [AddCommGroup Low] [AddCommGroup Middle]
  [Module ℤ High] [Module ℤ Low] [Module ℤ Middle]

/-- The original incoming map on the normalized higher cokernel. -/
def reducedCokernelToMiddle (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j) :
    (High ⧸ LinearMap.range (delta P Q)) →ₗ[ℤ] Middle :=
  intLinearMapOfAddHom
    ((cokernelToMiddle (overlapMap P Q) j hj).toAddMonoidHom.comp
      (overlapCokernelEquiv P Q).symm.toAddEquiv.toAddMonoidHom)

@[simp] theorem reducedCokernelToMiddle_apply
    (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j)
    (q : High ⧸ LinearMap.range (delta P Q)) :
    reducedCokernelToMiddle P Q j hj q =
      cokernelToMiddle (overlapMap P Q) j hj ((overlapCokernelEquiv P Q).symm q) := rfl

/-- On an actual quotient representative, the normalized incoming map is
the original map evaluated at `(0, -y)`. -/
@[simp] theorem reducedCokernelToMiddle_mk
    (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j) (y : High) :
    reducedCokernelToMiddle P Q j hj (Submodule.Quotient.mk y) = j (0, -y) := by
  rw [reducedCokernelToMiddle_apply, overlapCokernelEquiv_symm_mk]
  rfl

/-- The normalized incoming map is injective. -/
theorem reducedCokernelToMiddle_injective
    (P Q : High →ₗ[ℤ] High) (j : (High × High) →ₗ[ℤ] Middle)
    (hj : Function.Exact (overlapMap P Q) j) :
    Function.Injective (reducedCokernelToMiddle P Q j hj) :=
  (cokernelToMiddle_injective (overlapMap P Q) j hj).comp
    (overlapCokernelEquiv P Q).symm.injective

/-- The original outgoing map with codomain identified with the normalized
lower kernel. -/
def middleToReducedKernel (P Q : Low →ₗ[ℤ] Low)
    (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hδ : Function.Exact δ (overlapMap P Q)) :
    Middle →ₗ[ℤ] LinearMap.ker (delta P Q) :=
  intLinearMapOfAddHom
    ((overlapKerEquiv P Q).toAddEquiv.toAddMonoidHom.comp
      (middleToKernel δ (overlapMap P Q) hδ).toAddMonoidHom)

@[simp] theorem middleToReducedKernel_apply
    (P Q : Low →ₗ[ℤ] Low) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hδ : Function.Exact δ (overlapMap P Q)) (m : Middle) :
    middleToReducedKernel P Q δ hδ m =
      overlapKerEquiv P Q (middleToKernel δ (overlapMap P Q) hδ m) := rfl

/-- The underlying pair is precisely the final two coordinates of the
original outgoing map. -/
@[simp] theorem middleToReducedKernel_val
    (P Q : Low →ₗ[ℤ] Low) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hδ : Function.Exact δ (overlapMap P Q)) (m : Middle) :
    (middleToReducedKernel P Q δ hδ m : Low × Low) = (δ m).2 := rfl

/-- The normalized outgoing map is surjective. -/
theorem middleToReducedKernel_surjective
    (P Q : Low →ₗ[ℤ] Low) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hδ : Function.Exact δ (overlapMap P Q)) :
    Function.Surjective (middleToReducedKernel P Q δ hδ) :=
  (overlapKerEquiv P Q).surjective.comp
    (middleToKernel_surjective δ (overlapMap P Q) hδ)

/-- The genuine exact middle segment survives both explicit normalizations. -/
theorem reducedExtension_exact
    (PHigh QHigh : High →ₗ[ℤ] High) (PLow QLow : Low →ₗ[ℤ] Low)
    (j : (High × High) →ₗ[ℤ] Middle) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hj : Function.Exact (overlapMap PHigh QHigh) j) (hjδ : Function.Exact j δ)
    (hδ : Function.Exact δ (overlapMap PLow QLow)) :
    Function.Exact (reducedCokernelToMiddle PHigh QHigh j hj)
      (middleToReducedKernel PLow QLow δ hδ) := by
  have hex := cokernelToMiddle_middleToKernel_exact
    (overlapMap PHigh QHigh) j δ (overlapMap PLow QLow) hj hjδ hδ
  intro m
  constructor
  · intro hm
    have hzero : middleToKernel δ (overlapMap PLow QLow) hδ m = 0 := by
      apply (overlapKerEquiv PLow QLow).injective
      exact hm.trans (overlapKerEquiv PLow QLow).map_zero.symm
    obtain ⟨q, hq⟩ := (hex m).mp hzero
    refine ⟨overlapCokernelEquiv PHigh QHigh q, ?_⟩
    rw [reducedCokernelToMiddle_apply, LinearEquiv.symm_apply_apply]
    exact hq
  · rintro ⟨q, rfl⟩
    have hzero : middleToKernel δ (overlapMap PLow QLow) hδ
        (reducedCokernelToMiddle PHigh QHigh j hj q) = 0 :=
      (hex _).mpr ⟨(overlapCokernelEquiv PHigh QHigh).symm q, rfl⟩
    rw [middleToReducedKernel_apply, hzero, map_zero]

/-- The normalized incoming and outgoing linear maps compose to zero. -/
theorem reducedExtension_comp_eq_zero
    (PHigh QHigh : High →ₗ[ℤ] High) (PLow QLow : Low →ₗ[ℤ] Low)
    (j : (High × High) →ₗ[ℤ] Middle) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hj : Function.Exact (overlapMap PHigh QHigh) j) (hjδ : Function.Exact j δ)
    (hδ : Function.Exact δ (overlapMap PLow QLow)) :
    (middleToReducedKernel PLow QLow δ hδ).comp
      (reducedCokernelToMiddle PHigh QHigh j hj) = 0 :=
  (reducedExtension_exact PHigh QHigh PLow QLow j δ hj hjδ hδ).linearMap_comp_eq_zero

/-- The normalized extension as a literal short complex of integral modules. -/
def reducedExtension
    (PHigh QHigh : High →ₗ[ℤ] High) (PLow QLow : Low →ₗ[ℤ] Low)
    (j : (High × High) →ₗ[ℤ] Middle) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hj : Function.Exact (overlapMap PHigh QHigh) j) (hjδ : Function.Exact j δ)
    (hδ : Function.Exact δ (overlapMap PLow QLow)) :
    ShortComplex (ModuleCat.{u} ℤ) :=
  ShortComplex.moduleCatMk (reducedCokernelToMiddle PHigh QHigh j hj)
    (middleToReducedKernel PLow QLow δ hδ)
    (reducedExtension_comp_eq_zero PHigh QHigh PLow QLow j δ hj hjδ hδ)

/-- Every exact segment with the three-overlap outer maps gives an actual
short exact extension of the normalized kernel by the normalized cokernel. -/
theorem reducedExtension_shortExact
    (PHigh QHigh : High →ₗ[ℤ] High) (PLow QLow : Low →ₗ[ℤ] Low)
    (j : (High × High) →ₗ[ℤ] Middle) (δ : Middle →ₗ[ℤ] (Low × (Low × Low)))
    (hj : Function.Exact (overlapMap PHigh QHigh) j) (hjδ : Function.Exact j δ)
    (hδ : Function.Exact δ (overlapMap PLow QLow)) :
    (reducedExtension PHigh QHigh PLow QLow j δ hj hjδ hδ).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact reducedExtension_exact PHigh QHigh PLow QLow j δ hj hjδ hδ
  · exact reducedCokernelToMiddle_injective PHigh QHigh j hj
  · exact middleToReducedKernel_surjective PLow QLow δ hδ

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
