import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImagePeriodGerms
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# A genuine nonzero kernel element of raw stalk-to-fibre evaluation

On an original open complex base, the first marked character multiplied
by the vanishing base coordinate has a nonzero higher-direct-image stalk
germ, but its actual fibre evaluation is zero. Thus the raw stalk map
is not injective. The expected base-change isomorphism must specialize
the original base-function module to its residue field; it cannot be an
isomorphism of these raw additive groups.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Filter
open scoped ContDiff Manifold Topology Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreKernel

open PeriodFamilyHolomorphicCohomology

variable (U : Opens ℂ)

/-- The original holomorphic base coordinate vanishing at the chosen point. -/
def vanishingBaseCoordinate (b : U) :
    ContMDiffMap 𝓘(ℂ) 𝓘(ℂ) U ℂ ω :=
  ⟨fun x => (x : ℂ) - (b : ℂ), contMDiff_subtype_val.sub contMDiff_const⟩

@[simp] theorem vanishingBaseCoordinate_apply (b x : U) :
    vanishingBaseCoordinate U b x = (x : ℂ) - (b : ℂ) := rfl

/-- Multiply the first original marked character by that genuine vanishing function. -/
def vanishingPeriodCoefficients (b : U) : Cocycle.Coefficients ℂ U :=
  ![vanishingBaseCoordinate U b, 0, 0, 0]

theorem vanishingPeriodCoefficients_values (b x : U) :
    (fun j => vanishingPeriodCoefficients U b j x) =
      MarkedLinear.firstCoefficients ![(x : ℂ) - (b : ℂ), 0] := by
  funext j
  fin_cases j <;> rfl

theorem vanishingPeriodCoefficients_values_self (b : U) :
    (fun j => vanishingPeriodCoefficients U b j b) = 0 := by
  funext j
  fin_cases j <;> simp [vanishingPeriodCoefficients]

/-- The original coordinate on an open complex base is not locally constant
at any of its points, proved in the actual subspace topology. -/
theorem not_eventually_coordinate_eq (b : U) :
    ¬ ∀ᶠ (x : U) in 𝓝 b, (x : ℂ) = (b : ℂ) := by
  intro h
  obtain ⟨W, hW, hWopen, hbW⟩ := mem_nhds_iff.mp h
  have hopen : IsOpen ((Subtype.val : U → ℂ) '' W) :=
    U.isOpen.isOpenMap_subtype_val W hWopen
  have hb : (b : ℂ) ∈ (Subtype.val : U → ℂ) '' W := ⟨b, hbW, rfl⟩
  obtain ⟨z, hz, hzb⟩ := preperfect_iff_nhds.mp hopen.preperfect
    (b : ℂ) hb univ Filter.univ_mem
  obtain ⟨x, hxW, hxz⟩ := hz.2
  exact hzb (hxz.symm.trans (hW hxW))

/-- The actual period reduction of the variable character is the
literal vanishing base coordinate in its first component. -/
theorem reduction_vanishingPeriodCoefficients (P : HolomorphicPeriodMap ℂ U) (b x : U) :
    MarkedLinear.reduction (P.point x) (fun j => vanishingPeriodCoefficients U b j x) =
      ![(x : ℂ) - (b : ℂ), 0] := by
  rw [vanishingPeriodCoefficients_values, MarkedLinear.reduction_firstCoefficients]

/-- This variable character is a genuinely nonzero germ of the original
native first higher direct image, despite vanishing on the chosen fibre. -/
theorem vanishingPeriodGerm_ne_zero (P : HolomorphicPeriodMap ℂ U) (b : U) :
    periodStalkClass P b (vanishingPeriodCoefficients U b) ≠ 0 := by
  apply periodStalkClass_ne_zero_of_reduction P b (vanishingPeriodCoefficients U b)
  intro h
  apply not_eventually_coordinate_eq U b
  filter_upwards [h] with x hx
  have h0 := congrArg (fun c : Fin 2 → ℂ => c 0) hx
  rw [reduction_vanishingPeriodCoefficients] at h0
  exact sub_eq_zero.mp h0

/-- Its evaluation is zero in the actual original fibre cohomology group. -/
theorem fibreEvaluation_vanishingPeriodGerm (P : HolomorphicPeriodMap ℂ U) (b : U) :
    fibreEvaluation P b 1 (periodStalkClass P b (vanishingPeriodCoefficients U b)) = 0 := by
  have hc : -MarkedLinear.dbarLinear (P.point b)
      (fun j => vanishingPeriodCoefficients U b j b) = 0 := by
    rw [vanishingPeriodCoefficients_values_self, map_zero, neg_zero]
  apply (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b)).injective
  exact ((oneFibreCoordinates_periodStalkClass P b
    (vanishingPeriodCoefficients U b)).trans hc).trans
    (map_zero (PeriodTorusHolomorphicCohomology.h1Equiv (P.point b))).symm

/-- The genuine raw stalk evaluation is not injective on an open complex base.
This records why residue-field specialization is essential in base change. -/
theorem fibreEvaluation_one_not_injective (P : HolomorphicPeriodMap ℂ U) (b : U) :
    ¬ Function.Injective (fibreEvaluation P b 1) := by
  intro h
  apply vanishingPeriodGerm_ne_zero U P b
  exact h ((fibreEvaluation_vanishingPeriodGerm U P b).trans
    (map_zero (fibreEvaluation P b 1).hom).symm)

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.FibreKernel
