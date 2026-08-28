import Wikipedia.SmoothSixDPoincare.MorseHomologyPropagation
import Wikipedia.HopfProblem.SphereHomologyTop
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The actual relation contributed by an index-three handle

The original parametrized attaching two-sphere supplies one integral class
in the lower sublevel. The native exact sequence proves that the upper
second homology is the quotient by precisely the span of this class.
Both the relation and the quotient map are the original geometric maps.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.HomologyTransport

def quotientAddEquivOfKernel {R A B : Type*} [CommRing R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (f : A →ₗ[R] B) (P : Submodule R A) (hP : LinearMap.ker f = P)
    (hf : Surjective f) : (A ⧸ P) ≃+ B :=
  ((Submodule.quotEquivOfEq _ _ hP.symm).trans (f.quotKerEquivOfSurjective hf)).toAddEquiv

end Wikipedia.SmoothSixDPoincare.HomologyTransport

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology Wikipedia.HopfProblem.SphereHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

def indexThreeBoundaryEquiv (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 2 ≃ₗ[ℤ] ℤ := by
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1) := ⟨hindex⟩
  let H := homeomorphHomologyEquiv
    (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph 2
  exact H.symm.trans (unitSphereHomologyTopEquiv 1)

theorem indexThreeBoundary_scalar
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a : SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 2) :
    a = (d.indexThreeBoundaryEquiv hindex a) • (d.indexThreeBoundaryEquiv hindex).symm 1 := by
  apply (d.indexThreeBoundaryEquiv hindex).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply, zsmul_eq_mul, mul_one]
  simp

def indexThreeAttachingClass (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2 :=
  d.coreBoundaryHomologyMap 2 ((d.indexThreeBoundaryEquiv hindex).symm 1)

theorem coreBoundary_two_eq_smul
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a : SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 2) :
    d.coreBoundaryHomologyMap 2 a =
      (d.indexThreeBoundaryEquiv hindex a) • d.indexThreeAttachingClass hindex := by
  conv_lhs => rw [d.indexThreeBoundary_scalar hindex a]
  rw [map_zsmul]
  rfl

theorem coreBoundary_two_range
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.range (d.coreBoundaryHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [d.coreBoundary_two_eq_smul hindex b]
    exact Submodule.mem_span_singleton.mpr
      ⟨d.indexThreeBoundaryEquiv hindex b,
        int_smul_eq_zsmul
          (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2).isModule _ _⟩
  · intro ha
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨z • (d.indexThreeBoundaryEquiv hindex).symm 1, ?_⟩
    rw [map_zsmul]
    exact (int_smul_eq_zsmul
      (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2).isModule z
        (d.indexThreeAttachingClass hindex)).symm.trans hz

variable [T2Space M]

theorem indexThree_lowerRealization_surjective (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    Surjective (d.lowerRealizationHomologyMap 2) := by
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 1) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_upper hf 1] at ha
  exact ha

theorem indexThree_lowerRealization_kernel (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    LinearMap.ker (d.lowerRealizationHomologyMap 2) =
      Submodule.span ℤ {d.indexThreeAttachingClass hindex} := by
  rw [← d.morse_exact_at_lower hf 2 (by norm_num), d.coreBoundary_two_range hindex]

def indexThreeHomologyQuotient (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) :
    (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2 ⧸
      Submodule.span ℤ {d.indexThreeAttachingClass hindex}) ≃ₗ[ℤ]
        SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 2 :=
  (HomologyTransport.quotientAddEquivOfKernel (d.lowerRealizationHomologyMap 2)
    (Submodule.span ℤ {d.indexThreeAttachingClass hindex})
    (d.indexThree_lowerRealization_kernel hf hindex)
    (d.indexThree_lowerRealization_surjective hf hindex)).toIntLinearEquiv

theorem indexThreeHomologyQuotient_apply (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    (a : SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2) :
    d.indexThreeHomologyQuotient hf hindex (Submodule.Quotient.mk a) =
      d.lowerRealizationHomologyMap 2 a := rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
