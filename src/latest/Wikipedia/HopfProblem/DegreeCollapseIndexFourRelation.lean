import Wikipedia.SmoothSixDPoincare.MorseIndexThreePresentation

/-!
# The actual integral relation contributed by a native index-four handle

Its original parametrized attaching three-sphere supplies the integral
class in the lower sublevel. The native exact sequence identifies upper
third homology with the quotient by precisely this class. Adjoining its
actual column retains the preceding presentation map and all old columns.
This supplies the algebraic step for relative three/four cancellation.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.IndexFour

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology Wikipedia.HopfProblem.SphereHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

def indexFourBoundaryEquiv (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4) :
    SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 3 ≃ₗ[ℤ] ℤ := by
  let : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 3 + 1) := ⟨hindex⟩
  let H := homeomorphHomologyEquiv
    (SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 3).toHomeomorph 3
  exact H.symm.trans (unitSphereHomologyTopEquiv 2)

theorem indexFourBoundary_scalar
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4)
    (a : SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 3) :
    a = (indexFourBoundaryEquiv d hindex a) • (indexFourBoundaryEquiv d hindex).symm 1 := by
  apply (indexFourBoundaryEquiv d hindex).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply, zsmul_eq_mul, mul_one]
  simp

def indexFourAttachingClass (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4) :
    SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3 :=
  d.coreBoundaryHomologyMap 3 ((indexFourBoundaryEquiv d hindex).symm 1)

theorem coreBoundary_three_eq_smul
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4)
    (a : SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 3) :
    d.coreBoundaryHomologyMap 3 a =
      (indexFourBoundaryEquiv d hindex a) • indexFourAttachingClass d hindex := by
  conv_lhs => rw [indexFourBoundary_scalar d hindex a]
  rw [map_zsmul]
  rfl

theorem coreBoundary_three_range
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4) :
    LinearMap.range (d.coreBoundaryHomologyMap 3) =
      Submodule.span ℤ {indexFourAttachingClass d hindex} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    rw [coreBoundary_three_eq_smul d hindex b]
    exact Submodule.mem_span_singleton.mpr
      ⟨indexFourBoundaryEquiv d hindex b,
        int_smul_eq_zsmul
          (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3).isModule _ _⟩
  · intro ha
    obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp ha
    refine ⟨z • (indexFourBoundaryEquiv d hindex).symm 1, ?_⟩
    rw [map_zsmul]
    exact (int_smul_eq_zsmul
      (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3).isModule z
        (indexFourAttachingClass d hindex)).symm.trans hz

variable [T2Space M]

theorem indexFour_lowerRealization_surjective (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4) :
    Surjective (d.lowerRealizationHomologyMap 3) := by
  let : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 2) :=
    d.attachingHomology_subsingleton_of_index 2 (by decide) (by omega) (by omega)
  intro a
  have ha : a ∈ LinearMap.ker (d.morseConnectingMap hf 2) := Subsingleton.elim _ _
  rw [← d.morse_exact_at_upper hf 2] at ha
  exact ha

theorem indexFour_lowerRealization_kernel (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4) :
    LinearMap.ker (d.lowerRealizationHomologyMap 3) =
      Submodule.span ℤ {indexFourAttachingClass d hindex} := by
  rw [← d.morse_exact_at_lower hf 3 (by norm_num), coreBoundary_three_range d hindex]

def indexFourHomologyQuotient (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4) :
    (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3 ⧸
      Submodule.span ℤ {indexFourAttachingClass d hindex}) ≃ₗ[ℤ]
        SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 3 :=
  (HomologyTransport.quotientAddEquivOfKernel (d.lowerRealizationHomologyMap 3)
    (Submodule.span ℤ {indexFourAttachingClass d hindex})
    (indexFour_lowerRealization_kernel d hf hindex)
    (indexFour_lowerRealization_surjective d hf hindex)).toIntLinearEquiv

theorem indexFourHomologyQuotient_apply (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4)
    (a : SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3) :
    indexFourHomologyQuotient d hf hindex (Submodule.Quotient.mk a) =
      d.lowerRealizationHomologyMap 3 a := rfl

variable (hf : Continuous f)
  (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4)
  {r c : ℕ}
  (P : IntegerPresentation (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 3) r c)

def indexFourPresentation :
    IntegerPresentation (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 3) r (c + 1) :=
  P.adjoin (d.lowerRealizationHomologyMap 3) (indexFour_lowerRealization_surjective d hf hindex)
    (indexFourAttachingClass d hindex) (indexFour_lowerRealization_kernel d hf hindex)

theorem indexFourPresentation_map (v : Fin r → ℤ) :
    (indexFourPresentation d hf hindex P).map v =
      d.lowerRealizationHomologyMap 3 (P.map v) := rfl

theorem indexFourPresentation_column_zero :
    P.map ((indexFourPresentation d hf hindex P).columns 0) =
      indexFourAttachingClass d hindex :=
  P.adjoin_column_zero _ _ _ _

theorem indexFourPresentation_column_succ (i : Fin c) :
    (indexFourPresentation d hf hindex P).columns i.succ = P.columns i := rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.IndexFour
